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
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value;
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
lean_object* v_ref_299_; lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_345_; 
v_ref_299_ = lean_ctor_get(v___y_296_, 2);
v___x_300_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msg_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_345_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_345_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_345_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v_traceState_306_; lean_object* v_env_307_; lean_object* v_nextMacroScope_308_; lean_object* v_ngen_309_; lean_object* v_auxDeclNGen_310_; lean_object* v_cache_311_; lean_object* v_messages_312_; lean_object* v_infoState_313_; lean_object* v_snapshotTasks_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_344_; 
v___x_305_ = lean_st_ref_take(v___y_297_);
v_traceState_306_ = lean_ctor_get(v___x_305_, 4);
v_env_307_ = lean_ctor_get(v___x_305_, 0);
v_nextMacroScope_308_ = lean_ctor_get(v___x_305_, 1);
v_ngen_309_ = lean_ctor_get(v___x_305_, 2);
v_auxDeclNGen_310_ = lean_ctor_get(v___x_305_, 3);
v_cache_311_ = lean_ctor_get(v___x_305_, 5);
v_messages_312_ = lean_ctor_get(v___x_305_, 6);
v_infoState_313_ = lean_ctor_get(v___x_305_, 7);
v_snapshotTasks_314_ = lean_ctor_get(v___x_305_, 8);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_344_ == 0)
{
v___x_316_ = v___x_305_;
v_isShared_317_ = v_isSharedCheck_344_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snapshotTasks_314_);
lean_inc(v_infoState_313_);
lean_inc(v_messages_312_);
lean_inc(v_cache_311_);
lean_inc(v_traceState_306_);
lean_inc(v_auxDeclNGen_310_);
lean_inc(v_ngen_309_);
lean_inc(v_nextMacroScope_308_);
lean_inc(v_env_307_);
lean_dec(v___x_305_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_344_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
uint64_t v_tid_318_; lean_object* v_traces_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_343_; 
v_tid_318_ = lean_ctor_get_uint64(v_traceState_306_, sizeof(void*)*1);
v_traces_319_ = lean_ctor_get(v_traceState_306_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_traceState_306_);
if (v_isSharedCheck_343_ == 0)
{
v___x_321_ = v_traceState_306_;
v_isShared_322_ = v_isSharedCheck_343_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_traces_319_);
lean_dec(v_traceState_306_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_343_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; double v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_323_ = lean_box(0);
v___x_324_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0);
v___x_325_ = 0;
v___x_326_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1));
v___x_327_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_327_, 0, v_cls_292_);
lean_ctor_set(v___x_327_, 1, v___x_323_);
lean_ctor_set(v___x_327_, 2, v___x_326_);
lean_ctor_set_float(v___x_327_, sizeof(void*)*3, v___x_324_);
lean_ctor_set_float(v___x_327_, sizeof(void*)*3 + 8, v___x_324_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*3 + 16, v___x_325_);
v___x_328_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2));
v___x_329_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v_a_301_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
lean_inc(v_ref_299_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_ref_299_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_PersistentArray_push___redArg(v_traces_319_, v___x_330_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_331_);
v___x_333_ = v___x_321_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_331_);
lean_ctor_set_uint64(v_reuseFailAlloc_342_, sizeof(void*)*1, v_tid_318_);
v___x_333_ = v_reuseFailAlloc_342_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 4, v___x_333_);
v___x_335_ = v___x_316_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_env_307_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_nextMacroScope_308_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_ngen_309_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_auxDeclNGen_310_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_341_, 5, v_cache_311_);
lean_ctor_set(v_reuseFailAlloc_341_, 6, v_messages_312_);
lean_ctor_set(v_reuseFailAlloc_341_, 7, v_infoState_313_);
lean_ctor_set(v_reuseFailAlloc_341_, 8, v_snapshotTasks_314_);
v___x_335_ = v_reuseFailAlloc_341_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_st_ref_put(v___y_297_, v___x_335_);
v___x_337_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_337_);
v___x_339_ = v___x_303_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* v_cls_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_346_, v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_box(0);
v___x_360_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__1));
v___x_361_ = l_Lean_mkConst(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7(void){
_start:
{
lean_object* v_cls_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_cls_369_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_370_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_371_ = l_Lean_Name_append(v___x_370_, v_cls_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__8));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__10));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__12));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* v_e_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
if (lean_obj_tag(v_e_381_) == 7)
{
lean_object* v_binderName_393_; lean_object* v_binderType_394_; lean_object* v_body_395_; uint8_t v_binderInfo_396_; lean_object* v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v_toCold_422_; lean_object* v_inheritedTraceOptions_423_; lean_object* v_cls_424_; uint8_t v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___x_531_; lean_object* v_a_532_; uint8_t v___x_533_; 
v_binderName_393_ = lean_ctor_get(v_e_381_, 0);
v_binderType_394_ = lean_ctor_get(v_e_381_, 1);
v_body_395_ = lean_ctor_get(v_e_381_, 2);
v_binderInfo_396_ = lean_ctor_get_uint8(v_e_381_, sizeof(void*)*3 + 8);
v_toCold_422_ = lean_ctor_get(v_a_390_, 0);
v_inheritedTraceOptions_423_ = lean_ctor_get(v_toCold_422_, 11);
v_cls_424_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_531_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_424_, v_inheritedTraceOptions_423_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v___x_531_);
v___x_533_ = lean_unbox(v_a_532_);
lean_dec(v_a_532_);
if (v___x_533_ == 0)
{
v___y_489_ = v_a_382_;
v___y_490_ = v_a_383_;
v___y_491_ = v_a_384_;
v___y_492_ = v_a_385_;
v___y_493_ = v_a_386_;
v___y_494_ = v_a_387_;
v___y_495_ = v_a_388_;
v___y_496_ = v_a_389_;
v___y_497_ = v_a_390_;
v___y_498_ = v_a_391_;
goto v___jp_488_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Meta_Grind_updateLastTag(v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec_ref_known(v___x_534_, 1);
lean_inc_ref(v_e_381_);
v___x_535_ = l_Lean_MessageData_ofExpr(v_e_381_);
v___x_536_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_424_, v___x_535_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_dec_ref_known(v___x_536_, 1);
v___y_489_ = v_a_382_;
v___y_490_ = v_a_383_;
v___y_491_ = v_a_384_;
v___y_492_ = v_a_385_;
v___y_493_ = v_a_386_;
v___y_494_ = v_a_387_;
v___y_495_ = v_a_388_;
v___y_496_ = v_a_389_;
v___y_497_ = v_a_390_;
v___y_498_ = v_a_391_;
goto v___jp_488_;
}
else
{
lean_dec_ref_known(v_e_381_, 3);
return v___x_536_;
}
}
else
{
lean_dec_ref_known(v_e_381_, 3);
return v___x_534_;
}
}
v___jp_397_:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Simp_Result_getProof(v___y_399_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__2, &l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
lean_inc_ref(v___y_401_);
lean_inc_ref(v_binderType_394_);
v___x_412_ = l_Lean_mkApp5(v___x_411_, v_binderType_394_, v___y_398_, v___y_401_, v___y_402_, v_a_410_);
v___x_413_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_381_, v___y_401_, v___x_412_, v___y_400_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_413_;
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec_ref(v___y_398_);
lean_dec_ref_known(v_e_381_, 3);
v_a_414_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_409_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_409_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
v___jp_425_:
{
lean_object* v___x_437_; 
lean_inc_ref(v_binderType_394_);
v___x_437_ = l_Lean_Meta_Grind_mkEqTrueProof(v_binderType_394_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc_n(v_a_438_, 2);
lean_dec_ref_known(v___x_437_, 1);
lean_inc_ref(v_binderType_394_);
v___x_439_ = l_Lean_Meta_mkOfEqTrueCore(v_binderType_394_, v_a_438_);
v___x_440_ = lean_expr_instantiate1(v_body_395_, v___x_439_);
lean_dec_ref(v___x_439_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc(v___y_427_);
v___x_441_ = lean_grind_preprocess(v___x_440_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_381_, v___y_427_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v_expr_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v_expr_445_ = lean_ctor_get(v_a_442_, 0);
lean_inc_ref_n(v_expr_445_, 2);
v___x_446_ = lean_box(0);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc(v___y_427_);
v___x_447_ = lean_grind_internalize(v_expr_445_, v_a_444_, v___x_446_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_toCold_448_; lean_object* v_options_449_; lean_object* v_inheritedTraceOptions_450_; uint8_t v_hasTrace_451_; lean_object* v___x_452_; 
lean_dec_ref_known(v___x_447_, 1);
v_toCold_448_ = lean_ctor_get(v___y_435_, 0);
v_options_449_ = lean_ctor_get(v_toCold_448_, 2);
v_inheritedTraceOptions_450_ = lean_ctor_get(v_toCold_448_, 11);
v_hasTrace_451_ = lean_ctor_get_uint8(v_options_449_, sizeof(void*)*1);
lean_inc_ref(v_body_395_);
lean_inc_ref(v_binderType_394_);
lean_inc(v_binderName_393_);
v___x_452_ = l_Lean_mkLambda(v_binderName_393_, v_binderInfo_396_, v_binderType_394_, v_body_395_);
if (v_hasTrace_451_ == 0)
{
v___y_398_ = v___x_452_;
v___y_399_ = v_a_442_;
v___y_400_ = v___y_426_;
v___y_401_ = v_expr_445_;
v___y_402_ = v_a_438_;
v___y_403_ = v___y_427_;
v___y_404_ = v___y_429_;
v___y_405_ = v___y_433_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_435_;
v___y_408_ = v___y_436_;
goto v___jp_397_;
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__7, &l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
v___x_454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_450_, v_options_449_, v___x_453_);
if (v___x_454_ == 0)
{
v___y_398_ = v___x_452_;
v___y_399_ = v_a_442_;
v___y_400_ = v___y_426_;
v___y_401_ = v_expr_445_;
v___y_402_ = v_a_438_;
v___y_403_ = v___y_427_;
v___y_404_ = v___y_429_;
v___y_405_ = v___y_433_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_435_;
v___y_408_ = v___y_436_;
goto v___jp_397_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_Grind_updateLastTag(v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref_known(v___x_455_, 1);
v___x_456_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__9, &l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
lean_inc_ref(v_expr_445_);
v___x_457_ = l_Lean_MessageData_ofExpr(v_expr_445_);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__11, &l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
lean_inc_ref(v_e_381_);
v___x_461_ = l_Lean_indentExpr(v_e_381_);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_424_, v___x_462_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_dec_ref_known(v___x_463_, 1);
v___y_398_ = v___x_452_;
v___y_399_ = v_a_442_;
v___y_400_ = v___y_426_;
v___y_401_ = v_expr_445_;
v___y_402_ = v_a_438_;
v___y_403_ = v___y_427_;
v___y_404_ = v___y_429_;
v___y_405_ = v___y_433_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_435_;
v___y_408_ = v___y_436_;
goto v___jp_397_;
}
else
{
lean_dec_ref(v___x_452_);
lean_dec_ref(v_expr_445_);
lean_dec(v_a_442_);
lean_dec(v_a_438_);
lean_dec_ref_known(v_e_381_, 3);
return v___x_463_;
}
}
else
{
lean_dec_ref(v___x_452_);
lean_dec_ref(v_expr_445_);
lean_dec(v_a_442_);
lean_dec(v_a_438_);
lean_dec_ref_known(v_e_381_, 3);
return v___x_455_;
}
}
}
}
else
{
lean_dec_ref(v_expr_445_);
lean_dec(v_a_442_);
lean_dec(v_a_438_);
lean_dec_ref_known(v_e_381_, 3);
return v___x_447_;
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_a_442_);
lean_dec(v_a_438_);
lean_dec_ref_known(v_e_381_, 3);
v_a_464_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_443_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_443_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_a_438_);
lean_dec_ref_known(v_e_381_, 3);
v_a_472_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_441_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_441_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref_known(v_e_381_, 3);
v_a_480_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_437_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_437_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
v___jp_488_:
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_Expr_hasLooseBVars(v_body_395_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_inc_ref(v_body_395_);
lean_inc_ref(v_binderType_394_);
v___x_500_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_381_, v_binderType_394_, v_body_395_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
lean_inc_ref(v_binderType_394_);
v___x_501_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_394_, v___y_489_, v___y_493_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_522_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_522_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_522_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_522_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v___x_506_; 
v___x_506_ = lean_unbox(v_a_502_);
lean_dec(v_a_502_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec_ref_known(v_e_381_, 3);
v___x_507_ = lean_box(0);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_507_);
v___x_509_ = v___x_504_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v_toCold_511_; lean_object* v_inheritedTraceOptions_512_; lean_object* v___x_513_; lean_object* v_a_514_; uint8_t v___x_515_; uint8_t v___x_516_; 
lean_del_object(v___x_504_);
v_toCold_511_ = lean_ctor_get(v___y_497_, 0);
v_inheritedTraceOptions_512_ = lean_ctor_get(v_toCold_511_, 11);
v___x_513_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_424_, v_inheritedTraceOptions_512_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref(v___x_513_);
v___x_515_ = 0;
v___x_516_ = lean_unbox(v_a_514_);
lean_dec(v_a_514_);
if (v___x_516_ == 0)
{
v___y_426_ = v___x_515_;
v___y_427_ = v___y_489_;
v___y_428_ = v___y_490_;
v___y_429_ = v___y_491_;
v___y_430_ = v___y_492_;
v___y_431_ = v___y_493_;
v___y_432_ = v___y_494_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_496_;
v___y_435_ = v___y_497_;
v___y_436_ = v___y_498_;
goto v___jp_425_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Meta_Grind_updateLastTag(v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref_known(v___x_517_, 1);
v___x_518_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__13, &l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13);
lean_inc_ref(v_e_381_);
v___x_519_ = l_Lean_MessageData_ofExpr(v_e_381_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_424_, v___x_520_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_dec_ref_known(v___x_521_, 1);
v___y_426_ = v___x_515_;
v___y_427_ = v___y_489_;
v___y_428_ = v___y_490_;
v___y_429_ = v___y_491_;
v___y_430_ = v___y_492_;
v___y_431_ = v___y_493_;
v___y_432_ = v___y_494_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_496_;
v___y_435_ = v___y_497_;
v___y_436_ = v___y_498_;
goto v___jp_425_;
}
else
{
lean_dec_ref_known(v_e_381_, 3);
return v___x_521_;
}
}
else
{
lean_dec_ref_known(v_e_381_, 3);
return v___x_517_;
}
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref_known(v_e_381_, 3);
v_a_523_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_501_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_501_);
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
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref(v_e_381_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* v_e_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Meta_Grind_propagateForallPropUp(v_e_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec(v_a_540_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* v_cls_552_, lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_552_, v_msg_553_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* v_cls_566_, lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(v_cls_566_, v_msg_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec(v___y_568_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* v_origin_582_, lean_object* v_proof_583_, lean_object* v_kind_584_, lean_object* v_prios_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; uint8_t v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; 
v___x_591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
v___x_592_ = 0;
v___x_593_ = 1;
v___x_594_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v_origin_582_, v___x_591_, v_proof_583_, v_kind_584_, v_prios_585_, v___x_592_, v___x_592_, v___x_593_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_594_) == 0)
{
return v___x_594_;
}
else
{
lean_object* v_a_595_; uint8_t v___y_597_; uint8_t v___x_607_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
v___x_607_ = l_Lean_Exception_isInterrupt(v_a_595_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_Exception_isRuntime(v_a_595_);
v___y_597_ = v___x_608_;
goto v___jp_596_;
}
else
{
lean_dec(v_a_595_);
v___y_597_ = v___x_607_;
goto v___jp_596_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_594_, 0);
lean_dec(v_unused_606_);
v___x_599_ = v___x_594_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_dec(v___x_594_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 0);
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* v_origin_609_, lean_object* v_proof_610_, lean_object* v_kind_611_, lean_object* v_prios_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_origin_609_, v_proof_610_, v_kind_611_, v_prios_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
if (lean_obj_tag(v_x_620_) == 0)
{
uint8_t v___x_621_; 
v___x_621_ = 1;
return v___x_621_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = 0;
return v___x_622_;
}
}
else
{
if (lean_obj_tag(v_x_620_) == 0)
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
else
{
lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v_head_626_; lean_object* v_tail_627_; uint8_t v___x_628_; 
v_head_624_ = lean_ctor_get(v_x_619_, 0);
v_tail_625_ = lean_ctor_get(v_x_619_, 1);
v_head_626_ = lean_ctor_get(v_x_620_, 0);
v_tail_627_ = lean_ctor_get(v_x_620_, 1);
v___x_628_ = lean_expr_eqv(v_head_624_, v_head_626_);
if (v___x_628_ == 0)
{
return v___x_628_;
}
else
{
v_x_619_ = v_tail_625_;
v_x_620_ = v_tail_627_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_x_630_, v_x_631_);
lean_dec(v_x_631_);
lean_dec(v_x_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* v_thm_x27_634_, lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_eq(v_i_636_, v_stop_637_);
if (v___x_638_ == 0)
{
lean_object* v_patterns_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_patterns_639_ = lean_ctor_get(v_thm_x27_634_, 3);
v___x_640_ = lean_array_uget_borrowed(v_as_635_, v_i_636_);
v___x_641_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_patterns_639_, v___x_640_);
if (v___x_641_ == 0)
{
size_t v___x_642_; size_t v___x_643_; 
v___x_642_ = ((size_t)1ULL);
v___x_643_ = lean_usize_add(v_i_636_, v___x_642_);
v_i_636_ = v___x_643_;
goto _start;
}
else
{
return v___x_641_;
}
}
else
{
uint8_t v___x_645_; 
v___x_645_ = 0;
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* v_thm_x27_646_, lean_object* v_as_647_, lean_object* v_i_648_, lean_object* v_stop_649_){
_start:
{
size_t v_i_boxed_650_; size_t v_stop_boxed_651_; uint8_t v_res_652_; lean_object* v_r_653_; 
v_i_boxed_650_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_stop_boxed_651_ = lean_unbox_usize(v_stop_649_);
lean_dec(v_stop_649_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_646_, v_as_647_, v_i_boxed_650_, v_stop_boxed_651_);
lean_dec_ref(v_as_647_);
lean_dec_ref(v_thm_x27_646_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object* v_patternsFoundSoFar_654_, lean_object* v_thm_x27_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_patternsFoundSoFar_654_);
v___x_658_ = lean_nat_dec_lt(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = 1;
return v___x_659_;
}
else
{
if (v___x_658_ == 0)
{
return v___x_658_;
}
else
{
size_t v___x_660_; size_t v___x_661_; uint8_t v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_657_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_655_, v_patternsFoundSoFar_654_, v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
return v___x_658_;
}
else
{
uint8_t v___x_663_; 
v___x_663_ = 0;
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object* v_patternsFoundSoFar_664_, lean_object* v_thm_x27_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_664_, v_thm_x27_665_);
lean_dec_ref(v_thm_x27_665_);
lean_dec_ref(v_patternsFoundSoFar_664_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(lean_object* v_proof_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; 
lean_inc_ref(v_proof_679_);
v___x_683_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_679_, v_a_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_775_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_775_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_775_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_775_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___y_689_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = l_Lean_Expr_cleanupAnnotations(v_a_684_);
v___x_760_ = l_Lean_Expr_isApp(v___x_759_);
if (v___x_760_ == 0)
{
lean_dec_ref(v___x_759_);
v___y_689_ = v_a_680_;
goto v___jp_688_;
}
else
{
lean_object* v_arg_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_arg_761_ = lean_ctor_get(v___x_759_, 1);
lean_inc_ref(v_arg_761_);
v___x_762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_759_);
v___x_763_ = l_Lean_Expr_isApp(v___x_762_);
if (v___x_763_ == 0)
{
lean_dec_ref(v___x_762_);
lean_dec_ref(v_arg_761_);
v___y_689_ = v_a_680_;
goto v___jp_688_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_764_ = l_Lean_Expr_appFnCleanup___redArg(v___x_762_);
v___x_765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3));
v___x_766_ = l_Lean_Expr_isConstOf(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_Expr_isApp(v___x_764_);
if (v___x_767_ == 0)
{
lean_dec_ref(v___x_764_);
lean_dec_ref(v_arg_761_);
v___y_689_ = v_a_680_;
goto v___jp_688_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = l_Lean_Expr_appFnCleanup___redArg(v___x_764_);
v___x_769_ = l_Lean_Expr_isApp(v___x_768_);
if (v___x_769_ == 0)
{
lean_dec_ref(v___x_768_);
lean_dec_ref(v_arg_761_);
v___y_689_ = v_a_680_;
goto v___jp_688_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_768_);
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6));
v___x_772_ = l_Lean_Expr_isConstOf(v___x_770_, v___x_771_);
lean_dec_ref(v___x_770_);
if (v___x_772_ == 0)
{
lean_dec_ref(v_arg_761_);
v___y_689_ = v_a_680_;
goto v___jp_688_;
}
else
{
lean_del_object(v___x_686_);
lean_dec_ref(v_proof_679_);
v_proof_679_ = v_arg_761_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v___x_764_);
lean_del_object(v___x_686_);
lean_dec_ref(v_proof_679_);
v_proof_679_ = v_arg_761_;
goto _start;
}
}
}
v___jp_688_:
{
if (lean_obj_tag(v_proof_679_) == 1)
{
lean_object* v_fvarId_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v_fvarId_690_ = lean_ctor_get(v_proof_679_, 0);
lean_inc(v_fvarId_690_);
lean_dec_ref_known(v_proof_679_, 1);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v_fvarId_690_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_691_);
v___x_693_ = v___x_686_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
lean_object* v___x_695_; lean_object* v_toGoalState_696_; lean_object* v_ematch_697_; lean_object* v_mvarId_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_proof_679_);
v___x_695_ = lean_st_ref_take(v___y_689_);
v_toGoalState_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_toGoalState_696_);
v_ematch_697_ = lean_ctor_get(v_toGoalState_696_, 12);
lean_inc_ref(v_ematch_697_);
v_mvarId_698_ = lean_ctor_get(v___x_695_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_758_);
v___x_700_ = v___x_695_;
v_isShared_701_ = v_isSharedCheck_757_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_mvarId_698_);
lean_dec(v___x_695_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_757_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_nextDeclIdx_702_; lean_object* v_enodeMap_703_; lean_object* v_exprs_704_; lean_object* v_parents_705_; lean_object* v_congrTable_706_; lean_object* v_appMap_707_; lean_object* v_indicesFound_708_; lean_object* v_newFacts_709_; uint8_t v_inconsistent_710_; lean_object* v_nextIdx_711_; lean_object* v_newRawFacts_712_; lean_object* v_facts_713_; lean_object* v_extThms_714_; lean_object* v_inj_715_; lean_object* v_split_716_; lean_object* v_clean_717_; lean_object* v_sstates_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_755_; 
v_nextDeclIdx_702_ = lean_ctor_get(v_toGoalState_696_, 0);
v_enodeMap_703_ = lean_ctor_get(v_toGoalState_696_, 1);
v_exprs_704_ = lean_ctor_get(v_toGoalState_696_, 2);
v_parents_705_ = lean_ctor_get(v_toGoalState_696_, 3);
v_congrTable_706_ = lean_ctor_get(v_toGoalState_696_, 4);
v_appMap_707_ = lean_ctor_get(v_toGoalState_696_, 5);
v_indicesFound_708_ = lean_ctor_get(v_toGoalState_696_, 6);
v_newFacts_709_ = lean_ctor_get(v_toGoalState_696_, 7);
v_inconsistent_710_ = lean_ctor_get_uint8(v_toGoalState_696_, sizeof(void*)*17);
v_nextIdx_711_ = lean_ctor_get(v_toGoalState_696_, 8);
v_newRawFacts_712_ = lean_ctor_get(v_toGoalState_696_, 9);
v_facts_713_ = lean_ctor_get(v_toGoalState_696_, 10);
v_extThms_714_ = lean_ctor_get(v_toGoalState_696_, 11);
v_inj_715_ = lean_ctor_get(v_toGoalState_696_, 13);
v_split_716_ = lean_ctor_get(v_toGoalState_696_, 14);
v_clean_717_ = lean_ctor_get(v_toGoalState_696_, 15);
v_sstates_718_ = lean_ctor_get(v_toGoalState_696_, 16);
v_isSharedCheck_755_ = !lean_is_exclusive(v_toGoalState_696_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_toGoalState_696_, 12);
lean_dec(v_unused_756_);
v___x_720_ = v_toGoalState_696_;
v_isShared_721_ = v_isSharedCheck_755_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_sstates_718_);
lean_inc(v_clean_717_);
lean_inc(v_split_716_);
lean_inc(v_inj_715_);
lean_inc(v_extThms_714_);
lean_inc(v_facts_713_);
lean_inc(v_newRawFacts_712_);
lean_inc(v_nextIdx_711_);
lean_inc(v_newFacts_709_);
lean_inc(v_indicesFound_708_);
lean_inc(v_appMap_707_);
lean_inc(v_congrTable_706_);
lean_inc(v_parents_705_);
lean_inc(v_exprs_704_);
lean_inc(v_enodeMap_703_);
lean_inc(v_nextDeclIdx_702_);
lean_dec(v_toGoalState_696_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_755_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_thmMap_722_; lean_object* v_gmt_723_; lean_object* v_thms_724_; lean_object* v_newThms_725_; lean_object* v_numInstances_726_; lean_object* v_numDelayedInstances_727_; lean_object* v_num_728_; lean_object* v_preInstances_729_; lean_object* v_nextThmIdx_730_; lean_object* v_matchEqNames_731_; lean_object* v_delayedThmInsts_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_754_; 
v_thmMap_722_ = lean_ctor_get(v_ematch_697_, 0);
v_gmt_723_ = lean_ctor_get(v_ematch_697_, 1);
v_thms_724_ = lean_ctor_get(v_ematch_697_, 2);
v_newThms_725_ = lean_ctor_get(v_ematch_697_, 3);
v_numInstances_726_ = lean_ctor_get(v_ematch_697_, 4);
v_numDelayedInstances_727_ = lean_ctor_get(v_ematch_697_, 5);
v_num_728_ = lean_ctor_get(v_ematch_697_, 6);
v_preInstances_729_ = lean_ctor_get(v_ematch_697_, 7);
v_nextThmIdx_730_ = lean_ctor_get(v_ematch_697_, 8);
v_matchEqNames_731_ = lean_ctor_get(v_ematch_697_, 9);
v_delayedThmInsts_732_ = lean_ctor_get(v_ematch_697_, 10);
v_isSharedCheck_754_ = !lean_is_exclusive(v_ematch_697_);
if (v_isSharedCheck_754_ == 0)
{
v___x_734_ = v_ematch_697_;
v_isShared_735_ = v_isSharedCheck_754_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_delayedThmInsts_732_);
lean_inc(v_matchEqNames_731_);
lean_inc(v_nextThmIdx_730_);
lean_inc(v_preInstances_729_);
lean_inc(v_num_728_);
lean_inc(v_numDelayedInstances_727_);
lean_inc(v_numInstances_726_);
lean_inc(v_newThms_725_);
lean_inc(v_thms_724_);
lean_inc(v_gmt_723_);
lean_inc(v_thmMap_722_);
lean_dec(v_ematch_697_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_754_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_nextThmIdx_730_, v___x_736_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 8, v___x_737_);
v___x_739_ = v___x_734_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_thmMap_722_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_gmt_723_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_thms_724_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_newThms_725_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_numInstances_726_);
lean_ctor_set(v_reuseFailAlloc_753_, 5, v_numDelayedInstances_727_);
lean_ctor_set(v_reuseFailAlloc_753_, 6, v_num_728_);
lean_ctor_set(v_reuseFailAlloc_753_, 7, v_preInstances_729_);
lean_ctor_set(v_reuseFailAlloc_753_, 8, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_753_, 9, v_matchEqNames_731_);
lean_ctor_set(v_reuseFailAlloc_753_, 10, v_delayedThmInsts_732_);
v___x_739_ = v_reuseFailAlloc_753_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 12, v___x_739_);
v___x_741_ = v___x_720_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_nextDeclIdx_702_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_enodeMap_703_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_exprs_704_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_parents_705_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_congrTable_706_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v_appMap_707_);
lean_ctor_set(v_reuseFailAlloc_752_, 6, v_indicesFound_708_);
lean_ctor_set(v_reuseFailAlloc_752_, 7, v_newFacts_709_);
lean_ctor_set(v_reuseFailAlloc_752_, 8, v_nextIdx_711_);
lean_ctor_set(v_reuseFailAlloc_752_, 9, v_newRawFacts_712_);
lean_ctor_set(v_reuseFailAlloc_752_, 10, v_facts_713_);
lean_ctor_set(v_reuseFailAlloc_752_, 11, v_extThms_714_);
lean_ctor_set(v_reuseFailAlloc_752_, 12, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_752_, 13, v_inj_715_);
lean_ctor_set(v_reuseFailAlloc_752_, 14, v_split_716_);
lean_ctor_set(v_reuseFailAlloc_752_, 15, v_clean_717_);
lean_ctor_set(v_reuseFailAlloc_752_, 16, v_sstates_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*17, v_inconsistent_710_);
v___x_741_ = v_reuseFailAlloc_752_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_741_);
v___x_743_ = v___x_700_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_mvarId_698_);
v___x_743_ = v_reuseFailAlloc_751_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_744_ = lean_st_ref_put(v___y_689_, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1));
v___x_746_ = lean_name_append_index_after(v___x_745_, v_nextThmIdx_730_);
v___x_747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_747_);
v___x_749_ = v___x_686_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
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
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_proof_679_);
v_a_776_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_683_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_683_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___boxed(lean_object* v_proof_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec(v_a_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(lean_object* v_proof_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_789_, v_a_790_, v_a_797_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___boxed(lean_object* v_proof_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(v_proof_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec(v_a_803_);
return v_res_814_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t v_a_815_, lean_object* v_as_816_, size_t v_i_817_, size_t v_stop_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_eq(v_i_817_, v_stop_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_array_uget_borrowed(v_as_816_, v_i_817_);
v___x_821_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_820_, v_a_815_);
if (v___x_821_ == 0)
{
size_t v___x_822_; size_t v___x_823_; 
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_817_, v___x_822_);
v_i_817_ = v___x_823_;
goto _start;
}
else
{
return v___x_821_;
}
}
else
{
uint8_t v___x_825_; 
v___x_825_ = 0;
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object* v_a_826_, lean_object* v_as_827_, lean_object* v_i_828_, lean_object* v_stop_829_){
_start:
{
uint64_t v_a_3836__boxed_830_; size_t v_i_boxed_831_; size_t v_stop_boxed_832_; uint8_t v_res_833_; lean_object* v_r_834_; 
v_a_3836__boxed_830_ = lean_unbox_uint64(v_a_826_);
lean_dec_ref(v_a_826_);
v_i_boxed_831_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_stop_boxed_832_ = lean_unbox_usize(v_stop_829_);
lean_dec(v_stop_829_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v_a_3836__boxed_830_, v_as_827_, v_i_boxed_831_, v_stop_boxed_832_);
lean_dec_ref(v_as_827_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* v_proof_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_837_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_900_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_900_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_900_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_900_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
if (lean_obj_tag(v_a_847_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_852_; 
lean_del_object(v___x_849_);
v_val_851_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v_a_847_, 1);
lean_inc(v_a_844_);
lean_inc_ref(v_a_843_);
lean_inc(v_a_842_);
lean_inc_ref(v_a_841_);
v___x_852_ = lean_infer_type(v_proof_835_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_Lean_Meta_Grind_getAnchor(v_a_853_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_878_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_878_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_878_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_878_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_array_get_size(v_val_851_);
v___x_861_ = lean_nat_dec_lt(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec(v_a_855_);
lean_dec(v_val_851_);
v___x_862_ = lean_box(v___x_861_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_862_);
v___x_864_ = v___x_857_;
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
if (v___x_861_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec(v_a_855_);
lean_dec(v_val_851_);
v___x_866_ = lean_box(v___x_861_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_866_);
v___x_868_ = v___x_857_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
size_t v___x_870_; size_t v___x_871_; uint64_t v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_870_ = ((size_t)0ULL);
v___x_871_ = lean_usize_of_nat(v___x_860_);
v___x_872_ = lean_unbox_uint64(v_a_855_);
lean_dec(v_a_855_);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v___x_872_, v_val_851_, v___x_870_, v___x_871_);
lean_dec(v_val_851_);
v___x_874_ = lean_box(v___x_873_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_874_);
v___x_876_ = v___x_857_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_val_851_);
v_a_879_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_854_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_854_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_val_851_);
v_a_887_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_852_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_852_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec(v_a_847_);
lean_dec_ref(v_proof_835_);
v___x_895_ = 1;
v___x_896_ = lean_box(v___x_895_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_896_);
v___x_898_ = v___x_849_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_proof_835_);
v_a_901_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_846_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_846_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* v_proof_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* v_a_921_, lean_object* v_as_922_, size_t v_sz_923_, size_t v_i_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_a_938_; uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_924_, v_sz_923_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v_a_921_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_925_);
return v___x_943_;
}
else
{
lean_object* v_a_944_; uint8_t v___x_945_; 
v_a_944_ = lean_array_uget_borrowed(v_as_922_, v_i_924_);
v___x_945_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_b_925_, v_a_944_);
if (v___x_945_ == 0)
{
v_a_938_ = v_b_925_;
goto v___jp_937_;
}
else
{
lean_object* v___x_946_; 
lean_inc(v_a_921_);
lean_inc(v_a_944_);
v___x_946_ = l_Lean_Meta_Grind_activateTheorem(v_a_944_, v_a_921_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_patterns_947_; lean_object* v___x_948_; 
lean_dec_ref_known(v___x_946_, 1);
v_patterns_947_ = lean_ctor_get(v_a_944_, 3);
lean_inc(v_patterns_947_);
v___x_948_ = lean_array_push(v_b_925_, v_patterns_947_);
v_a_938_ = v___x_948_;
goto v___jp_937_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v_b_925_);
lean_dec(v_a_921_);
v_a_949_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_946_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_924_, v___x_939_);
v_i_924_ = v___x_940_;
v_b_925_ = v_a_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* v_a_957_, lean_object* v_as_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
size_t v_sz_boxed_973_; size_t v_i_boxed_974_; lean_object* v_res_975_; 
v_sz_boxed_973_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_974_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_957_, v_as_958_, v_sz_boxed_973_, v_i_boxed_974_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v_as_958_);
return v_res_975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* v_e_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; 
lean_inc_ref(v_e_981_);
v___x_993_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc_n(v_a_994_, 2);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_a_994_, v_a_982_, v_a_989_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
lean_inc_ref(v_e_981_);
v___x_997_ = l_Lean_Meta_mkOfEqTrueCore(v_e_981_, v_a_994_);
lean_inc_ref(v___x_997_);
v___x_998_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v___x_997_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1182_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1182_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1182_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_unbox(v_a_999_);
lean_dec(v_a_999_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v___x_1004_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_del_object(v___x_1001_);
v___x_1008_ = lean_st_ref_get(v_a_982_);
v___x_1009_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_981_, v_a_982_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = l_Lean_Meta_Grind_getSymbolPriorities___redArg(v_a_984_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_n(v_a_1012_, 2);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = lean_unsigned_to_nat(1000u);
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
v___x_1015_ = 0;
lean_inc_ref(v___x_997_);
lean_inc(v_a_996_);
v___x_1016_ = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(v_a_996_, v___x_1014_, v___x_997_, v___x_1013_, v_a_1012_, v___x_1015_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; size_t v_sz_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v_sz_1018_ = lean_array_size(v_a_1017_);
v___x_1019_ = ((size_t)0ULL);
lean_inc(v_a_1010_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_1010_, v_a_1017_, v_sz_1018_, v___x_1019_, v___x_1014_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_1017_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = lean_box(6);
lean_inc(v_a_1012_);
lean_inc_ref(v___x_997_);
lean_inc(v_a_996_);
v___x_1023_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_996_, v___x_997_, v___x_1022_, v_a_1012_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_toGoalState_1024_; lean_object* v_ematch_1025_; lean_object* v_newThms_1026_; lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1141_; 
v_toGoalState_1024_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_toGoalState_1024_);
lean_dec(v___x_1008_);
v_ematch_1025_ = lean_ctor_get(v_toGoalState_1024_, 12);
lean_inc_ref(v_ematch_1025_);
lean_dec_ref(v_toGoalState_1024_);
v_newThms_1026_ = lean_ctor_get(v_ematch_1025_, 3);
lean_inc_ref(v_newThms_1026_);
lean_dec_ref(v_ematch_1025_);
v_a_1027_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1029_ = v___x_1023_;
v_isShared_1030_ = v_isSharedCheck_1141_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1023_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1141_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_size_1031_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v_patternsFoundSoFar_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; 
v_size_1031_ = lean_ctor_get(v_newThms_1026_, 2);
lean_inc(v_size_1031_);
lean_dec_ref(v_newThms_1026_);
if (lean_obj_tag(v_a_1027_) == 1)
{
lean_object* v_val_1136_; uint8_t v___x_1137_; 
v_val_1136_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v_a_1027_, 1);
v___x_1137_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_a_1021_, v_val_1136_);
if (v___x_1137_ == 0)
{
lean_dec(v_val_1136_);
v_patternsFoundSoFar_1111_ = v_a_1021_;
v___y_1112_ = v_a_982_;
v___y_1113_ = v_a_983_;
v___y_1114_ = v_a_984_;
v___y_1115_ = v_a_985_;
v___y_1116_ = v_a_986_;
v___y_1117_ = v_a_987_;
v___y_1118_ = v_a_988_;
v___y_1119_ = v_a_989_;
v___y_1120_ = v_a_990_;
v___y_1121_ = v_a_991_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1138_; 
lean_inc(v_a_1010_);
lean_inc(v_val_1136_);
v___x_1138_ = l_Lean_Meta_Grind_activateTheorem(v_val_1136_, v_a_1010_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_patterns_1139_; lean_object* v___x_1140_; 
lean_dec_ref_known(v___x_1138_, 1);
v_patterns_1139_ = lean_ctor_get(v_val_1136_, 3);
lean_inc(v_patterns_1139_);
lean_dec(v_val_1136_);
v___x_1140_ = lean_array_push(v_a_1021_, v_patterns_1139_);
v_patternsFoundSoFar_1111_ = v___x_1140_;
v___y_1112_ = v_a_982_;
v___y_1113_ = v_a_983_;
v___y_1114_ = v_a_984_;
v___y_1115_ = v_a_985_;
v___y_1116_ = v_a_986_;
v___y_1117_ = v_a_987_;
v___y_1118_ = v_a_988_;
v___y_1119_ = v_a_989_;
v___y_1120_ = v_a_990_;
v___y_1121_ = v_a_991_;
goto v___jp_1110_;
}
else
{
lean_dec(v_val_1136_);
lean_dec(v_size_1031_);
lean_del_object(v___x_1029_);
lean_dec(v_a_1021_);
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
return v___x_1138_;
}
}
}
else
{
lean_dec(v_a_1027_);
v_patternsFoundSoFar_1111_ = v_a_1021_;
v___y_1112_ = v_a_982_;
v___y_1113_ = v_a_983_;
v___y_1114_ = v_a_984_;
v___y_1115_ = v_a_985_;
v___y_1116_ = v_a_986_;
v___y_1117_ = v_a_987_;
v___y_1118_ = v_a_988_;
v___y_1119_ = v_a_989_;
v___y_1120_ = v_a_990_;
v___y_1121_ = v_a_991_;
goto v___jp_1110_;
}
v___jp_1032_:
{
lean_object* v___x_1040_; lean_object* v_toGoalState_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1078_; 
v___x_1040_ = lean_st_ref_get(v___y_1033_);
v_toGoalState_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_1040_, 1);
lean_dec(v_unused_1079_);
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1078_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_toGoalState_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1078_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_ematch_1045_; lean_object* v_newThms_1046_; lean_object* v_size_1047_; uint8_t v___x_1048_; 
v_ematch_1045_ = lean_ctor_get(v_toGoalState_1041_, 12);
lean_inc_ref(v_ematch_1045_);
lean_dec_ref(v_toGoalState_1041_);
v_newThms_1046_ = lean_ctor_get(v_ematch_1045_, 3);
lean_inc_ref(v_newThms_1046_);
lean_dec_ref(v_ematch_1045_);
v_size_1047_ = lean_ctor_get(v_newThms_1046_, 2);
lean_inc(v_size_1047_);
lean_dec_ref(v_newThms_1046_);
v___x_1048_ = lean_nat_dec_eq(v_size_1047_, v_size_1031_);
lean_dec(v_size_1031_);
lean_dec(v_size_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
lean_del_object(v___x_1043_);
lean_dec_ref(v_e_981_);
v___x_1049_ = lean_box(0);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1049_);
v___x_1051_ = v___x_1029_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v___x_1053_; 
lean_del_object(v___x_1029_);
v___x_1053_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1034_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1069_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1069_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1069_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
uint8_t v_verbose_1058_; 
v_verbose_1058_ = lean_ctor_get_uint8(v_a_1054_, 0);
lean_dec(v_a_1054_);
if (v_verbose_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_del_object(v___x_1043_);
lean_dec_ref(v_e_981_);
v___x_1059_ = lean_box(0);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_del_object(v___x_1056_);
v___x_1063_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
v___x_1064_ = l_Lean_indentExpr(v_e_981_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 7);
lean_ctor_set(v___x_1043_, 1, v___x_1064_);
lean_ctor_set(v___x_1043_, 0, v___x_1063_);
v___x_1066_ = v___x_1043_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Sym_reportIssue(v___x_1066_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_del_object(v___x_1043_);
lean_dec_ref(v_e_981_);
v_a_1070_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1053_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1053_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
v___jp_1080_:
{
lean_object* v___x_1091_; lean_object* v_toGoalState_1092_; lean_object* v_ematch_1093_; lean_object* v_newThms_1094_; lean_object* v_size_1095_; uint8_t v___x_1096_; 
v___x_1091_ = lean_st_ref_get(v___y_1081_);
v_toGoalState_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_toGoalState_1092_);
lean_dec(v___x_1091_);
v_ematch_1093_ = lean_ctor_get(v_toGoalState_1092_, 12);
lean_inc_ref(v_ematch_1093_);
lean_dec_ref(v_toGoalState_1092_);
v_newThms_1094_ = lean_ctor_get(v_ematch_1093_, 3);
lean_inc_ref(v_newThms_1094_);
lean_dec_ref(v_ematch_1093_);
v_size_1095_ = lean_ctor_get(v_newThms_1094_, 2);
lean_inc(v_size_1095_);
lean_dec_ref(v_newThms_1094_);
v___x_1096_ = lean_nat_dec_eq(v_size_1095_, v_size_1031_);
lean_dec(v_size_1095_);
if (v___x_1096_ == 0)
{
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
v___y_1033_ = v___y_1081_;
v___y_1034_ = v___y_1085_;
v___y_1035_ = v___y_1086_;
v___y_1036_ = v___y_1087_;
v___y_1037_ = v___y_1088_;
v___y_1038_ = v___y_1089_;
v___y_1039_ = v___y_1090_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2));
v___x_1098_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_996_, v___x_997_, v___x_1097_, v_a_1012_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
if (lean_obj_tag(v_a_1099_) == 1)
{
lean_object* v_val_1100_; lean_object* v___x_1101_; 
v_val_1100_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v_a_1099_, 1);
v___x_1101_ = l_Lean_Meta_Grind_activateTheorem(v_val_1100_, v_a_1010_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_dec_ref_known(v___x_1101_, 1);
v___y_1033_ = v___y_1081_;
v___y_1034_ = v___y_1085_;
v___y_1035_ = v___y_1086_;
v___y_1036_ = v___y_1087_;
v___y_1037_ = v___y_1088_;
v___y_1038_ = v___y_1089_;
v___y_1039_ = v___y_1090_;
goto v___jp_1032_;
}
else
{
lean_dec(v_size_1031_);
lean_del_object(v___x_1029_);
lean_dec_ref(v_e_981_);
return v___x_1101_;
}
}
else
{
lean_dec(v_a_1099_);
lean_dec(v_a_1010_);
v___y_1033_ = v___y_1081_;
v___y_1034_ = v___y_1085_;
v___y_1035_ = v___y_1086_;
v___y_1036_ = v___y_1087_;
v___y_1037_ = v___y_1088_;
v___y_1038_ = v___y_1089_;
v___y_1039_ = v___y_1090_;
goto v___jp_1032_;
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_size_1031_);
lean_del_object(v___x_1029_);
lean_dec(v_a_1010_);
lean_dec_ref(v_e_981_);
v_a_1102_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1098_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1098_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
v___jp_1110_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_box(7);
lean_inc(v_a_1012_);
lean_inc_ref(v___x_997_);
lean_inc(v_a_996_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_996_, v___x_997_, v___x_1122_, v_a_1012_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
if (lean_obj_tag(v_a_1124_) == 1)
{
lean_object* v_val_1125_; uint8_t v___x_1126_; 
v_val_1125_ = lean_ctor_get(v_a_1124_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v_a_1124_, 1);
v___x_1126_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_1111_, v_val_1125_);
lean_dec_ref(v_patternsFoundSoFar_1111_);
if (v___x_1126_ == 0)
{
lean_dec(v_val_1125_);
v___y_1081_ = v___y_1112_;
v___y_1082_ = v___y_1113_;
v___y_1083_ = v___y_1114_;
v___y_1084_ = v___y_1115_;
v___y_1085_ = v___y_1116_;
v___y_1086_ = v___y_1117_;
v___y_1087_ = v___y_1118_;
v___y_1088_ = v___y_1119_;
v___y_1089_ = v___y_1120_;
v___y_1090_ = v___y_1121_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1127_; 
lean_inc(v_a_1010_);
v___x_1127_ = l_Lean_Meta_Grind_activateTheorem(v_val_1125_, v_a_1010_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_dec_ref_known(v___x_1127_, 1);
v___y_1081_ = v___y_1112_;
v___y_1082_ = v___y_1113_;
v___y_1083_ = v___y_1114_;
v___y_1084_ = v___y_1115_;
v___y_1085_ = v___y_1116_;
v___y_1086_ = v___y_1117_;
v___y_1087_ = v___y_1118_;
v___y_1088_ = v___y_1119_;
v___y_1089_ = v___y_1120_;
v___y_1090_ = v___y_1121_;
goto v___jp_1080_;
}
else
{
lean_dec(v_size_1031_);
lean_del_object(v___x_1029_);
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
return v___x_1127_;
}
}
}
else
{
lean_dec(v_a_1124_);
lean_dec_ref(v_patternsFoundSoFar_1111_);
v___y_1081_ = v___y_1112_;
v___y_1082_ = v___y_1113_;
v___y_1083_ = v___y_1114_;
v___y_1084_ = v___y_1115_;
v___y_1085_ = v___y_1116_;
v___y_1086_ = v___y_1117_;
v___y_1087_ = v___y_1118_;
v___y_1088_ = v___y_1119_;
v___y_1089_ = v___y_1120_;
v___y_1090_ = v___y_1121_;
goto v___jp_1080_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_patternsFoundSoFar_1111_);
lean_dec(v_size_1031_);
lean_del_object(v___x_1029_);
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v_a_1128_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1123_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1123_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_a_1021_);
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_dec(v___x_1008_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v_a_1142_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1023_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1023_);
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
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_dec(v___x_1008_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v_a_1150_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1020_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1020_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_a_1012_);
lean_dec(v_a_1010_);
lean_dec(v___x_1008_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v_a_1158_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1016_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1016_);
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
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_a_1010_);
lean_dec(v___x_1008_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v_a_1166_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1011_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1011_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v___x_1008_);
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v_a_1174_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1009_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1009_);
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
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v___x_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_e_981_);
v_a_1183_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_998_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_998_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_a_994_);
lean_dec_ref(v_e_981_);
v_a_1191_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_995_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_995_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_e_981_);
v_a_1199_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_993_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_993_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* v_e_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec(v_a_1208_);
return v_res_1219_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1225_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_1226_ = l_Lean_Name_append(v___x_1225_, v___x_1224_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__3));
v___x_1229_ = l_Lean_stringToMessageData(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__10));
v___x_1245_ = l_Lean_mkConst(v___x_1244_, v___x_1243_);
return v___x_1245_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__13));
v___x_1253_ = l_Lean_mkConst(v___x_1252_, v___x_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* v_e_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
if (lean_obj_tag(v_e_1254_) == 7)
{
lean_object* v_binderName_1266_; lean_object* v_binderType_1267_; lean_object* v_body_1268_; uint8_t v_binderInfo_1269_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___x_1378_; 
v_binderName_1266_ = lean_ctor_get(v_e_1254_, 0);
v_binderType_1267_ = lean_ctor_get(v_e_1254_, 1);
v_body_1268_ = lean_ctor_get(v_e_1254_, 2);
v_binderInfo_1269_ = lean_ctor_get_uint8(v_e_1254_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_1254_);
v___x_1378_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1254_, v_a_1255_, v_a_1259_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; uint8_t v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = lean_unbox(v_a_1379_);
lean_dec(v_a_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_inc_ref(v_e_1254_);
v___x_1381_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1254_, v_a_1255_, v_a_1259_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1466_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1466_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1466_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_unbox(v_a_1382_);
lean_dec(v_a_1382_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec_ref_known(v_e_1254_, 3);
v___x_1387_ = lean_box(0);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v___x_1391_; 
lean_del_object(v___x_1384_);
lean_inc_ref(v_e_1254_);
v___x_1391_ = l_Lean_Meta_Grind_eqResolution(v_e_1254_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
if (lean_obj_tag(v_a_1392_) == 1)
{
lean_object* v_val_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1457_; 
v_val_1393_ = lean_ctor_get(v_a_1392_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_a_1392_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1395_ = v_a_1392_;
v_isShared_1396_ = v_isSharedCheck_1457_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_val_1393_);
lean_dec(v_a_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1457_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1456_; 
v_fst_1397_ = lean_ctor_get(v_val_1393_, 0);
v_snd_1398_ = lean_ctor_get(v_val_1393_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_val_1393_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1400_ = v_val_1393_;
v_isShared_1401_ = v_isSharedCheck_1456_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snd_1398_);
lean_inc(v_fst_1397_);
lean_dec(v_val_1393_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1456_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v_toCold_1440_; lean_object* v_options_1441_; uint8_t v_hasTrace_1442_; 
v_toCold_1440_ = lean_ctor_get(v_a_1263_, 0);
v_options_1441_ = lean_ctor_get(v_toCold_1440_, 2);
v_hasTrace_1442_ = lean_ctor_get_uint8(v_options_1441_, sizeof(void*)*1);
if (v_hasTrace_1442_ == 0)
{
lean_del_object(v___x_1400_);
v___y_1403_ = v_a_1255_;
v___y_1404_ = v_a_1256_;
v___y_1405_ = v_a_1257_;
v___y_1406_ = v_a_1258_;
v___y_1407_ = v_a_1259_;
v___y_1408_ = v_a_1260_;
v___y_1409_ = v_a_1261_;
v___y_1410_ = v_a_1262_;
v___y_1411_ = v_a_1263_;
v___y_1412_ = v_a_1264_;
goto v___jp_1402_;
}
else
{
lean_object* v_inheritedTraceOptions_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_inheritedTraceOptions_1443_ = lean_ctor_get(v_toCold_1440_, 11);
v___x_1444_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1445_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__2, &l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2);
v___x_1446_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1443_, v_options_1441_, v___x_1445_);
if (v___x_1446_ == 0)
{
lean_del_object(v___x_1400_);
v___y_1403_ = v_a_1255_;
v___y_1404_ = v_a_1256_;
v___y_1405_ = v_a_1257_;
v___y_1406_ = v_a_1258_;
v___y_1407_ = v_a_1259_;
v___y_1408_ = v_a_1260_;
v___y_1409_ = v_a_1261_;
v___y_1410_ = v_a_1262_;
v___y_1411_ = v_a_1263_;
v___y_1412_ = v_a_1264_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_Meta_Grind_updateLastTag(v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec_ref_known(v___x_1447_, 1);
lean_inc_ref(v_e_1254_);
v___x_1448_ = l_Lean_MessageData_ofExpr(v_e_1254_);
v___x_1449_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__4, &l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4);
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 7);
lean_ctor_set(v___x_1400_, 1, v___x_1449_);
lean_ctor_set(v___x_1400_, 0, v___x_1448_);
v___x_1451_ = v___x_1400_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_inc(v_fst_1397_);
v___x_1452_ = l_Lean_MessageData_ofExpr(v_fst_1397_);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v___x_1444_, v___x_1453_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_dec_ref_known(v___x_1454_, 1);
v___y_1403_ = v_a_1255_;
v___y_1404_ = v_a_1256_;
v___y_1405_ = v_a_1257_;
v___y_1406_ = v_a_1258_;
v___y_1407_ = v_a_1259_;
v___y_1408_ = v_a_1260_;
v___y_1409_ = v_a_1261_;
v___y_1410_ = v_a_1262_;
v___y_1411_ = v_a_1263_;
v___y_1412_ = v_a_1264_;
goto v___jp_1402_;
}
else
{
lean_dec(v_snd_1398_);
lean_dec(v_fst_1397_);
lean_del_object(v___x_1395_);
lean_dec_ref_known(v_e_1254_, 3);
return v___x_1454_;
}
}
}
else
{
lean_del_object(v___x_1400_);
lean_dec(v_snd_1398_);
lean_dec(v_fst_1397_);
lean_del_object(v___x_1395_);
lean_dec_ref_known(v_e_1254_, 3);
return v___x_1447_;
}
}
}
v___jp_1402_:
{
lean_object* v___x_1413_; 
lean_inc_ref(v_e_1254_);
v___x_1413_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1254_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1254_, v___y_1403_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
lean_inc_ref_n(v_e_1254_, 2);
v___x_1417_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1254_, v_a_1414_);
v___x_1418_ = l_Lean_Expr_app___override(v_snd_1398_, v___x_1417_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 4);
lean_ctor_set(v___x_1395_, 0, v_e_1254_);
v___x_1420_ = v___x_1395_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_e_1254_);
v___x_1420_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_box(1);
v___x_1422_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1418_, v_fst_1397_, v_a_1416_, v___x_1420_, v___x_1421_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_dec_ref_known(v___x_1422_, 1);
v___y_1324_ = v___y_1403_;
v___y_1325_ = v___y_1404_;
v___y_1326_ = v___y_1405_;
v___y_1327_ = v___y_1406_;
v___y_1328_ = v___y_1407_;
v___y_1329_ = v___y_1408_;
v___y_1330_ = v___y_1409_;
v___y_1331_ = v___y_1410_;
v___y_1332_ = v___y_1411_;
v___y_1333_ = v___y_1412_;
goto v___jp_1323_;
}
else
{
lean_dec_ref_known(v_e_1254_, 3);
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_a_1414_);
lean_dec(v_snd_1398_);
lean_dec(v_fst_1397_);
lean_del_object(v___x_1395_);
lean_dec_ref_known(v_e_1254_, 3);
v_a_1424_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1415_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1415_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_snd_1398_);
lean_dec(v_fst_1397_);
lean_del_object(v___x_1395_);
lean_dec_ref_known(v_e_1254_, 3);
v_a_1432_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1413_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1413_);
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
}
else
{
lean_dec(v_a_1392_);
v___y_1324_ = v_a_1255_;
v___y_1325_ = v_a_1256_;
v___y_1326_ = v_a_1257_;
v___y_1327_ = v_a_1258_;
v___y_1328_ = v_a_1259_;
v___y_1329_ = v_a_1260_;
v___y_1330_ = v_a_1261_;
v___y_1331_ = v_a_1262_;
v___y_1332_ = v_a_1263_;
v___y_1333_ = v_a_1264_;
goto v___jp_1323_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref_known(v_e_1254_, 3);
v_a_1458_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1391_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1391_);
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
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref_known(v_e_1254_, 3);
v_a_1467_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1381_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1381_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v___x_1475_; 
lean_inc_ref(v_binderType_1267_);
v___x_1475_ = l_Lean_Meta_isProp(v_binderType_1267_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; uint8_t v___x_1522_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1522_ = l_Lean_Expr_hasLooseBVars(v_body_1268_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_unbox(v_a_1476_);
lean_dec(v_a_1476_);
if (v___x_1523_ == 0)
{
goto v___jp_1477_;
}
else
{
if (v___x_1522_ == 0)
{
lean_object* v___x_1524_; 
lean_inc_ref(v_body_1268_);
lean_inc_ref(v_binderType_1267_);
v___x_1524_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_n(v_a_1525_, 2);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__11, &l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
lean_inc_ref(v_body_1268_);
lean_inc_ref_n(v_binderType_1267_, 2);
v___x_1527_ = l_Lean_mkApp3(v___x_1526_, v_binderType_1267_, v_body_1268_, v_a_1525_);
v___x_1528_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_binderType_1267_, v___x_1527_, v_a_1255_, v_a_1257_, v_a_1259_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec_ref_known(v___x_1528_, 1);
v___x_1529_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__14, &l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14);
lean_inc_ref(v_body_1268_);
v___x_1530_ = l_Lean_mkApp3(v___x_1529_, v_binderType_1267_, v_body_1268_, v_a_1525_);
v___x_1531_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_body_1268_, v___x_1530_, v_a_1255_, v_a_1257_, v_a_1259_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v___x_1531_;
}
else
{
lean_dec(v_a_1525_);
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
return v___x_1528_;
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
v_a_1532_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1524_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1524_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
goto v___jp_1477_;
}
}
}
else
{
lean_dec(v_a_1476_);
goto v___jp_1477_;
}
v___jp_1477_:
{
lean_object* v___x_1478_; 
lean_inc_ref(v_binderType_1267_);
v___x_1478_ = l_Lean_Meta_getLevel(v_binderType_1267_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
lean_inc_ref(v_e_1254_);
v___x_1480_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
lean_inc_ref(v_body_1268_);
v___x_1482_ = l_Lean_mkNot(v_body_1268_);
lean_inc_ref(v_binderType_1267_);
lean_inc(v_binderName_1266_);
v___x_1483_ = l_Lean_mkLambda(v_binderName_1266_, v_binderInfo_1269_, v_binderType_1267_, v___x_1482_);
v___x_1484_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1486_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_a_1479_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
lean_inc_ref(v___x_1488_);
v___x_1489_ = l_Lean_mkConst(v___x_1486_, v___x_1488_);
lean_inc_ref_n(v_binderType_1267_, 3);
v___x_1490_ = l_Lean_mkAppB(v___x_1489_, v_binderType_1267_, v___x_1483_);
lean_inc_ref(v_body_1268_);
lean_inc(v_binderName_1266_);
v___x_1491_ = l_Lean_mkLambda(v_binderName_1266_, v_binderInfo_1269_, v_binderType_1267_, v_body_1268_);
v___x_1492_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__8));
v___x_1493_ = l_Lean_mkConst(v___x_1492_, v___x_1488_);
v___x_1494_ = l_Lean_mkApp3(v___x_1493_, v_binderType_1267_, v___x_1491_, v_a_1481_);
v___x_1495_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_e_1254_);
v___x_1496_ = lean_box(1);
v___x_1497_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1494_, v___x_1490_, v_a_1485_, v___x_1495_, v___x_1496_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v___x_1497_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v___x_1483_);
lean_dec(v_a_1481_);
lean_dec(v_a_1479_);
lean_dec_ref_known(v_e_1254_, 3);
v_a_1498_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1484_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1484_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_a_1479_);
lean_dec_ref_known(v_e_1254_, 3);
v_a_1506_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1480_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1480_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref_known(v_e_1254_, 3);
v_a_1514_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1478_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1478_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec_ref_known(v_e_1254_, 3);
v_a_1540_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1475_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1475_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref_known(v_e_1254_, 3);
v_a_1548_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1378_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1378_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
v___jp_1270_:
{
if (lean_obj_tag(v___y_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1314_; 
v_a_1282_ = lean_ctor_get(v___y_1281_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___y_1281_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1284_ = v___y_1281_;
v_isShared_1285_ = v_isSharedCheck_1314_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___y_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1314_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_unbox(v_a_1282_);
lean_dec(v_a_1282_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
lean_dec_ref_known(v_e_1254_, 3);
v___x_1287_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; 
lean_del_object(v___x_1284_);
v___x_1291_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1254_, v___y_1273_, v___y_1272_, v___y_1271_, v___y_1276_, v___y_1275_, v___y_1279_, v___y_1274_, v___y_1278_, v___y_1280_, v___y_1277_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
lean_inc_ref(v_body_1268_);
v___x_1293_ = l_Lean_Meta_Grind_mkEqFalseProof(v_body_1268_, v___y_1273_, v___y_1272_, v___y_1271_, v___y_1276_, v___y_1275_, v___y_1279_, v___y_1274_, v___y_1278_, v___y_1280_, v___y_1277_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(v_binderType_1267_);
v___x_1296_ = l_Lean_mkApp4(v___x_1295_, v_binderType_1267_, v_body_1268_, v_a_1292_, v_a_1294_);
v___x_1297_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_binderType_1267_, v___x_1296_, v___y_1273_, v___y_1271_, v___y_1275_, v___y_1274_, v___y_1278_, v___y_1280_, v___y_1277_);
return v___x_1297_;
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_a_1292_);
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
v_a_1298_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1293_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1293_);
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
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
v_a_1306_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1291_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1291_);
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
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
lean_dec_ref_known(v_e_1254_, 3);
v_a_1315_ = lean_ctor_get(v___y_1281_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___y_1281_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___y_1281_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___y_1281_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
v___jp_1323_:
{
uint8_t v___x_1334_; 
v___x_1334_ = l_Lean_Expr_hasLooseBVars(v_body_1268_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_inc_ref(v_body_1268_);
lean_inc_ref(v_binderType_1267_);
v___x_1335_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_body_1268_, v___y_1324_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1349_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1349_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1349_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_unbox(v_a_1336_);
lean_dec(v_a_1336_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
lean_dec_ref_known(v_e_1254_, 3);
v___x_1341_ = lean_box(0);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1341_);
v___x_1343_ = v___x_1338_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v___x_1345_; 
lean_del_object(v___x_1338_);
lean_inc_ref(v_body_1268_);
v___x_1345_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_1268_, v___y_1324_, v___y_1328_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; uint8_t v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
v___x_1347_ = lean_unbox(v_a_1346_);
lean_dec(v_a_1346_);
if (v___x_1347_ == 0)
{
v___y_1271_ = v___y_1326_;
v___y_1272_ = v___y_1325_;
v___y_1273_ = v___y_1324_;
v___y_1274_ = v___y_1330_;
v___y_1275_ = v___y_1328_;
v___y_1276_ = v___y_1327_;
v___y_1277_ = v___y_1333_;
v___y_1278_ = v___y_1331_;
v___y_1279_ = v___y_1329_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___x_1345_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref_known(v___x_1345_, 1);
lean_inc_ref(v_binderType_1267_);
v___x_1348_ = l_Lean_Meta_isProp(v_binderType_1267_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
v___y_1271_ = v___y_1326_;
v___y_1272_ = v___y_1325_;
v___y_1273_ = v___y_1324_;
v___y_1274_ = v___y_1330_;
v___y_1275_ = v___y_1328_;
v___y_1276_ = v___y_1327_;
v___y_1277_ = v___y_1333_;
v___y_1278_ = v___y_1331_;
v___y_1279_ = v___y_1329_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___x_1348_;
goto v___jp_1270_;
}
}
else
{
v___y_1271_ = v___y_1326_;
v___y_1272_ = v___y_1325_;
v___y_1273_ = v___y_1324_;
v___y_1274_ = v___y_1330_;
v___y_1275_ = v___y_1328_;
v___y_1276_ = v___y_1327_;
v___y_1277_ = v___y_1333_;
v___y_1278_ = v___y_1331_;
v___y_1279_ = v___y_1329_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___x_1345_;
goto v___jp_1270_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_body_1268_);
lean_dec_ref(v_binderType_1267_);
lean_dec_ref_known(v_e_1254_, 3);
v_a_1350_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1335_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1335_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v___x_1358_; 
lean_inc_ref(v_binderType_1267_);
v___x_1358_ = l_Lean_Meta_isProp(v_binderType_1267_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1369_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1369_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1369_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_unbox(v_a_1359_);
lean_dec(v_a_1359_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_del_object(v___x_1361_);
v___x_1364_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1254_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec_ref_known(v_e_1254_, 3);
v___x_1365_ = lean_box(0);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1365_);
v___x_1367_ = v___x_1361_;
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
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref_known(v_e_1254_, 3);
v_a_1370_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1358_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1358_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v_e_1254_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* v_e_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Meta_Grind_propagateForallPropDown(v_e_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec(v_a_1559_);
return v_res_1570_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1576_ = l_Lean_mkConst(v___x_1575_, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = l_Lean_Expr_bvar___override(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* v_e_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1600_; 
lean_inc_ref(v_e_1585_);
v___x_1600_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1585_, v_a_1586_, v_a_1590_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1655_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1655_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1655_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_unbox(v_a_1601_);
lean_dec(v_a_1601_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
lean_dec_ref(v_e_1585_);
v___x_1606_ = lean_box(0);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1606_);
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
else
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
lean_del_object(v___x_1603_);
lean_inc_ref(v_e_1585_);
v___x_1610_ = l_Lean_Expr_cleanupAnnotations(v_e_1585_);
v___x_1611_ = l_Lean_Expr_isApp(v___x_1610_);
if (v___x_1611_ == 0)
{
lean_dec_ref(v___x_1610_);
lean_dec_ref(v_e_1585_);
goto v___jp_1597_;
}
else
{
lean_object* v_arg_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_arg_1612_ = lean_ctor_get(v___x_1610_, 1);
lean_inc_ref(v_arg_1612_);
v___x_1613_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1610_);
v___x_1614_ = l_Lean_Expr_isApp(v___x_1613_);
if (v___x_1614_ == 0)
{
lean_dec_ref(v___x_1613_);
lean_dec_ref(v_arg_1612_);
lean_dec_ref(v_e_1585_);
goto v___jp_1597_;
}
else
{
lean_object* v_arg_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_arg_1615_ = lean_ctor_get(v___x_1613_, 1);
lean_inc_ref(v_arg_1615_);
v___x_1616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1613_);
v___x_1617_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1618_ = l_Lean_Expr_isConstOf(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_dec_ref(v___x_1616_);
lean_dec_ref(v_arg_1615_);
lean_dec_ref(v_arg_1612_);
lean_dec_ref(v_e_1585_);
goto v___jp_1597_;
}
else
{
lean_object* v___x_1619_; 
lean_inc_ref(v_e_1585_);
v___x_1619_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__2, &l_Lean_Meta_Grind_propagateExistsDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2);
v___x_1624_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__3, &l_Lean_Meta_Grind_propagateExistsDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3);
lean_inc_ref(v_arg_1612_);
v___x_1625_ = l_Lean_Expr_app___override(v_arg_1612_, v___x_1624_);
v___x_1626_ = l_Lean_Expr_headBeta(v___x_1625_);
v___x_1627_ = l_Lean_Expr_app___override(v___x_1623_, v___x_1626_);
v___x_1628_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__5));
v___x_1629_ = 0;
lean_inc_ref(v_arg_1615_);
v___x_1630_ = l_Lean_mkForall(v___x_1628_, v___x_1629_, v_arg_1615_, v___x_1627_);
v___x_1631_ = l_Lean_Expr_constLevels_x21(v___x_1616_);
lean_dec_ref(v___x_1616_);
v___x_1632_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__7));
v___x_1633_ = l_Lean_mkConst(v___x_1632_, v___x_1631_);
lean_inc_ref(v_e_1585_);
v___x_1634_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1585_, v_a_1620_);
v___x_1635_ = l_Lean_mkApp3(v___x_1633_, v_arg_1615_, v_arg_1612_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_e_1585_);
v___x_1637_ = lean_box(1);
v___x_1638_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1635_, v___x_1630_, v_a_1622_, v___x_1636_, v___x_1637_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1638_;
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_a_1620_);
lean_dec_ref(v___x_1616_);
lean_dec_ref(v_arg_1615_);
lean_dec_ref(v_arg_1612_);
lean_dec_ref(v_e_1585_);
v_a_1639_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1621_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1621_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v___x_1616_);
lean_dec_ref(v_arg_1615_);
lean_dec_ref(v_arg_1612_);
lean_dec_ref(v_e_1585_);
v_a_1647_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1619_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1619_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_e_1585_);
v_a_1656_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1600_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1600_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
v___jp_1597_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* v_e_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_Grind_propagateExistsDown(v_e_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec(v_a_1665_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1679_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 12, 0);
v___x_1680_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1678_, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9____boxed(lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_();
return v_res_1682_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_1691_ = l_Lean_mkConst(v___x_1690_, v___x_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object* v_e_1692_){
_start:
{
if (lean_obj_tag(v_e_1692_) == 7)
{
lean_object* v_binderName_1693_; lean_object* v_binderType_1694_; lean_object* v_body_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_binderName_1693_ = lean_ctor_get(v_e_1692_, 0);
v_binderType_1694_ = lean_ctor_get(v_e_1692_, 1);
v_body_1695_ = lean_ctor_get(v_e_1692_, 2);
lean_inc_ref(v_body_1695_);
lean_inc_ref(v_binderType_1694_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_binderType_1694_);
lean_ctor_set(v___x_1696_, 1, v_body_1695_);
lean_inc(v_binderName_1693_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_binderName_1693_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1699_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = l_Lean_Expr_isAppOfArity(v_e_1692_, v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_box(0);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1));
v___x_1704_ = l_Lean_Expr_appArg_x21(v_e_1692_);
v___x_1705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1703_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object* v_e_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_e_1709_);
lean_dec_ref(v_e_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* v_fst_1711_, lean_object* v_a_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_expr_instantiate1(v_fst_1711_, v_a_1712_);
v___x_1722_ = l_Lean_Meta_getLevel(v___x_1721_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* v_fst_1723_, lean_object* v_a_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Meta_Grind_simpForall___lam__0(v_fst_1723_, v_a_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v_a_1724_);
lean_dec_ref(v_fst_1723_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
lean_inc(v___y_1735_);
v___x_1744_ = lean_apply_9(v_k_1734_, v_b_1738_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, lean_box(0));
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(v_k_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v_b_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* v_name_1756_, uint8_t v_bi_1757_, lean_object* v_type_1758_, lean_object* v_k_1759_, uint8_t v_kind_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___f_1769_; lean_object* v___x_1770_; 
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v___y_1761_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1769_, 0, v_k_1759_);
lean_closure_set(v___f_1769_, 1, v___y_1761_);
lean_closure_set(v___f_1769_, 2, v___y_1762_);
lean_closure_set(v___f_1769_, 3, v___y_1763_);
v___x_1770_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1756_, v_bi_1757_, v_type_1758_, v___f_1769_, v_kind_1760_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1770_) == 0)
{
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_1779_, lean_object* v_bi_1780_, lean_object* v_type_1781_, lean_object* v_k_1782_, lean_object* v_kind_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v_bi_boxed_1792_; uint8_t v_kind_boxed_1793_; lean_object* v_res_1794_; 
v_bi_boxed_1792_ = lean_unbox(v_bi_1780_);
v_kind_boxed_1793_ = lean_unbox(v_kind_1783_);
v_res_1794_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1779_, v_bi_boxed_1792_, v_type_1781_, v_k_1782_, v_kind_boxed_1793_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* v_name_1795_, lean_object* v_type_1796_, lean_object* v_k_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = 0;
v___x_1807_ = 0;
v___x_1808_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1795_, v___x_1806_, v_type_1796_, v_k_1797_, v___x_1807_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* v_name_1809_, lean_object* v_type_1810_, lean_object* v_k_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_1809_, v_type_1810_, v_k_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
return v_res_1820_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__13(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(0);
v___x_1848_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_1849_ = l_Lean_mkConst(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__16(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__15));
v___x_1857_ = l_Lean_mkConst(v___x_1856_, v___x_1855_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__21(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__20));
v___x_1870_ = l_Lean_mkConst(v___x_1869_, v___x_1868_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__24(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_box(0);
v___x_1877_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__23));
v___x_1878_ = l_Lean_mkConst(v___x_1877_, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__27(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_box(0);
v___x_1885_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__26));
v___x_1886_ = l_Lean_mkConst(v___x_1885_, v___x_1884_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__30(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__29));
v___x_1894_ = l_Lean_mkConst(v___x_1893_, v___x_1892_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__33(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__32));
v___x_1901_ = l_Lean_mkConst(v___x_1900_, v___x_1899_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__36(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_box(0);
v___x_1908_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__35));
v___x_1909_ = l_Lean_mkConst(v___x_1908_, v___x_1907_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__37(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = l_Lean_Level_ofNat(v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__38(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__37, &l_Lean_Meta_Grind_simpForall___closed__37_once, _init_l_Lean_Meta_Grind_simpForall___closed__37);
v___x_1913_ = l_Lean_mkSort(v___x_1912_);
return v___x_1913_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__41(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__40));
v___x_1919_ = l_Lean_mkConst(v___x_1918_, v___x_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* v_e_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
if (lean_obj_tag(v_e_1920_) == 7)
{
lean_object* v_binderName_1932_; lean_object* v_binderType_1933_; lean_object* v_body_1934_; uint8_t v_binderInfo_1935_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; uint8_t v___y_1944_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___x_2144_; 
v_binderName_1932_ = lean_ctor_get(v_e_1920_, 0);
lean_inc(v_binderName_1932_);
v_binderType_1933_ = lean_ctor_get(v_e_1920_, 1);
lean_inc_ref(v_binderType_1933_);
v_body_1934_ = lean_ctor_get(v_e_1920_, 2);
lean_inc_ref(v_body_1934_);
v_binderInfo_1935_ = lean_ctor_get_uint8(v_e_1920_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1920_, 3);
v___x_2144_ = l_Lean_Expr_hasLooseBVars(v_body_1934_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_inc_ref(v_binderType_1933_);
v___x_2145_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1933_, v_a_1925_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; uint8_t v___x_2147_; lean_object* v___y_2149_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2147_ = 1;
v___x_2173_ = l_Lean_Expr_cleanupAnnotations(v_a_2146_);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2175_ = l_Lean_Expr_isConstOf(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_2177_ = l_Lean_Expr_isConstOf(v___x_2173_, v___x_2176_);
lean_dec_ref(v___x_2173_);
if (v___x_2177_ == 0)
{
if (lean_obj_tag(v_binderType_1933_) == 7)
{
lean_object* v_binderName_2178_; lean_object* v_binderType_2179_; lean_object* v_body_2180_; uint8_t v_binderInfo_2181_; uint8_t v_a_2183_; uint8_t v___x_2216_; 
v_binderName_2178_ = lean_ctor_get(v_binderType_1933_, 0);
v_binderType_2179_ = lean_ctor_get(v_binderType_1933_, 1);
v_body_2180_ = lean_ctor_get(v_binderType_1933_, 2);
v_binderInfo_2181_ = lean_ctor_get_uint8(v_binderType_1933_, sizeof(void*)*3 + 8);
v___x_2216_ = l_Lean_Expr_hasLooseBVars(v_body_2180_);
if (v___x_2216_ == 0)
{
v_a_2183_ = v___x_2216_;
goto v___jp_2182_;
}
else
{
lean_object* v___x_2217_; 
lean_inc_ref(v_binderType_1933_);
v___x_2217_ = l_Lean_Meta_isProp(v_binderType_1933_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; uint8_t v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = lean_unbox(v_a_2218_);
lean_dec(v_a_2218_);
v_a_2183_ = v___x_2219_;
goto v___jp_2182_;
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref_known(v_binderType_1933_, 3);
lean_dec_ref(v_body_1934_);
lean_dec(v_binderName_1932_);
v_a_2220_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2217_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2217_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
v___jp_2182_:
{
if (v_a_2183_ == 0)
{
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_inc_ref_n(v_body_2180_, 2);
lean_inc_ref_n(v_binderType_2179_, 3);
lean_inc_n(v_binderName_2178_, 2);
lean_dec_ref_known(v_binderType_1933_, 3);
lean_dec(v_binderName_1932_);
v___x_2184_ = l_Lean_mkLambda(v_binderName_2178_, v_binderInfo_2181_, v_binderType_2179_, v_body_2180_);
v___x_2185_ = l_Lean_Meta_getLevel(v_binderType_2179_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2207_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2207_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2207_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2190_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_a_2186_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
lean_inc_ref(v___x_2192_);
v___x_2193_ = l_Lean_mkConst(v___x_2190_, v___x_2192_);
v___x_2194_ = l_Lean_mkNot(v_body_2180_);
lean_inc_ref_n(v_binderType_2179_, 2);
v___x_2195_ = l_Lean_mkLambda(v_binderName_2178_, v_binderInfo_2181_, v_binderType_2179_, v___x_2194_);
v___x_2196_ = l_Lean_mkAppB(v___x_2193_, v_binderType_2179_, v___x_2195_);
lean_inc_ref(v_body_1934_);
v___x_2197_ = l_Lean_mkOr(v___x_2196_, v_body_1934_);
v___x_2198_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__18));
v___x_2199_ = l_Lean_mkConst(v___x_2198_, v___x_2192_);
v___x_2200_ = l_Lean_mkApp3(v___x_2199_, v_binderType_2179_, v___x_2184_, v_body_1934_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2202_, 0, v___x_2197_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*2, v___x_2147_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2203_);
v___x_2205_ = v___x_2188_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v___x_2184_);
lean_dec_ref(v_body_2180_);
lean_dec_ref(v_binderType_2179_);
lean_dec(v_binderName_2178_);
lean_dec_ref(v_body_1934_);
v_a_2208_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2185_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2185_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
else
{
lean_object* v___x_2228_; 
lean_inc_ref(v_body_1934_);
v___x_2228_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_1934_, v_a_1925_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___x_2230_ = l_Lean_Expr_cleanupAnnotations(v_a_2229_);
v___x_2231_ = l_Lean_Expr_isConstOf(v___x_2230_, v___x_2174_);
if (v___x_2231_ == 0)
{
uint8_t v___x_2232_; 
v___x_2232_ = l_Lean_Expr_isConstOf(v___x_2230_, v___x_2176_);
lean_dec_ref(v___x_2230_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; 
lean_inc_ref(v_binderType_1933_);
v___x_2233_ = l_Lean_Meta_isProp(v_binderType_1933_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; uint8_t v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
v___x_2235_ = lean_unbox(v_a_2234_);
lean_dec(v_a_2234_);
if (v___x_2235_ == 0)
{
v___y_2149_ = v___x_2233_;
goto v___jp_2148_;
}
else
{
lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2233_, 1);
lean_inc_ref(v_body_1934_);
lean_inc_ref(v_binderType_1933_);
v___x_2236_ = l_Lean_Meta_isExprDefEq(v_binderType_1933_, v_body_1934_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
v___y_2149_ = v___x_2236_;
goto v___jp_2148_;
}
}
else
{
v___y_2149_ = v___x_2233_;
goto v___jp_2148_;
}
}
else
{
lean_object* v___x_2237_; 
lean_inc_ref(v_binderType_1933_);
v___x_2237_ = l_Lean_Meta_isProp(v_binderType_1933_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2252_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2252_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2252_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_unbox(v_a_2238_);
lean_dec(v_a_2238_);
if (v___x_2242_ == 0)
{
lean_del_object(v___x_2240_);
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
lean_dec_ref(v_body_1934_);
lean_dec(v_binderName_1932_);
v___x_2243_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2244_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__21, &l_Lean_Meta_Grind_simpForall___closed__21_once, _init_l_Lean_Meta_Grind_simpForall___closed__21);
v___x_2245_ = l_Lean_Expr_app___override(v___x_2244_, v_binderType_1933_);
v___x_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2247_, 0, v___x_2243_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*2, v___x_2147_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2248_);
v___x_2250_ = v___x_2240_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2253_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2237_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2237_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
else
{
lean_object* v___x_2261_; 
lean_dec_ref(v___x_2230_);
lean_inc_ref(v_binderType_1933_);
v___x_2261_ = l_Lean_Meta_isProp(v_binderType_1933_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2276_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2276_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2276_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_unbox(v_a_2262_);
lean_dec(v_a_2262_);
if (v___x_2266_ == 0)
{
lean_del_object(v___x_2264_);
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec_ref(v_body_1934_);
lean_dec(v_binderName_1932_);
lean_inc_ref(v_binderType_1933_);
v___x_2267_ = l_Lean_mkNot(v_binderType_1933_);
v___x_2268_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__24, &l_Lean_Meta_Grind_simpForall___closed__24_once, _init_l_Lean_Meta_Grind_simpForall___closed__24);
v___x_2269_ = l_Lean_Expr_app___override(v___x_2268_, v_binderType_1933_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2271_, 0, v___x_2267_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*2, v___x_2147_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2272_);
v___x_2274_ = v___x_2264_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2277_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2261_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2261_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2285_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2228_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2228_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
else
{
lean_object* v___x_2293_; 
lean_inc_ref(v_body_1934_);
v___x_2293_ = l_Lean_Meta_isProp(v_body_1934_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2307_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2307_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2307_;
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
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v___x_2299_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__27, &l_Lean_Meta_Grind_simpForall___closed__27_once, _init_l_Lean_Meta_Grind_simpForall___closed__27);
lean_inc_ref(v_body_1934_);
v___x_2300_ = l_Lean_Expr_app___override(v___x_2299_, v_body_1934_);
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2302_, 0, v_body_1934_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*2, v___x_2147_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2303_);
v___x_2305_ = v___x_2296_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2308_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2293_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2293_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
else
{
lean_object* v___x_2316_; 
lean_dec_ref(v___x_2173_);
lean_inc_ref(v_body_1934_);
v___x_2316_ = l_Lean_Meta_isProp(v_body_1934_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2331_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2331_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2331_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
uint8_t v___x_2321_; 
v___x_2321_ = lean_unbox(v_a_2317_);
lean_dec(v_a_2317_);
if (v___x_2321_ == 0)
{
lean_del_object(v___x_2319_);
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v___x_2322_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2323_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__30, &l_Lean_Meta_Grind_simpForall___closed__30_once, _init_l_Lean_Meta_Grind_simpForall___closed__30);
v___x_2324_ = l_Lean_Expr_app___override(v___x_2323_, v_body_1934_);
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2326_, 0, v___x_2322_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*2, v___x_2147_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2327_);
v___x_2329_ = v___x_2319_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2332_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2316_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2316_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
v___jp_2148_:
{
if (lean_obj_tag(v___y_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2164_; 
v_a_2150_ = lean_ctor_get(v___y_2149_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___y_2149_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2152_ = v___y_2149_;
v_isShared_2153_ = v_isSharedCheck_2164_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___y_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2164_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_unbox(v_a_2150_);
lean_dec(v_a_2150_);
if (v___x_2154_ == 0)
{
lean_del_object(v___x_2152_);
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_dec_ref(v_body_1934_);
lean_dec(v_binderName_1932_);
v___x_2155_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2156_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__16, &l_Lean_Meta_Grind_simpForall___closed__16_once, _init_l_Lean_Meta_Grind_simpForall___closed__16);
v___x_2157_ = l_Lean_Expr_app___override(v___x_2156_, v_binderType_1933_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2159_, 0, v___x_2155_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*2, v___x_2147_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2160_);
v___x_2162_ = v___x_2152_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2165_ = lean_ctor_get(v___y_2149_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___y_2149_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___y_2149_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___y_2149_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2340_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2145_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2145_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v___x_2348_; 
lean_inc_ref(v_binderType_1933_);
v___x_2348_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1933_, v_a_1925_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = l_Lean_Expr_cleanupAnnotations(v_a_2349_);
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2352_ = l_Lean_Expr_isConstOf(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_2354_ = l_Lean_Expr_isConstOf(v___x_2350_, v___x_2353_);
lean_dec_ref(v___x_2350_);
if (v___x_2354_ == 0)
{
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__33, &l_Lean_Meta_Grind_simpForall___closed__33_once, _init_l_Lean_Meta_Grind_simpForall___closed__33);
v___x_2356_ = lean_expr_instantiate1(v_body_1934_, v___x_2355_);
lean_inc_ref(v___x_2356_);
v___x_2357_ = l_Lean_Meta_isProp(v___x_2356_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2372_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
uint8_t v___x_2362_; 
v___x_2362_ = lean_unbox(v_a_2358_);
lean_dec(v_a_2358_);
if (v___x_2362_ == 0)
{
lean_del_object(v___x_2360_);
lean_dec_ref(v___x_2356_);
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2363_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_body_1934_);
v___x_2364_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__36, &l_Lean_Meta_Grind_simpForall___closed__36_once, _init_l_Lean_Meta_Grind_simpForall___closed__36);
v___x_2365_ = l_Lean_Expr_app___override(v___x_2364_, v___x_2363_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2356_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*2, v___x_2144_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2368_);
v___x_2370_ = v___x_2360_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v___x_2356_);
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2373_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2357_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2357_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v___x_2350_);
lean_inc_ref(v_body_1934_);
lean_inc_ref(v_binderType_1933_);
lean_inc(v_binderName_1932_);
v___x_2381_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_body_1934_);
lean_inc(v_a_1927_);
lean_inc_ref(v_a_1926_);
lean_inc(v_a_1925_);
lean_inc_ref(v_a_1924_);
lean_inc_ref(v___x_2381_);
v___x_2382_ = lean_infer_type(v___x_2381_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__38, &l_Lean_Meta_Grind_simpForall___closed__38_once, _init_l_Lean_Meta_Grind_simpForall___closed__38);
lean_inc_ref(v_binderType_1933_);
lean_inc(v_binderName_1932_);
v___x_2385_ = l_Lean_mkForall(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v___x_2384_);
v___x_2386_ = l_Lean_Meta_isExprDefEq(v_a_2383_, v___x_2385_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2401_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2401_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2401_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_unbox(v_a_2387_);
lean_dec(v_a_2387_);
if (v___x_2391_ == 0)
{
lean_del_object(v___x_2389_);
lean_dec_ref(v___x_2381_);
v___y_2133_ = v_a_1921_;
v___y_2134_ = v_a_1922_;
v___y_2135_ = v_a_1923_;
v___y_2136_ = v_a_1924_;
v___y_2137_ = v_a_1925_;
v___y_2138_ = v_a_1926_;
v___y_2139_ = v_a_1927_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v___x_2392_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2393_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__41, &l_Lean_Meta_Grind_simpForall___closed__41_once, _init_l_Lean_Meta_Grind_simpForall___closed__41);
v___x_2394_ = l_Lean_Expr_app___override(v___x_2393_, v___x_2381_);
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2392_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*2, v___x_2144_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2397_);
v___x_2399_ = v___x_2389_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v___x_2381_);
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2402_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2386_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2386_);
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
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v___x_2381_);
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2410_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2382_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2382_);
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
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2418_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2348_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2348_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
v___jp_1936_:
{
if (v___y_1944_ == 0)
{
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
goto v___jp_1929_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = l_Lean_Expr_appFn_x21(v_body_1934_);
v___x_1946_ = l_Lean_Expr_appFn_x21(v___x_1945_);
if (lean_obj_tag(v___x_1946_) == 4)
{
lean_object* v_declName_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v_declName_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_declName_1947_);
lean_dec_ref_known(v___x_1946_, 2);
v___x_1948_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_1949_ = lean_name_eq(v_declName_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_1951_ = lean_name_eq(v_declName_1947_, v___x_1950_);
lean_dec(v_declName_1947_);
if (v___x_1951_ == 0)
{
lean_dec_ref(v___x_1945_);
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
goto v___jp_1929_;
}
else
{
lean_object* v_pRaw_1952_; lean_object* v_qRaw_1953_; lean_object* v_p_1954_; lean_object* v_q_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_pRaw_1952_ = l_Lean_Expr_appArg_x21(v___x_1945_);
lean_dec_ref(v___x_1945_);
v_qRaw_1953_ = l_Lean_Expr_appArg_x21(v_body_1934_);
lean_dec_ref(v_body_1934_);
lean_inc_ref(v_pRaw_1952_);
lean_inc_ref_n(v_binderType_1933_, 5);
lean_inc_n(v_binderName_1932_, 3);
v_p_1954_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_pRaw_1952_);
lean_inc_ref(v_qRaw_1953_);
v_q_1955_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_qRaw_1953_);
v___x_1956_ = l_Lean_mkForall(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_pRaw_1952_);
v___x_1957_ = l_Lean_mkForall(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_qRaw_1953_);
v___x_1958_ = l_Lean_Meta_getLevel(v_binderType_1933_, v___y_1940_, v___y_1941_, v___y_1943_, v___y_1939_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1975_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1975_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1975_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_expr_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v_expr_1963_ = l_Lean_mkAnd(v___x_1956_, v___x_1957_);
v___x_1964_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__6));
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1959_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_mkConst(v___x_1964_, v___x_1966_);
v___x_1968_ = l_Lean_mkApp3(v___x_1967_, v_binderType_1933_, v_p_1954_, v_q_1955_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1970_, 0, v_expr_1963_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*2, v___y_1944_);
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1971_);
v___x_1973_ = v___x_1961_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v___x_1957_);
lean_dec_ref(v___x_1956_);
lean_dec_ref(v_q_1955_);
lean_dec_ref(v_p_1954_);
lean_dec_ref(v_binderType_1933_);
v_a_1976_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1958_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1958_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
else
{
lean_object* v_pRaw_1984_; lean_object* v_pRaw_1985_; lean_object* v___x_1986_; 
lean_dec(v_declName_1947_);
v_pRaw_1984_ = l_Lean_Expr_appArg_x21(v___x_1945_);
lean_dec_ref(v___x_1945_);
v_pRaw_1985_ = l_Lean_Expr_appArg_x21(v_body_1934_);
lean_dec_ref(v_body_1934_);
v___x_1986_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1984_);
if (lean_obj_tag(v___x_1986_) == 1)
{
lean_object* v_val_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_pRaw_1984_);
v_val_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_2057_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_val_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2057_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_snd_1991_; lean_object* v_fst_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2056_; 
v_snd_1991_ = lean_ctor_get(v_val_1987_, 1);
v_fst_1992_ = lean_ctor_get(v_val_1987_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_val_1987_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_1994_ = v_val_1987_;
v_isShared_1995_ = v_isSharedCheck_2056_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_snd_1991_);
lean_inc(v_fst_1992_);
lean_dec(v_val_1987_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2056_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2055_; 
v_fst_1996_ = lean_ctor_get(v_snd_1991_, 0);
v_snd_1997_ = lean_ctor_get(v_snd_1991_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_snd_1991_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_1999_ = v_snd_1991_;
v_isShared_2000_ = v_isSharedCheck_2055_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_snd_1997_);
lean_inc(v_fst_1996_);
lean_dec(v_snd_1991_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2055_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v_p_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v_q_2004_; lean_object* v_00_u03b2_2005_; lean_object* v___x_2006_; 
lean_inc_ref(v_pRaw_1985_);
lean_inc_ref_n(v_binderType_1933_, 4);
lean_inc_n(v_binderName_1932_, 3);
v_p_2001_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_pRaw_1985_);
v___x_2002_ = 0;
lean_inc(v_snd_1997_);
lean_inc_n(v_fst_1996_, 2);
lean_inc(v_fst_1992_);
v___x_2003_ = l_Lean_mkLambda(v_fst_1992_, v___x_2002_, v_fst_1996_, v_snd_1997_);
v_q_2004_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v___x_2003_);
v_00_u03b2_2005_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_fst_1996_);
v___x_2006_ = l_Lean_Meta_getLevel(v_binderType_1933_, v___y_1940_, v___y_1941_, v___y_1943_, v___y_1939_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
lean_inc(v_fst_1996_);
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2008_, 0, v_fst_1996_);
lean_inc_ref(v_binderType_1933_);
lean_inc(v_binderName_1932_);
v___x_2009_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1932_, v_binderType_1933_, v___f_2008_, v___y_1938_, v___y_1942_, v___y_1937_, v___y_1940_, v___y_1941_, v___y_1943_, v___y_1939_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2038_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2038_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2038_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2014_ = lean_unsigned_to_nat(0u);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_expr_lift_loose_bvars(v_pRaw_1985_, v___x_2014_, v___x_2015_);
lean_dec_ref(v_pRaw_1985_);
v___x_2017_ = l_Lean_mkOr(v_snd_1997_, v___x_2016_);
v___x_2018_ = l_Lean_mkForall(v_fst_1992_, v___x_2002_, v_fst_1996_, v___x_2017_);
lean_inc_ref(v_binderType_1933_);
v___x_2019_ = l_Lean_mkForall(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_2021_ = lean_box(0);
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 1);
lean_ctor_set(v___x_1999_, 1, v___x_2021_);
lean_ctor_set(v___x_1999_, 0, v_a_2010_);
v___x_2023_ = v___x_1999_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2010_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 1);
lean_ctor_set(v___x_1994_, 1, v___x_2023_);
lean_ctor_set(v___x_1994_, 0, v_a_2007_);
v___x_2025_ = v___x_1994_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2007_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2026_ = l_Lean_mkConst(v___x_2020_, v___x_2025_);
v___x_2027_ = l_Lean_mkApp4(v___x_2026_, v_binderType_1933_, v_00_u03b2_2005_, v_p_2001_, v_q_2004_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2027_);
v___x_2029_ = v___x_1989_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2030_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2030_, 0, v___x_2019_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*2, v___y_1944_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2031_);
v___x_2033_ = v___x_2012_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_2007_);
lean_dec_ref(v_00_u03b2_2005_);
lean_dec_ref(v_q_2004_);
lean_dec_ref(v_p_2001_);
lean_del_object(v___x_1999_);
lean_dec(v_snd_1997_);
lean_dec(v_fst_1996_);
lean_del_object(v___x_1994_);
lean_dec(v_fst_1992_);
lean_del_object(v___x_1989_);
lean_dec_ref(v_pRaw_1985_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2039_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2009_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2009_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v_00_u03b2_2005_);
lean_dec_ref(v_q_2004_);
lean_dec_ref(v_p_2001_);
lean_del_object(v___x_1999_);
lean_dec(v_snd_1997_);
lean_dec(v_fst_1996_);
lean_del_object(v___x_1994_);
lean_dec(v_fst_1992_);
lean_del_object(v___x_1989_);
lean_dec_ref(v_pRaw_1985_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2047_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2006_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2006_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2058_; 
lean_dec(v___x_1986_);
v___x_2058_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1985_);
lean_dec_ref(v_pRaw_1985_);
if (lean_obj_tag(v___x_2058_) == 1)
{
lean_object* v_val_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2129_; 
v_val_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2129_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_val_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2129_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_snd_2063_; lean_object* v_fst_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2128_; 
v_snd_2063_ = lean_ctor_get(v_val_2059_, 1);
v_fst_2064_ = lean_ctor_get(v_val_2059_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_val_2059_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2066_ = v_val_2059_;
v_isShared_2067_ = v_isSharedCheck_2128_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_snd_2063_);
lean_inc(v_fst_2064_);
lean_dec(v_val_2059_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2128_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2127_; 
v_fst_2068_ = lean_ctor_get(v_snd_2063_, 0);
v_snd_2069_ = lean_ctor_get(v_snd_2063_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_snd_2063_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2071_ = v_snd_2063_;
v_isShared_2072_ = v_isSharedCheck_2127_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_inc(v_fst_2068_);
lean_dec(v_snd_2063_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2127_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_p_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v_q_2076_; lean_object* v_00_u03b2_2077_; lean_object* v___x_2078_; 
lean_inc_ref(v_pRaw_1984_);
lean_inc_ref_n(v_binderType_1933_, 4);
lean_inc_n(v_binderName_1932_, 3);
v_p_2073_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_pRaw_1984_);
v___x_2074_ = 0;
lean_inc(v_snd_2069_);
lean_inc_n(v_fst_2068_, 2);
lean_inc(v_fst_2064_);
v___x_2075_ = l_Lean_mkLambda(v_fst_2064_, v___x_2074_, v_fst_2068_, v_snd_2069_);
v_q_2076_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v___x_2075_);
v_00_u03b2_2077_ = l_Lean_mkLambda(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v_fst_2068_);
v___x_2078_ = l_Lean_Meta_getLevel(v_binderType_1933_, v___y_1940_, v___y_1941_, v___y_1943_, v___y_1939_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___f_2080_; lean_object* v___x_2081_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
lean_inc(v_fst_2068_);
v___f_2080_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2080_, 0, v_fst_2068_);
lean_inc_ref(v_binderType_1933_);
lean_inc(v_binderName_1932_);
v___x_2081_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1932_, v_binderType_1933_, v___f_2080_, v___y_1938_, v___y_1942_, v___y_1937_, v___y_1940_, v___y_1941_, v___y_1943_, v___y_1939_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2110_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2110_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2110_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_unsigned_to_nat(1u);
v___x_2088_ = lean_expr_lift_loose_bvars(v_pRaw_1984_, v___x_2086_, v___x_2087_);
lean_dec_ref(v_pRaw_1984_);
v___x_2089_ = l_Lean_mkOr(v___x_2088_, v_snd_2069_);
v___x_2090_ = l_Lean_mkForall(v_fst_2064_, v___x_2074_, v_fst_2068_, v___x_2089_);
lean_inc_ref(v_binderType_1933_);
v___x_2091_ = l_Lean_mkForall(v_binderName_1932_, v_binderInfo_1935_, v_binderType_1933_, v___x_2090_);
v___x_2092_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__10));
v___x_2093_ = lean_box(0);
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 1);
lean_ctor_set(v___x_2071_, 1, v___x_2093_);
lean_ctor_set(v___x_2071_, 0, v_a_2082_);
v___x_2095_ = v___x_2071_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2082_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 1);
lean_ctor_set(v___x_2066_, 1, v___x_2095_);
lean_ctor_set(v___x_2066_, 0, v_a_2079_);
v___x_2097_ = v___x_2066_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2079_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2098_ = l_Lean_mkConst(v___x_2092_, v___x_2097_);
v___x_2099_ = l_Lean_mkApp4(v___x_2098_, v_binderType_1933_, v_00_u03b2_2077_, v_p_2073_, v_q_2076_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2099_);
v___x_2101_ = v___x_2061_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2102_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2102_, 0, v___x_2091_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
lean_ctor_set_uint8(v___x_2102_, sizeof(void*)*2, v___y_1944_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2103_);
v___x_2105_ = v___x_2084_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_a_2079_);
lean_dec_ref(v_00_u03b2_2077_);
lean_dec_ref(v_q_2076_);
lean_dec_ref(v_p_2073_);
lean_del_object(v___x_2071_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_del_object(v___x_2066_);
lean_dec(v_fst_2064_);
lean_del_object(v___x_2061_);
lean_dec_ref(v_pRaw_1984_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2111_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2081_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2081_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v_00_u03b2_2077_);
lean_dec_ref(v_q_2076_);
lean_dec_ref(v_p_2073_);
lean_del_object(v___x_2071_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_del_object(v___x_2066_);
lean_dec(v_fst_2064_);
lean_del_object(v___x_2061_);
lean_dec_ref(v_pRaw_1984_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v_a_2119_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2078_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2078_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2058_);
lean_dec_ref(v_pRaw_1984_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
goto v___jp_1929_;
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref(v___x_1946_);
lean_dec_ref(v___x_1945_);
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec(v_binderName_1932_);
v___x_2130_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
}
v___jp_2132_:
{
uint8_t v___x_2140_; 
v___x_2140_ = l_Lean_Expr_isApp(v_body_1934_);
if (v___x_2140_ == 0)
{
v___y_1937_ = v___y_2135_;
v___y_1938_ = v___y_2133_;
v___y_1939_ = v___y_2139_;
v___y_1940_ = v___y_2136_;
v___y_1941_ = v___y_2137_;
v___y_1942_ = v___y_2134_;
v___y_1943_ = v___y_2138_;
v___y_1944_ = v___x_2140_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2141_ = l_Lean_Expr_getAppNumArgs(v_body_1934_);
v___x_2142_ = lean_unsigned_to_nat(2u);
v___x_2143_ = lean_nat_dec_eq(v___x_2141_, v___x_2142_);
lean_dec(v___x_2141_);
v___y_1937_ = v___y_2135_;
v___y_1938_ = v___y_2133_;
v___y_1939_ = v___y_2139_;
v___y_1940_ = v___y_2136_;
v___y_1941_ = v___y_2137_;
v___y_1942_ = v___y_2134_;
v___y_1943_ = v___y_2138_;
v___y_1944_ = v___x_2143_;
goto v___jp_1936_;
}
}
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
lean_dec_ref(v_e_1920_);
v___x_2426_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
return v___x_2427_;
}
v___jp_1929_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* v_e_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_Grind_simpForall(v_e_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* v_00_u03b1_2438_, lean_object* v_name_2439_, uint8_t v_bi_2440_, lean_object* v_type_2441_, lean_object* v_k_2442_, uint8_t v_kind_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_2439_, v_bi_2440_, v_type_2441_, v_k_2442_, v_kind_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_name_2454_, lean_object* v_bi_2455_, lean_object* v_type_2456_, lean_object* v_k_2457_, lean_object* v_kind_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
uint8_t v_bi_boxed_2467_; uint8_t v_kind_boxed_2468_; lean_object* v_res_2469_; 
v_bi_boxed_2467_ = lean_unbox(v_bi_2455_);
v_kind_boxed_2468_ = lean_unbox(v_kind_2458_);
v_res_2469_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(v_00_u03b1_2453_, v_name_2454_, v_bi_boxed_2467_, v_type_2456_, v_k_2457_, v_kind_boxed_2468_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* v_00_u03b1_2470_, lean_object* v_name_2471_, lean_object* v_type_2472_, lean_object* v_k_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_2471_, v_type_2472_, v_k_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_name_2484_, lean_object* v_type_2485_, lean_object* v_k_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(v_00_u03b1_2483_, v_name_2484_, v_type_2485_, v_k_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_));
v___x_2511_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_));
v___x_2512_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___boxed), 9, 0);
v___x_2513_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2510_, v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12____boxed(lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_();
return v_res_2515_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = lean_box(0);
v___x_2530_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__5));
v___x_2531_ = l_Lean_mkConst(v___x_2530_, v___x_2529_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* v_e_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2559_ = l_Lean_Expr_cleanupAnnotations(v_e_2547_);
v___x_2560_ = l_Lean_Expr_isApp(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_dec_ref(v___x_2559_);
goto v___jp_2553_;
}
else
{
lean_object* v_arg_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v_arg_2561_ = lean_ctor_get(v___x_2559_, 1);
lean_inc_ref(v_arg_2561_);
v___x_2562_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2559_);
v___x_2563_ = l_Lean_Expr_isApp(v___x_2562_);
if (v___x_2563_ == 0)
{
lean_dec_ref(v___x_2562_);
lean_dec_ref(v_arg_2561_);
goto v___jp_2553_;
}
else
{
lean_object* v_arg_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v_arg_2564_ = lean_ctor_get(v___x_2562_, 1);
lean_inc_ref(v_arg_2564_);
v___x_2565_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2562_);
v___x_2566_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2567_ = l_Lean_Expr_isConstOf(v___x_2565_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
lean_dec_ref(v_arg_2561_);
goto v___jp_2553_;
}
else
{
if (lean_obj_tag(v_arg_2561_) == 6)
{
lean_object* v_binderName_2568_; lean_object* v_body_2569_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2635_; uint8_t v___y_2636_; lean_object* v___y_2637_; uint8_t v___y_2638_; uint8_t v___y_2665_; uint8_t v___x_2694_; 
v_binderName_2568_ = lean_ctor_get(v_arg_2561_, 0);
lean_inc(v_binderName_2568_);
v_body_2569_ = lean_ctor_get(v_arg_2561_, 2);
lean_inc_ref(v_body_2569_);
lean_dec_ref_known(v_arg_2561_, 3);
v___x_2694_ = l_Lean_Expr_isApp(v_body_2569_);
if (v___x_2694_ == 0)
{
v___y_2665_ = v___x_2694_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2695_ = l_Lean_Expr_getAppNumArgs(v_body_2569_);
v___x_2696_ = lean_unsigned_to_nat(2u);
v___x_2697_ = lean_nat_dec_eq(v___x_2695_, v___x_2696_);
lean_dec(v___x_2695_);
v___y_2665_ = v___x_2697_;
goto v___jp_2664_;
}
v___jp_2570_:
{
uint8_t v___x_2575_; 
v___x_2575_ = l_Lean_Expr_hasLooseBVars(v_body_2569_);
if (v___x_2575_ == 0)
{
if (v___x_2567_ == 0)
{
lean_dec_ref(v_body_2569_);
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
goto v___jp_2556_;
}
else
{
lean_object* v___x_2576_; 
lean_inc_ref(v_arg_2564_);
v___x_2576_ = l_Lean_Meta_isProp(v_arg_2564_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2625_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2625_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2625_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_unbox(v_a_2577_);
lean_dec(v_a_2577_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_del_object(v___x_2579_);
v___x_2582_ = l_Lean_Expr_constLevels_x21(v___x_2565_);
lean_dec_ref(v___x_2565_);
v___x_2583_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__1));
lean_inc(v___x_2582_);
v___x_2584_ = l_Lean_mkConst(v___x_2583_, v___x_2582_);
lean_inc_ref(v_arg_2564_);
v___x_2585_ = l_Lean_Expr_app___override(v___x_2584_, v_arg_2564_);
v___x_2586_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2585_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2607_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2607_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2607_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
if (lean_obj_tag(v_a_2587_) == 1)
{
lean_object* v_val_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2606_; 
v_val_2591_ = lean_ctor_get(v_a_2587_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_a_2587_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2593_ = v_a_2587_;
v_isShared_2594_ = v_isSharedCheck_2606_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_val_2591_);
lean_dec(v_a_2587_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2606_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2595_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__3));
v___x_2596_ = l_Lean_mkConst(v___x_2595_, v___x_2582_);
lean_inc_ref(v_body_2569_);
v___x_2597_ = l_Lean_mkApp3(v___x_2596_, v_arg_2564_, v_val_2591_, v_body_2569_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2597_);
v___x_2599_ = v___x_2593_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2600_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2600_, 0, v_body_2569_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*2, v___x_2567_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2601_);
v___x_2603_ = v___x_2589_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
lean_dec(v___x_2582_);
lean_dec_ref(v_body_2569_);
lean_dec_ref(v_arg_2564_);
goto v___jp_2556_;
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v___x_2582_);
lean_dec_ref(v_body_2569_);
lean_dec_ref(v_arg_2564_);
v_a_2608_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2586_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2586_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_dec_ref(v___x_2565_);
lean_inc_ref(v_body_2569_);
lean_inc_ref(v_arg_2564_);
v___x_2616_ = l_Lean_mkAnd(v_arg_2564_, v_body_2569_);
v___x_2617_ = lean_obj_once(&l_Lean_Meta_Grind_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6);
v___x_2618_ = l_Lean_mkAppB(v___x_2617_, v_arg_2564_, v_body_2569_);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
v___x_2620_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2620_, 0, v___x_2616_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*2, v___x_2567_);
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2621_);
v___x_2623_ = v___x_2579_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref(v_body_2569_);
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
v_a_2626_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2576_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2576_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
else
{
lean_dec_ref(v_body_2569_);
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
goto v___jp_2556_;
}
}
v___jp_2634_:
{
if (v___y_2638_ == 0)
{
uint8_t v___x_2639_; 
v___x_2639_ = l_Lean_Expr_hasLooseBVars(v___y_2635_);
if (v___x_2639_ == 0)
{
if (v___y_2636_ == 0)
{
lean_dec_ref(v___y_2637_);
lean_dec_ref(v___y_2635_);
lean_dec(v_binderName_2568_);
v___y_2571_ = v_a_2548_;
v___y_2572_ = v_a_2549_;
v___y_2573_ = v_a_2550_;
v___y_2574_ = v_a_2551_;
goto v___jp_2570_;
}
else
{
uint8_t v___x_2640_; lean_object* v_p_2641_; lean_object* v___x_2642_; lean_object* v_expr_2643_; lean_object* v_u_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec_ref(v_body_2569_);
v___x_2640_ = 0;
lean_inc_ref_n(v_arg_2564_, 2);
v_p_2641_ = l_Lean_mkLambda(v_binderName_2568_, v___x_2640_, v_arg_2564_, v___y_2637_);
lean_inc_ref(v_p_2641_);
lean_inc_ref(v___x_2565_);
v___x_2642_ = l_Lean_mkAppB(v___x_2565_, v_arg_2564_, v_p_2641_);
lean_inc_ref(v___y_2635_);
v_expr_2643_ = l_Lean_mkAnd(v___x_2642_, v___y_2635_);
v_u_2644_ = l_Lean_Expr_constLevels_x21(v___x_2565_);
lean_dec_ref(v___x_2565_);
v___x_2645_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__8));
v___x_2646_ = l_Lean_mkConst(v___x_2645_, v_u_2644_);
v___x_2647_ = l_Lean_mkApp3(v___x_2646_, v_arg_2564_, v_p_2641_, v___y_2635_);
v___x_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2649_, 0, v_expr_2643_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*2, v___x_2567_);
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
else
{
lean_dec_ref(v___y_2637_);
lean_dec_ref(v___y_2635_);
lean_dec(v_binderName_2568_);
v___y_2571_ = v_a_2548_;
v___y_2572_ = v_a_2549_;
v___y_2573_ = v_a_2550_;
v___y_2574_ = v_a_2551_;
goto v___jp_2570_;
}
}
else
{
uint8_t v___x_2652_; lean_object* v_p_2653_; lean_object* v___x_2654_; lean_object* v_expr_2655_; lean_object* v_u_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec_ref(v_body_2569_);
v___x_2652_ = 0;
lean_inc_ref_n(v_arg_2564_, 2);
v_p_2653_ = l_Lean_mkLambda(v_binderName_2568_, v___x_2652_, v_arg_2564_, v___y_2635_);
lean_inc_ref(v_p_2653_);
lean_inc_ref(v___x_2565_);
v___x_2654_ = l_Lean_mkAppB(v___x_2565_, v_arg_2564_, v_p_2653_);
lean_inc_ref(v___y_2637_);
v_expr_2655_ = l_Lean_mkAnd(v___y_2637_, v___x_2654_);
v_u_2656_ = l_Lean_Expr_constLevels_x21(v___x_2565_);
lean_dec_ref(v___x_2565_);
v___x_2657_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__10));
v___x_2658_ = l_Lean_mkConst(v___x_2657_, v_u_2656_);
v___x_2659_ = l_Lean_mkApp3(v___x_2658_, v_arg_2564_, v_p_2653_, v___y_2637_);
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
v___x_2661_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2661_, 0, v_expr_2655_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*2, v___x_2567_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
return v___x_2663_;
}
}
v___jp_2664_:
{
if (v___y_2665_ == 0)
{
lean_dec(v_binderName_2568_);
v___y_2571_ = v_a_2548_;
v___y_2572_ = v_a_2549_;
v___y_2573_ = v_a_2550_;
v___y_2574_ = v_a_2551_;
goto v___jp_2570_;
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = l_Lean_Expr_appFn_x21(v_body_2569_);
v___x_2667_ = l_Lean_Expr_appFn_x21(v___x_2666_);
if (lean_obj_tag(v___x_2667_) == 4)
{
lean_object* v_declName_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_declName_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_declName_2668_);
lean_dec_ref_known(v___x_2667_, 2);
v___x_2669_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_2670_ = lean_name_eq(v_declName_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_2672_ = lean_name_eq(v_declName_2668_, v___x_2671_);
lean_dec(v_declName_2668_);
if (v___x_2672_ == 0)
{
lean_dec_ref(v___x_2666_);
lean_dec(v_binderName_2568_);
v___y_2571_ = v_a_2548_;
v___y_2572_ = v_a_2549_;
v___y_2573_ = v_a_2550_;
v___y_2574_ = v_a_2551_;
goto v___jp_2570_;
}
else
{
lean_object* v_b_2673_; lean_object* v_b_2674_; uint8_t v___x_2675_; 
v_b_2673_ = l_Lean_Expr_appArg_x21(v___x_2666_);
lean_dec_ref(v___x_2666_);
v_b_2674_ = l_Lean_Expr_appArg_x21(v_body_2569_);
v___x_2675_ = l_Lean_Expr_hasLooseBVars(v_b_2673_);
if (v___x_2675_ == 0)
{
v___y_2635_ = v_b_2674_;
v___y_2636_ = v___x_2672_;
v___y_2637_ = v_b_2673_;
v___y_2638_ = v___x_2672_;
goto v___jp_2634_;
}
else
{
v___y_2635_ = v_b_2674_;
v___y_2636_ = v___x_2672_;
v___y_2637_ = v_b_2673_;
v___y_2638_ = v___x_2670_;
goto v___jp_2634_;
}
}
}
else
{
lean_object* v_pRaw_2676_; lean_object* v_qRaw_2677_; uint8_t v___x_2678_; lean_object* v_p_2679_; lean_object* v_q_2680_; lean_object* v_u_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v_expr_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_dec(v_declName_2668_);
v_pRaw_2676_ = l_Lean_Expr_appArg_x21(v___x_2666_);
lean_dec_ref(v___x_2666_);
v_qRaw_2677_ = l_Lean_Expr_appArg_x21(v_body_2569_);
lean_dec_ref(v_body_2569_);
v___x_2678_ = 0;
lean_inc_ref_n(v_arg_2564_, 4);
lean_inc(v_binderName_2568_);
v_p_2679_ = l_Lean_mkLambda(v_binderName_2568_, v___x_2678_, v_arg_2564_, v_pRaw_2676_);
v_q_2680_ = l_Lean_mkLambda(v_binderName_2568_, v___x_2678_, v_arg_2564_, v_qRaw_2677_);
v_u_2681_ = l_Lean_Expr_constLevels_x21(v___x_2565_);
lean_inc_ref(v_p_2679_);
lean_inc_ref(v___x_2565_);
v___x_2682_ = l_Lean_mkAppB(v___x_2565_, v_arg_2564_, v_p_2679_);
lean_inc_ref(v_q_2680_);
v___x_2683_ = l_Lean_mkAppB(v___x_2565_, v_arg_2564_, v_q_2680_);
v_expr_2684_ = l_Lean_mkOr(v___x_2682_, v___x_2683_);
v___x_2685_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__12));
v___x_2686_ = l_Lean_mkConst(v___x_2685_, v_u_2681_);
v___x_2687_ = l_Lean_mkApp3(v___x_2686_, v_arg_2564_, v_p_2679_, v_q_2680_);
v___x_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
v___x_2689_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2689_, 0, v_expr_2684_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*2, v___x_2567_);
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
return v___x_2691_;
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec_ref(v___x_2667_);
lean_dec_ref(v___x_2666_);
lean_dec_ref(v_body_2569_);
lean_dec(v_binderName_2568_);
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
v___x_2692_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
}
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
lean_dec_ref(v_arg_2561_);
v___x_2698_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
}
}
}
v___jp_2553_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
v___jp_2556_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object* v_e_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* v_e_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2707_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* v_e_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_Meta_Grind_simpExists(v_e_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2746_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
v___x_2747_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2744_, v___x_2745_, v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11____boxed(lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_();
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* v_s_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_));
v___x_2755_ = 1;
v___x_2756_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2750_, v___x_2754_, v___x_2755_, v_a_2751_, v_a_2752_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2759_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2757_, v___x_2758_, v___x_2755_, v_a_2751_, v_a_2752_);
return v___x_2759_;
}
else
{
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object* v_s_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Meta_Grind_addForallSimproc(v_s_2760_, v_a_2761_, v_a_2762_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
return v_res_2764_;
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
