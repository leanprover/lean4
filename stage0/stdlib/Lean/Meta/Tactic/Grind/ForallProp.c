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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 213, 255, 45, 151, 209, 83, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value),LEAN_SCALAR_PTR_LITERAL(120, 104, 189, 185, 38, 81, 44, 71)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpForall"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(207, 161, 230, 164, 57, 132, 181, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpExists"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(220, 43, 168, 20, 165, 143, 80, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10____boxed(lean_object*);
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
lean_dec_ref(v___x_196_);
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
lean_dec_ref(v___x_60_);
lean_inc_ref(v_b_37_);
v___x_62_ = l_Lean_Meta_Grind_mkEqFalseProof(v_b_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
lean_dec_ref(v___x_62_);
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
lean_dec_ref(v___y_93_);
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
lean_dec_ref(v___x_96_);
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
lean_dec_ref(v___x_99_);
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
lean_dec_ref(v___x_103_);
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
lean_dec_ref(v___y_126_);
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
lean_dec_ref(v___x_129_);
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
lean_dec_ref(v___x_133_);
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
lean_dec_ref(v___y_155_);
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
lean_dec_ref(v___x_158_);
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
lean_dec_ref(v___x_165_);
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
lean_object* v_options_240_; uint8_t v_hasTrace_241_; 
v_options_240_ = lean_ctor_get(v___y_237_, 2);
v_hasTrace_241_ = lean_ctor_get_uint8(v_options_240_, sizeof(void*)*1);
if (v_hasTrace_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_cls_227_);
v___x_242_ = lean_box(v_hasTrace_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_244_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_245_ = l_Lean_Name_append(v___x_244_, v_cls_227_);
v___x_246_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_228_, v_options_240_, v___x_245_);
lean_dec(v___x_245_);
v___x_247_ = lean_box(v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0___boxed(lean_object* v_cls_249_, lean_object* v_____do__lift_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_249_, v_____do__lift_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v_____do__lift_250_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(lean_object* v_msgData_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v_env_270_; lean_object* v___x_271_; lean_object* v_mctx_272_; lean_object* v_lctx_273_; lean_object* v_options_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_269_ = lean_st_ref_get(v___y_267_);
v_env_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_env_270_);
lean_dec(v___x_269_);
v___x_271_ = lean_st_ref_get(v___y_265_);
v_mctx_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_mctx_272_);
lean_dec(v___x_271_);
v_lctx_273_ = lean_ctor_get(v___y_264_, 2);
v_options_274_ = lean_ctor_get(v___y_266_, 2);
lean_inc_ref(v_options_274_);
lean_inc_ref(v_lctx_273_);
v___x_275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_275_, 0, v_env_270_);
lean_ctor_set(v___x_275_, 1, v_mctx_272_);
lean_ctor_set(v___x_275_, 2, v_lctx_273_);
lean_ctor_set(v___x_275_, 3, v_options_274_);
v___x_276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v_msgData_263_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0___boxed(lean_object* v_msgData_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msgData_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_285_; double v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_float_of_nat(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* v_cls_290_, lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_ref_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_343_; 
v_ref_297_ = lean_ctor_get(v___y_294_, 5);
v___x_298_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msg_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_343_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_343_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_343_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v_traceState_304_; lean_object* v_env_305_; lean_object* v_nextMacroScope_306_; lean_object* v_ngen_307_; lean_object* v_auxDeclNGen_308_; lean_object* v_cache_309_; lean_object* v_messages_310_; lean_object* v_infoState_311_; lean_object* v_snapshotTasks_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_342_; 
v___x_303_ = lean_st_ref_take(v___y_295_);
v_traceState_304_ = lean_ctor_get(v___x_303_, 4);
v_env_305_ = lean_ctor_get(v___x_303_, 0);
v_nextMacroScope_306_ = lean_ctor_get(v___x_303_, 1);
v_ngen_307_ = lean_ctor_get(v___x_303_, 2);
v_auxDeclNGen_308_ = lean_ctor_get(v___x_303_, 3);
v_cache_309_ = lean_ctor_get(v___x_303_, 5);
v_messages_310_ = lean_ctor_get(v___x_303_, 6);
v_infoState_311_ = lean_ctor_get(v___x_303_, 7);
v_snapshotTasks_312_ = lean_ctor_get(v___x_303_, 8);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_342_ == 0)
{
v___x_314_ = v___x_303_;
v_isShared_315_ = v_isSharedCheck_342_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_snapshotTasks_312_);
lean_inc(v_infoState_311_);
lean_inc(v_messages_310_);
lean_inc(v_cache_309_);
lean_inc(v_traceState_304_);
lean_inc(v_auxDeclNGen_308_);
lean_inc(v_ngen_307_);
lean_inc(v_nextMacroScope_306_);
lean_inc(v_env_305_);
lean_dec(v___x_303_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_342_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint64_t v_tid_316_; lean_object* v_traces_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_341_; 
v_tid_316_ = lean_ctor_get_uint64(v_traceState_304_, sizeof(void*)*1);
v_traces_317_ = lean_ctor_get(v_traceState_304_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_traceState_304_);
if (v_isSharedCheck_341_ == 0)
{
v___x_319_ = v_traceState_304_;
v_isShared_320_ = v_isSharedCheck_341_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_traces_317_);
lean_dec(v_traceState_304_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_341_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; double v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_321_ = lean_box(0);
v___x_322_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0);
v___x_323_ = 0;
v___x_324_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1));
v___x_325_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_325_, 0, v_cls_290_);
lean_ctor_set(v___x_325_, 1, v___x_321_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
lean_ctor_set_float(v___x_325_, sizeof(void*)*3, v___x_322_);
lean_ctor_set_float(v___x_325_, sizeof(void*)*3 + 8, v___x_322_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*3 + 16, v___x_323_);
v___x_326_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2));
v___x_327_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v_a_299_);
lean_ctor_set(v___x_327_, 2, v___x_326_);
lean_inc(v_ref_297_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_ref_297_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_PersistentArray_push___redArg(v_traces_317_, v___x_328_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_329_);
v___x_331_ = v___x_319_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_329_);
lean_ctor_set_uint64(v_reuseFailAlloc_340_, sizeof(void*)*1, v_tid_316_);
v___x_331_ = v_reuseFailAlloc_340_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 4, v___x_331_);
v___x_333_ = v___x_314_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_env_305_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_nextMacroScope_306_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_ngen_307_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_auxDeclNGen_308_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_339_, 5, v_cache_309_);
lean_ctor_set(v_reuseFailAlloc_339_, 6, v_messages_310_);
lean_ctor_set(v_reuseFailAlloc_339_, 7, v_infoState_311_);
lean_ctor_set(v_reuseFailAlloc_339_, 8, v_snapshotTasks_312_);
v___x_333_ = v_reuseFailAlloc_339_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_334_ = lean_st_ref_set(v___y_295_, v___x_333_);
v___x_335_ = lean_box(0);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_335_);
v___x_337_ = v___x_301_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* v_cls_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_344_, v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_box(0);
v___x_358_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__1));
v___x_359_ = l_Lean_mkConst(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7(void){
_start:
{
lean_object* v_cls_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_cls_367_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_368_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_369_ = l_Lean_Name_append(v___x_368_, v_cls_367_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__8));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__10));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__12));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* v_e_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
if (lean_obj_tag(v_e_379_) == 7)
{
lean_object* v_binderName_391_; lean_object* v_binderType_392_; lean_object* v_body_393_; uint8_t v_binderInfo_394_; lean_object* v___y_396_; uint8_t v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v_inheritedTraceOptions_420_; lean_object* v_cls_421_; uint8_t v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___x_526_; lean_object* v_a_527_; uint8_t v___x_528_; 
v_binderName_391_ = lean_ctor_get(v_e_379_, 0);
v_binderType_392_ = lean_ctor_get(v_e_379_, 1);
v_body_393_ = lean_ctor_get(v_e_379_, 2);
v_binderInfo_394_ = lean_ctor_get_uint8(v_e_379_, sizeof(void*)*3 + 8);
v_inheritedTraceOptions_420_ = lean_ctor_get(v_a_388_, 13);
v_cls_421_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_526_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_421_, v_inheritedTraceOptions_420_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_unbox(v_a_527_);
lean_dec(v_a_527_);
if (v___x_528_ == 0)
{
v___y_485_ = v_a_380_;
v___y_486_ = v_a_381_;
v___y_487_ = v_a_382_;
v___y_488_ = v_a_383_;
v___y_489_ = v_a_384_;
v___y_490_ = v_a_385_;
v___y_491_ = v_a_386_;
v___y_492_ = v_a_387_;
v___y_493_ = v_a_388_;
v___y_494_ = v_a_389_;
goto v___jp_484_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_Grind_updateLastTag(v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec_ref(v___x_529_);
lean_inc_ref(v_e_379_);
v___x_530_ = l_Lean_MessageData_ofExpr(v_e_379_);
v___x_531_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_421_, v___x_530_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_dec_ref(v___x_531_);
v___y_485_ = v_a_380_;
v___y_486_ = v_a_381_;
v___y_487_ = v_a_382_;
v___y_488_ = v_a_383_;
v___y_489_ = v_a_384_;
v___y_490_ = v_a_385_;
v___y_491_ = v_a_386_;
v___y_492_ = v_a_387_;
v___y_493_ = v_a_388_;
v___y_494_ = v_a_389_;
goto v___jp_484_;
}
else
{
lean_dec_ref(v_e_379_);
return v___x_531_;
}
}
else
{
lean_dec_ref(v_e_379_);
return v___x_529_;
}
}
v___jp_395_:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Simp_Result_getProof(v___y_396_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v___x_407_);
v___x_409_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__2, &l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
lean_inc_ref(v___y_399_);
lean_inc_ref(v_binderType_392_);
v___x_410_ = l_Lean_mkApp5(v___x_409_, v_binderType_392_, v___y_398_, v___y_399_, v___y_400_, v_a_408_);
v___x_411_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_379_, v___y_399_, v___x_410_, v___y_397_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
return v___x_411_;
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec_ref(v_e_379_);
v_a_412_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_407_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_407_);
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
v___jp_422_:
{
lean_object* v___x_434_; 
lean_inc_ref(v_binderType_392_);
v___x_434_ = l_Lean_Meta_Grind_mkEqTrueProof(v_binderType_392_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_n(v_a_435_, 2);
lean_dec_ref(v___x_434_);
lean_inc_ref(v_binderType_392_);
v___x_436_ = l_Lean_Meta_mkOfEqTrueCore(v_binderType_392_, v_a_435_);
v___x_437_ = lean_expr_instantiate1(v_body_393_, v___x_436_);
lean_dec_ref(v___x_436_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
lean_inc(v___y_425_);
lean_inc(v___y_424_);
v___x_438_ = lean_grind_preprocess(v___x_437_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
v___x_440_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_379_, v___y_424_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_expr_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
v_expr_442_ = lean_ctor_get(v_a_439_, 0);
lean_inc_ref_n(v_expr_442_, 2);
v___x_443_ = lean_box(0);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
lean_inc(v___y_425_);
lean_inc(v___y_424_);
v___x_444_ = lean_grind_internalize(v_expr_442_, v_a_441_, v___x_443_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_options_445_; lean_object* v_inheritedTraceOptions_446_; uint8_t v_hasTrace_447_; lean_object* v___x_448_; 
lean_dec_ref(v___x_444_);
v_options_445_ = lean_ctor_get(v___y_432_, 2);
v_inheritedTraceOptions_446_ = lean_ctor_get(v___y_432_, 13);
v_hasTrace_447_ = lean_ctor_get_uint8(v_options_445_, sizeof(void*)*1);
lean_inc_ref(v_body_393_);
lean_inc_ref(v_binderType_392_);
lean_inc(v_binderName_391_);
v___x_448_ = l_Lean_mkLambda(v_binderName_391_, v_binderInfo_394_, v_binderType_392_, v_body_393_);
if (v_hasTrace_447_ == 0)
{
v___y_396_ = v_a_439_;
v___y_397_ = v___y_423_;
v___y_398_ = v___x_448_;
v___y_399_ = v_expr_442_;
v___y_400_ = v_a_435_;
v___y_401_ = v___y_424_;
v___y_402_ = v___y_426_;
v___y_403_ = v___y_430_;
v___y_404_ = v___y_431_;
v___y_405_ = v___y_432_;
v___y_406_ = v___y_433_;
goto v___jp_395_;
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__7, &l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
v___x_450_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_446_, v_options_445_, v___x_449_);
if (v___x_450_ == 0)
{
v___y_396_ = v_a_439_;
v___y_397_ = v___y_423_;
v___y_398_ = v___x_448_;
v___y_399_ = v_expr_442_;
v___y_400_ = v_a_435_;
v___y_401_ = v___y_424_;
v___y_402_ = v___y_426_;
v___y_403_ = v___y_430_;
v___y_404_ = v___y_431_;
v___y_405_ = v___y_432_;
v___y_406_ = v___y_433_;
goto v___jp_395_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_updateLastTag(v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec_ref(v___x_451_);
v___x_452_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__9, &l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
lean_inc_ref(v_expr_442_);
v___x_453_ = l_Lean_MessageData_ofExpr(v_expr_442_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__11, &l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
lean_inc_ref(v_e_379_);
v___x_457_ = l_Lean_indentExpr(v_e_379_);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_421_, v___x_458_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_dec_ref(v___x_459_);
v___y_396_ = v_a_439_;
v___y_397_ = v___y_423_;
v___y_398_ = v___x_448_;
v___y_399_ = v_expr_442_;
v___y_400_ = v_a_435_;
v___y_401_ = v___y_424_;
v___y_402_ = v___y_426_;
v___y_403_ = v___y_430_;
v___y_404_ = v___y_431_;
v___y_405_ = v___y_432_;
v___y_406_ = v___y_433_;
goto v___jp_395_;
}
else
{
lean_dec_ref(v___x_448_);
lean_dec_ref(v_expr_442_);
lean_dec(v_a_439_);
lean_dec(v_a_435_);
lean_dec_ref(v_e_379_);
return v___x_459_;
}
}
else
{
lean_dec_ref(v___x_448_);
lean_dec_ref(v_expr_442_);
lean_dec(v_a_439_);
lean_dec(v_a_435_);
lean_dec_ref(v_e_379_);
return v___x_451_;
}
}
}
}
else
{
lean_dec_ref(v_expr_442_);
lean_dec(v_a_439_);
lean_dec(v_a_435_);
lean_dec_ref(v_e_379_);
return v___x_444_;
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_439_);
lean_dec(v_a_435_);
lean_dec_ref(v_e_379_);
v_a_460_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_440_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_440_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_a_435_);
lean_dec_ref(v_e_379_);
v_a_468_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_438_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_438_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v_e_379_);
v_a_476_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_434_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_434_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
v___jp_484_:
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Expr_hasLooseBVars(v_body_393_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_inc_ref(v_body_393_);
lean_inc_ref(v_binderType_392_);
v___x_496_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_379_, v_binderType_392_, v_body_393_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; 
lean_inc_ref(v_binderType_392_);
v___x_497_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_392_, v___y_485_, v___y_489_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_517_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_517_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_517_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___x_502_; 
v___x_502_ = lean_unbox(v_a_498_);
lean_dec(v_a_498_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec_ref(v_e_379_);
v___x_503_ = lean_box(0);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_503_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_inheritedTraceOptions_507_; lean_object* v___x_508_; lean_object* v_a_509_; uint8_t v___x_510_; uint8_t v___x_511_; 
lean_del_object(v___x_500_);
v_inheritedTraceOptions_507_ = lean_ctor_get(v___y_493_, 13);
v___x_508_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_421_, v_inheritedTraceOptions_507_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = 0;
v___x_511_ = lean_unbox(v_a_509_);
lean_dec(v_a_509_);
if (v___x_511_ == 0)
{
v___y_423_ = v___x_510_;
v___y_424_ = v___y_485_;
v___y_425_ = v___y_486_;
v___y_426_ = v___y_487_;
v___y_427_ = v___y_488_;
v___y_428_ = v___y_489_;
v___y_429_ = v___y_490_;
v___y_430_ = v___y_491_;
v___y_431_ = v___y_492_;
v___y_432_ = v___y_493_;
v___y_433_ = v___y_494_;
goto v___jp_422_;
}
else
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Meta_Grind_updateLastTag(v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec_ref(v___x_512_);
v___x_513_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__13, &l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13);
lean_inc_ref(v_e_379_);
v___x_514_ = l_Lean_MessageData_ofExpr(v_e_379_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_421_, v___x_515_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_dec_ref(v___x_516_);
v___y_423_ = v___x_510_;
v___y_424_ = v___y_485_;
v___y_425_ = v___y_486_;
v___y_426_ = v___y_487_;
v___y_427_ = v___y_488_;
v___y_428_ = v___y_489_;
v___y_429_ = v___y_490_;
v___y_430_ = v___y_491_;
v___y_431_ = v___y_492_;
v___y_432_ = v___y_493_;
v___y_433_ = v___y_494_;
goto v___jp_422_;
}
else
{
lean_dec_ref(v_e_379_);
return v___x_516_;
}
}
else
{
lean_dec_ref(v_e_379_);
return v___x_512_;
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_e_379_);
v_a_518_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_497_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_497_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec_ref(v_e_379_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* v_e_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_Grind_propagateForallPropUp(v_e_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec(v_a_535_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* v_cls_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_547_, v_msg_548_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* v_cls_561_, lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(v_cls_561_, v_msg_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec(v___y_563_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object* v_proof_578_){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = l_Lean_Expr_cleanupAnnotations(v_proof_578_);
v___x_580_ = l_Lean_Expr_isApp(v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v___x_579_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
lean_object* v_arg_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_arg_582_ = lean_ctor_get(v___x_579_, 1);
lean_inc_ref(v_arg_582_);
v___x_583_ = l_Lean_Expr_appFnCleanup___redArg(v___x_579_);
v___x_584_ = l_Lean_Expr_isApp(v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_dec_ref(v___x_583_);
lean_dec_ref(v_arg_582_);
v___x_585_ = lean_box(0);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = l_Lean_Expr_appFnCleanup___redArg(v___x_583_);
v___x_587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1));
v___x_588_ = l_Lean_Expr_isConstOf(v___x_586_, v___x_587_);
lean_dec_ref(v___x_586_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_dec_ref(v_arg_582_);
v___x_589_ = lean_box(0);
return v___x_589_;
}
else
{
if (lean_obj_tag(v_arg_582_) == 1)
{
lean_object* v_fvarId_590_; lean_object* v___x_591_; 
v_fvarId_590_ = lean_ctor_get(v_arg_582_, 0);
lean_inc(v_fvarId_590_);
lean_dec_ref(v_arg_582_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v_fvarId_590_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; 
lean_dec_ref(v_arg_582_);
v___x_592_ = lean_box(0);
return v___x_592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* v_origin_595_, lean_object* v_proof_596_, lean_object* v_kind_597_, lean_object* v_prios_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
v___x_605_ = 0;
v___x_606_ = 1;
v___x_607_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v_origin_595_, v___x_604_, v_proof_596_, v_kind_597_, v_prios_598_, v___x_605_, v___x_605_, v___x_606_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
if (lean_obj_tag(v___x_607_) == 0)
{
return v___x_607_;
}
else
{
lean_object* v_a_608_; uint8_t v___y_610_; uint8_t v___x_620_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
v___x_620_ = l_Lean_Exception_isInterrupt(v_a_608_);
if (v___x_620_ == 0)
{
uint8_t v___x_621_; 
v___x_621_ = l_Lean_Exception_isRuntime(v_a_608_);
v___y_610_ = v___x_621_;
goto v___jp_609_;
}
else
{
lean_dec(v_a_608_);
v___y_610_ = v___x_620_;
goto v___jp_609_;
}
v___jp_609_:
{
if (v___y_610_ == 0)
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_618_; 
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v___x_607_, 0);
lean_dec(v_unused_619_);
v___x_612_ = v___x_607_;
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
else
{
lean_dec(v___x_607_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_box(0);
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 0);
lean_ctor_set(v___x_612_, 0, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* v_origin_622_, lean_object* v_proof_623_, lean_object* v_kind_624_, lean_object* v_prios_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_origin_622_, v_proof_623_, v_kind_624_, v_prios_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_631_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
if (lean_obj_tag(v_x_633_) == 0)
{
uint8_t v___x_634_; 
v___x_634_ = 1;
return v___x_634_;
}
else
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
else
{
if (lean_obj_tag(v_x_633_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v_head_639_; lean_object* v_tail_640_; uint8_t v___x_641_; 
v_head_637_ = lean_ctor_get(v_x_632_, 0);
v_tail_638_ = lean_ctor_get(v_x_632_, 1);
v_head_639_ = lean_ctor_get(v_x_633_, 0);
v_tail_640_ = lean_ctor_get(v_x_633_, 1);
v___x_641_ = lean_expr_eqv(v_head_637_, v_head_639_);
if (v___x_641_ == 0)
{
return v___x_641_;
}
else
{
v_x_632_ = v_tail_638_;
v_x_633_ = v_tail_640_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_x_643_, v_x_644_);
lean_dec(v_x_644_);
lean_dec(v_x_643_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* v_thm_x27_647_, lean_object* v_as_648_, size_t v_i_649_, size_t v_stop_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_eq(v_i_649_, v_stop_650_);
if (v___x_651_ == 0)
{
lean_object* v_patterns_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_patterns_652_ = lean_ctor_get(v_thm_x27_647_, 3);
v___x_653_ = lean_array_uget_borrowed(v_as_648_, v_i_649_);
v___x_654_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_patterns_652_, v___x_653_);
if (v___x_654_ == 0)
{
size_t v___x_655_; size_t v___x_656_; 
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_add(v_i_649_, v___x_655_);
v_i_649_ = v___x_656_;
goto _start;
}
else
{
return v___x_654_;
}
}
else
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* v_thm_x27_659_, lean_object* v_as_660_, lean_object* v_i_661_, lean_object* v_stop_662_){
_start:
{
size_t v_i_boxed_663_; size_t v_stop_boxed_664_; uint8_t v_res_665_; lean_object* v_r_666_; 
v_i_boxed_663_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_stop_boxed_664_ = lean_unbox_usize(v_stop_662_);
lean_dec(v_stop_662_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_659_, v_as_660_, v_i_boxed_663_, v_stop_boxed_664_);
lean_dec_ref(v_as_660_);
lean_dec_ref(v_thm_x27_659_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object* v_patternsFoundSoFar_667_, lean_object* v_thm_x27_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_array_get_size(v_patternsFoundSoFar_667_);
v___x_671_ = lean_nat_dec_lt(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 1;
return v___x_672_;
}
else
{
if (v___x_671_ == 0)
{
return v___x_671_;
}
else
{
size_t v___x_673_; size_t v___x_674_; uint8_t v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_670_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_668_, v_patternsFoundSoFar_667_, v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
return v___x_671_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = 0;
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object* v_patternsFoundSoFar_677_, lean_object* v_thm_x27_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_677_, v_thm_x27_678_);
lean_dec_ref(v_thm_x27_678_);
lean_dec_ref(v_patternsFoundSoFar_677_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t v_a_681_, lean_object* v_as_682_, size_t v_i_683_, size_t v_stop_684_){
_start:
{
uint8_t v___x_685_; 
v___x_685_ = lean_usize_dec_eq(v_i_683_, v_stop_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_array_uget_borrowed(v_as_682_, v_i_683_);
v___x_687_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_686_, v_a_681_);
if (v___x_687_ == 0)
{
size_t v___x_688_; size_t v___x_689_; 
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_add(v_i_683_, v___x_688_);
v_i_683_ = v___x_689_;
goto _start;
}
else
{
return v___x_687_;
}
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object* v_a_692_, lean_object* v_as_693_, lean_object* v_i_694_, lean_object* v_stop_695_){
_start:
{
uint64_t v_a_4179__boxed_696_; size_t v_i_boxed_697_; size_t v_stop_boxed_698_; uint8_t v_res_699_; lean_object* v_r_700_; 
v_a_4179__boxed_696_ = lean_unbox_uint64(v_a_692_);
lean_dec_ref(v_a_692_);
v_i_boxed_697_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_stop_boxed_698_ = lean_unbox_usize(v_stop_695_);
lean_dec(v_stop_695_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v_a_4179__boxed_696_, v_as_693_, v_i_boxed_697_, v_stop_boxed_698_);
lean_dec_ref(v_as_693_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* v_proof_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_703_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_766_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_766_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_766_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_766_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
if (lean_obj_tag(v_a_713_) == 1)
{
lean_object* v_val_717_; lean_object* v___x_718_; 
lean_del_object(v___x_715_);
v_val_717_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v_a_713_);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
v___x_718_ = lean_infer_type(v_proof_701_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = l_Lean_Meta_Grind_getAnchor(v_a_719_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_744_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_744_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_744_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_744_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_array_get_size(v_val_717_);
v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_dec(v_a_721_);
lean_dec(v_val_717_);
v___x_728_ = lean_box(v___x_727_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_728_);
v___x_730_ = v___x_723_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
if (v___x_727_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_734_; 
lean_dec(v_a_721_);
lean_dec(v_val_717_);
v___x_732_ = lean_box(v___x_727_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_732_);
v___x_734_ = v___x_723_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
else
{
size_t v___x_736_; size_t v___x_737_; uint64_t v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_736_ = ((size_t)0ULL);
v___x_737_ = lean_usize_of_nat(v___x_726_);
v___x_738_ = lean_unbox_uint64(v_a_721_);
lean_dec(v_a_721_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v___x_738_, v_val_717_, v___x_736_, v___x_737_);
lean_dec(v_val_717_);
v___x_740_ = lean_box(v___x_739_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_740_);
v___x_742_ = v___x_723_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_val_717_);
v_a_745_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_720_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_720_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_val_717_);
v_a_753_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_718_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_718_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
lean_dec(v_a_713_);
lean_dec_ref(v_proof_701_);
v___x_761_ = 1;
v___x_762_ = lean_box(v___x_761_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_762_);
v___x_764_ = v___x_715_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_proof_701_);
v_a_767_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_712_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_712_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* v_proof_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* v_a_787_, lean_object* v_as_788_, size_t v_sz_789_, size_t v_i_790_, lean_object* v_b_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_a_804_; uint8_t v___x_808_; 
v___x_808_ = lean_usize_dec_lt(v_i_790_, v_sz_789_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_a_787_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_b_791_);
return v___x_809_;
}
else
{
lean_object* v_a_810_; uint8_t v___x_811_; 
v_a_810_ = lean_array_uget_borrowed(v_as_788_, v_i_790_);
v___x_811_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_b_791_, v_a_810_);
if (v___x_811_ == 0)
{
v_a_804_ = v_b_791_;
goto v___jp_803_;
}
else
{
lean_object* v___x_812_; 
lean_inc(v_a_787_);
lean_inc(v_a_810_);
v___x_812_ = l_Lean_Meta_Grind_activateTheorem(v_a_810_, v_a_787_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_patterns_813_; lean_object* v___x_814_; 
lean_dec_ref(v___x_812_);
v_patterns_813_ = lean_ctor_get(v_a_810_, 3);
lean_inc(v_patterns_813_);
v___x_814_ = lean_array_push(v_b_791_, v_patterns_813_);
v_a_804_ = v___x_814_;
goto v___jp_803_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v_b_791_);
lean_dec(v_a_787_);
v_a_815_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_812_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_812_);
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
v___jp_803_:
{
size_t v___x_805_; size_t v___x_806_; 
v___x_805_ = ((size_t)1ULL);
v___x_806_ = lean_usize_add(v_i_790_, v___x_805_);
v_i_790_ = v___x_806_;
v_b_791_ = v_a_804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* v_a_823_, lean_object* v_as_824_, lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
size_t v_sz_boxed_839_; size_t v_i_boxed_840_; lean_object* v_res_841_; 
v_sz_boxed_839_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_840_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_823_, v_as_824_, v_sz_boxed_839_, v_i_boxed_840_, v_b_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v_as_824_);
return v_res_841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* v_e_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; uint8_t v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; uint8_t v___y_949_; lean_object* v_patternsFoundSoFar_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___x_975_; 
lean_inc_ref(v_e_848_);
v___x_975_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_origin_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___x_1076_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_n(v_a_976_, 2);
lean_dec_ref(v___x_975_);
v___x_1076_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(v_a_976_);
if (lean_obj_tag(v___x_1076_) == 1)
{
lean_object* v_val_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_val_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_val_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_val_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
v_origin_978_ = v___x_1082_;
v___y_979_ = v_a_849_;
v___y_980_ = v_a_850_;
v___y_981_ = v_a_851_;
v___y_982_ = v_a_852_;
v___y_983_ = v_a_853_;
v___y_984_ = v_a_854_;
v___y_985_ = v_a_855_;
v___y_986_ = v_a_856_;
v___y_987_ = v_a_857_;
v___y_988_ = v_a_858_;
goto v___jp_977_;
}
}
}
else
{
lean_object* v___x_1085_; lean_object* v_toGoalState_1086_; lean_object* v_ematch_1087_; lean_object* v_mvarId_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v___x_1076_);
v___x_1085_ = lean_st_ref_take(v_a_849_);
v_toGoalState_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_toGoalState_1086_);
v_ematch_1087_ = lean_ctor_get(v_toGoalState_1086_, 12);
lean_inc_ref(v_ematch_1087_);
v_mvarId_1088_ = lean_ctor_get(v___x_1085_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1085_, 0);
lean_dec(v_unused_1145_);
v___x_1090_ = v___x_1085_;
v_isShared_1091_ = v_isSharedCheck_1144_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_mvarId_1088_);
lean_dec(v___x_1085_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1144_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_nextDeclIdx_1092_; lean_object* v_enodeMap_1093_; lean_object* v_exprs_1094_; lean_object* v_parents_1095_; lean_object* v_congrTable_1096_; lean_object* v_appMap_1097_; lean_object* v_indicesFound_1098_; lean_object* v_newFacts_1099_; uint8_t v_inconsistent_1100_; lean_object* v_nextIdx_1101_; lean_object* v_newRawFacts_1102_; lean_object* v_facts_1103_; lean_object* v_extThms_1104_; lean_object* v_inj_1105_; lean_object* v_split_1106_; lean_object* v_clean_1107_; lean_object* v_sstates_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1142_; 
v_nextDeclIdx_1092_ = lean_ctor_get(v_toGoalState_1086_, 0);
v_enodeMap_1093_ = lean_ctor_get(v_toGoalState_1086_, 1);
v_exprs_1094_ = lean_ctor_get(v_toGoalState_1086_, 2);
v_parents_1095_ = lean_ctor_get(v_toGoalState_1086_, 3);
v_congrTable_1096_ = lean_ctor_get(v_toGoalState_1086_, 4);
v_appMap_1097_ = lean_ctor_get(v_toGoalState_1086_, 5);
v_indicesFound_1098_ = lean_ctor_get(v_toGoalState_1086_, 6);
v_newFacts_1099_ = lean_ctor_get(v_toGoalState_1086_, 7);
v_inconsistent_1100_ = lean_ctor_get_uint8(v_toGoalState_1086_, sizeof(void*)*17);
v_nextIdx_1101_ = lean_ctor_get(v_toGoalState_1086_, 8);
v_newRawFacts_1102_ = lean_ctor_get(v_toGoalState_1086_, 9);
v_facts_1103_ = lean_ctor_get(v_toGoalState_1086_, 10);
v_extThms_1104_ = lean_ctor_get(v_toGoalState_1086_, 11);
v_inj_1105_ = lean_ctor_get(v_toGoalState_1086_, 13);
v_split_1106_ = lean_ctor_get(v_toGoalState_1086_, 14);
v_clean_1107_ = lean_ctor_get(v_toGoalState_1086_, 15);
v_sstates_1108_ = lean_ctor_get(v_toGoalState_1086_, 16);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_toGoalState_1086_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v_toGoalState_1086_, 12);
lean_dec(v_unused_1143_);
v___x_1110_ = v_toGoalState_1086_;
v_isShared_1111_ = v_isSharedCheck_1142_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_sstates_1108_);
lean_inc(v_clean_1107_);
lean_inc(v_split_1106_);
lean_inc(v_inj_1105_);
lean_inc(v_extThms_1104_);
lean_inc(v_facts_1103_);
lean_inc(v_newRawFacts_1102_);
lean_inc(v_nextIdx_1101_);
lean_inc(v_newFacts_1099_);
lean_inc(v_indicesFound_1098_);
lean_inc(v_appMap_1097_);
lean_inc(v_congrTable_1096_);
lean_inc(v_parents_1095_);
lean_inc(v_exprs_1094_);
lean_inc(v_enodeMap_1093_);
lean_inc(v_nextDeclIdx_1092_);
lean_dec(v_toGoalState_1086_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1142_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_thmMap_1112_; lean_object* v_gmt_1113_; lean_object* v_thms_1114_; lean_object* v_newThms_1115_; lean_object* v_numInstances_1116_; lean_object* v_numDelayedInstances_1117_; lean_object* v_num_1118_; lean_object* v_preInstances_1119_; lean_object* v_nextThmIdx_1120_; lean_object* v_matchEqNames_1121_; lean_object* v_delayedThmInsts_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1141_; 
v_thmMap_1112_ = lean_ctor_get(v_ematch_1087_, 0);
v_gmt_1113_ = lean_ctor_get(v_ematch_1087_, 1);
v_thms_1114_ = lean_ctor_get(v_ematch_1087_, 2);
v_newThms_1115_ = lean_ctor_get(v_ematch_1087_, 3);
v_numInstances_1116_ = lean_ctor_get(v_ematch_1087_, 4);
v_numDelayedInstances_1117_ = lean_ctor_get(v_ematch_1087_, 5);
v_num_1118_ = lean_ctor_get(v_ematch_1087_, 6);
v_preInstances_1119_ = lean_ctor_get(v_ematch_1087_, 7);
v_nextThmIdx_1120_ = lean_ctor_get(v_ematch_1087_, 8);
v_matchEqNames_1121_ = lean_ctor_get(v_ematch_1087_, 9);
v_delayedThmInsts_1122_ = lean_ctor_get(v_ematch_1087_, 10);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_ematch_1087_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1124_ = v_ematch_1087_;
v_isShared_1125_ = v_isSharedCheck_1141_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_delayedThmInsts_1122_);
lean_inc(v_matchEqNames_1121_);
lean_inc(v_nextThmIdx_1120_);
lean_inc(v_preInstances_1119_);
lean_inc(v_num_1118_);
lean_inc(v_numDelayedInstances_1117_);
lean_inc(v_numInstances_1116_);
lean_inc(v_newThms_1115_);
lean_inc(v_thms_1114_);
lean_inc(v_gmt_1113_);
lean_inc(v_thmMap_1112_);
lean_dec(v_ematch_1087_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1141_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v_nextThmIdx_1120_, v___x_1126_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 8, v___x_1127_);
v___x_1129_ = v___x_1124_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_thmMap_1112_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_gmt_1113_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_thms_1114_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_newThms_1115_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_numInstances_1116_);
lean_ctor_set(v_reuseFailAlloc_1140_, 5, v_numDelayedInstances_1117_);
lean_ctor_set(v_reuseFailAlloc_1140_, 6, v_num_1118_);
lean_ctor_set(v_reuseFailAlloc_1140_, 7, v_preInstances_1119_);
lean_ctor_set(v_reuseFailAlloc_1140_, 8, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1140_, 9, v_matchEqNames_1121_);
lean_ctor_set(v_reuseFailAlloc_1140_, 10, v_delayedThmInsts_1122_);
v___x_1129_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 12, v___x_1129_);
v___x_1131_ = v___x_1110_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_nextDeclIdx_1092_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_enodeMap_1093_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_exprs_1094_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_parents_1095_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_congrTable_1096_);
lean_ctor_set(v_reuseFailAlloc_1139_, 5, v_appMap_1097_);
lean_ctor_set(v_reuseFailAlloc_1139_, 6, v_indicesFound_1098_);
lean_ctor_set(v_reuseFailAlloc_1139_, 7, v_newFacts_1099_);
lean_ctor_set(v_reuseFailAlloc_1139_, 8, v_nextIdx_1101_);
lean_ctor_set(v_reuseFailAlloc_1139_, 9, v_newRawFacts_1102_);
lean_ctor_set(v_reuseFailAlloc_1139_, 10, v_facts_1103_);
lean_ctor_set(v_reuseFailAlloc_1139_, 11, v_extThms_1104_);
lean_ctor_set(v_reuseFailAlloc_1139_, 12, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1139_, 13, v_inj_1105_);
lean_ctor_set(v_reuseFailAlloc_1139_, 14, v_split_1106_);
lean_ctor_set(v_reuseFailAlloc_1139_, 15, v_clean_1107_);
lean_ctor_set(v_reuseFailAlloc_1139_, 16, v_sstates_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1139_, sizeof(void*)*17, v_inconsistent_1100_);
v___x_1131_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1131_);
v___x_1133_ = v___x_1090_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_mvarId_1088_);
v___x_1133_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = lean_st_ref_set(v_a_849_, v___x_1133_);
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3));
v___x_1136_ = lean_name_append_index_after(v___x_1135_, v_nextThmIdx_1120_);
v___x_1137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v_origin_978_ = v___x_1137_;
v___y_979_ = v_a_849_;
v___y_980_ = v_a_850_;
v___y_981_ = v_a_851_;
v___y_982_ = v_a_852_;
v___y_983_ = v_a_853_;
v___y_984_ = v_a_854_;
v___y_985_ = v_a_855_;
v___y_986_ = v_a_856_;
v___y_987_ = v_a_857_;
v___y_988_ = v_a_858_;
goto v___jp_977_;
}
}
}
}
}
}
}
v___jp_977_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_inc_ref(v_e_848_);
v___x_989_ = l_Lean_Meta_mkOfEqTrueCore(v_e_848_, v_a_976_);
lean_inc_ref(v___x_989_);
v___x_990_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v___x_989_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1067_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1067_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1067_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
uint8_t v___x_995_; 
v___x_995_ = lean_unbox(v_a_991_);
lean_dec(v_a_991_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
v___x_996_ = lean_box(0);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_996_);
v___x_998_ = v___x_993_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_del_object(v___x_993_);
v___x_1000_ = lean_st_ref_get(v___y_979_);
v___x_1001_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_848_, v___y_979_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = l_Lean_Meta_Grind_getSymbolPriorities___redArg(v___y_981_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_n(v_a_1004_, 2);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_unsigned_to_nat(1000u);
v___x_1006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
v___x_1007_ = 0;
lean_inc_ref(v___x_989_);
lean_inc_ref(v_origin_978_);
v___x_1008_ = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(v_origin_978_, v___x_1006_, v___x_989_, v___x_1005_, v_a_1004_, v___x_1007_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; size_t v_sz_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v_sz_1010_ = lean_array_size(v_a_1009_);
v___x_1011_ = ((size_t)0ULL);
lean_inc(v_a_1002_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_1002_, v_a_1009_, v_sz_1010_, v___x_1011_, v___x_1006_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v_a_1009_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_box(6);
lean_inc(v_a_1004_);
lean_inc_ref(v___x_989_);
lean_inc_ref(v_origin_978_);
v___x_1015_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_origin_978_, v___x_989_, v___x_1014_, v_a_1004_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_toGoalState_1016_; lean_object* v_ematch_1017_; lean_object* v_newThms_1018_; lean_object* v_a_1019_; 
v_toGoalState_1016_ = lean_ctor_get(v___x_1000_, 0);
lean_inc_ref(v_toGoalState_1016_);
lean_dec(v___x_1000_);
v_ematch_1017_ = lean_ctor_get(v_toGoalState_1016_, 12);
lean_inc_ref(v_ematch_1017_);
lean_dec_ref(v_toGoalState_1016_);
v_newThms_1018_ = lean_ctor_get(v_ematch_1017_, 3);
lean_inc_ref(v_newThms_1018_);
lean_dec_ref(v_ematch_1017_);
v_a_1019_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1015_);
if (lean_obj_tag(v_a_1019_) == 1)
{
lean_object* v_size_1020_; lean_object* v_val_1021_; uint8_t v___x_1022_; 
v_size_1020_ = lean_ctor_get(v_newThms_1018_, 2);
lean_inc(v_size_1020_);
lean_dec_ref(v_newThms_1018_);
v_val_1021_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_val_1021_);
lean_dec_ref(v_a_1019_);
v___x_1022_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_a_1013_, v_val_1021_);
if (v___x_1022_ == 0)
{
lean_dec(v_val_1021_);
v___y_944_ = v_size_1020_;
v___y_945_ = v_a_1002_;
v___y_946_ = v___x_989_;
v___y_947_ = v_a_1004_;
v___y_948_ = v_origin_978_;
v___y_949_ = v___x_1007_;
v_patternsFoundSoFar_950_ = v_a_1013_;
v___y_951_ = v___y_979_;
v___y_952_ = v___y_980_;
v___y_953_ = v___y_981_;
v___y_954_ = v___y_982_;
v___y_955_ = v___y_983_;
v___y_956_ = v___y_984_;
v___y_957_ = v___y_985_;
v___y_958_ = v___y_986_;
v___y_959_ = v___y_987_;
v___y_960_ = v___y_988_;
goto v___jp_943_;
}
else
{
lean_object* v___x_1023_; 
lean_inc(v_a_1002_);
lean_inc(v_val_1021_);
v___x_1023_ = l_Lean_Meta_Grind_activateTheorem(v_val_1021_, v_a_1002_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_patterns_1024_; lean_object* v___x_1025_; 
lean_dec_ref(v___x_1023_);
v_patterns_1024_ = lean_ctor_get(v_val_1021_, 3);
lean_inc(v_patterns_1024_);
lean_dec(v_val_1021_);
v___x_1025_ = lean_array_push(v_a_1013_, v_patterns_1024_);
v___y_944_ = v_size_1020_;
v___y_945_ = v_a_1002_;
v___y_946_ = v___x_989_;
v___y_947_ = v_a_1004_;
v___y_948_ = v_origin_978_;
v___y_949_ = v___x_1007_;
v_patternsFoundSoFar_950_ = v___x_1025_;
v___y_951_ = v___y_979_;
v___y_952_ = v___y_980_;
v___y_953_ = v___y_981_;
v___y_954_ = v___y_982_;
v___y_955_ = v___y_983_;
v___y_956_ = v___y_984_;
v___y_957_ = v___y_985_;
v___y_958_ = v___y_986_;
v___y_959_ = v___y_987_;
v___y_960_ = v___y_988_;
goto v___jp_943_;
}
else
{
lean_dec(v_val_1021_);
lean_dec(v_size_1020_);
lean_dec(v_a_1013_);
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
return v___x_1023_;
}
}
}
else
{
lean_object* v_size_1026_; 
lean_dec(v_a_1019_);
v_size_1026_ = lean_ctor_get(v_newThms_1018_, 2);
lean_inc(v_size_1026_);
lean_dec_ref(v_newThms_1018_);
v___y_944_ = v_size_1026_;
v___y_945_ = v_a_1002_;
v___y_946_ = v___x_989_;
v___y_947_ = v_a_1004_;
v___y_948_ = v_origin_978_;
v___y_949_ = v___x_1007_;
v_patternsFoundSoFar_950_ = v_a_1013_;
v___y_951_ = v___y_979_;
v___y_952_ = v___y_980_;
v___y_953_ = v___y_981_;
v___y_954_ = v___y_982_;
v___y_955_ = v___y_983_;
v___y_956_ = v___y_984_;
v___y_957_ = v___y_985_;
v___y_958_ = v___y_986_;
v___y_959_ = v___y_987_;
v___y_960_ = v___y_988_;
goto v___jp_943_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_a_1013_);
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec(v___x_1000_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
v_a_1027_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1015_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1015_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec(v___x_1000_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
v_a_1035_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1012_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1012_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_a_1004_);
lean_dec(v_a_1002_);
lean_dec(v___x_1000_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
v_a_1043_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1008_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1008_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1002_);
lean_dec(v___x_1000_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
v_a_1051_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1003_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1003_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v___x_1000_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
v_a_1059_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1001_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1001_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v___x_989_);
lean_dec_ref(v_origin_978_);
lean_dec_ref(v_e_848_);
v_a_1068_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_990_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_990_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_e_848_);
v_a_1146_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_975_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_975_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
v___jp_860_:
{
lean_object* v___x_869_; lean_object* v_toGoalState_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_905_; 
v___x_869_ = lean_st_ref_get(v___y_862_);
v_toGoalState_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_869_, 1);
lean_dec(v_unused_906_);
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_905_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_toGoalState_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_905_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_ematch_874_; lean_object* v_newThms_875_; lean_object* v_size_876_; uint8_t v___x_877_; 
v_ematch_874_ = lean_ctor_get(v_toGoalState_870_, 12);
lean_inc_ref(v_ematch_874_);
lean_dec_ref(v_toGoalState_870_);
v_newThms_875_ = lean_ctor_get(v_ematch_874_, 3);
lean_inc_ref(v_newThms_875_);
lean_dec_ref(v_ematch_874_);
v_size_876_ = lean_ctor_get(v_newThms_875_, 2);
lean_inc(v_size_876_);
lean_dec_ref(v_newThms_875_);
v___x_877_ = lean_nat_dec_eq(v_size_876_, v___y_861_);
lean_dec(v___y_861_);
lean_dec(v_size_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_del_object(v___x_872_);
lean_dec_ref(v_e_848_);
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_863_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_896_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_896_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v___x_885_; 
v___x_885_ = lean_unbox(v_a_881_);
lean_dec(v_a_881_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_del_object(v___x_872_);
lean_dec_ref(v_e_848_);
v___x_886_ = lean_box(0);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_886_);
v___x_888_ = v___x_883_;
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
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
lean_del_object(v___x_883_);
v___x_890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
v___x_891_ = l_Lean_indentExpr(v_e_848_);
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 7);
lean_ctor_set(v___x_872_, 1, v___x_891_);
lean_ctor_set(v___x_872_, 0, v___x_890_);
v___x_893_ = v___x_872_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_895_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Sym_reportIssue(v___x_893_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_872_);
lean_dec_ref(v_e_848_);
v_a_897_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_880_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_880_);
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
}
v___jp_907_:
{
lean_object* v___x_924_; lean_object* v_toGoalState_925_; lean_object* v_ematch_926_; lean_object* v_newThms_927_; lean_object* v_size_928_; uint8_t v___x_929_; 
v___x_924_ = lean_st_ref_get(v___y_914_);
v_toGoalState_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc_ref(v_toGoalState_925_);
lean_dec(v___x_924_);
v_ematch_926_ = lean_ctor_get(v_toGoalState_925_, 12);
lean_inc_ref(v_ematch_926_);
lean_dec_ref(v_toGoalState_925_);
v_newThms_927_ = lean_ctor_get(v_ematch_926_, 3);
lean_inc_ref(v_newThms_927_);
lean_dec_ref(v_ematch_926_);
v_size_928_ = lean_ctor_get(v_newThms_927_, 2);
lean_inc(v_size_928_);
lean_dec_ref(v_newThms_927_);
v___x_929_ = lean_nat_dec_eq(v_size_928_, v___y_908_);
lean_dec(v_size_928_);
if (v___x_929_ == 0)
{
lean_dec_ref(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
v___y_861_ = v___y_908_;
v___y_862_ = v___y_914_;
v___y_863_ = v___y_918_;
v___y_864_ = v___y_919_;
v___y_865_ = v___y_920_;
v___y_866_ = v___y_921_;
v___y_867_ = v___y_922_;
v___y_868_ = v___y_923_;
goto v___jp_860_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_930_, 0, v___y_913_);
v___x_931_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v___y_912_, v___y_910_, v___x_930_, v___y_911_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref(v___x_931_);
if (lean_obj_tag(v_a_932_) == 1)
{
lean_object* v_val_933_; lean_object* v___x_934_; 
v_val_933_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_val_933_);
lean_dec_ref(v_a_932_);
v___x_934_ = l_Lean_Meta_Grind_activateTheorem(v_val_933_, v___y_909_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec_ref(v___x_934_);
v___y_861_ = v___y_908_;
v___y_862_ = v___y_914_;
v___y_863_ = v___y_918_;
v___y_864_ = v___y_919_;
v___y_865_ = v___y_920_;
v___y_866_ = v___y_921_;
v___y_867_ = v___y_922_;
v___y_868_ = v___y_923_;
goto v___jp_860_;
}
else
{
lean_dec(v___y_908_);
lean_dec_ref(v_e_848_);
return v___x_934_;
}
}
else
{
lean_dec(v_a_932_);
lean_dec(v___y_909_);
v___y_861_ = v___y_908_;
v___y_862_ = v___y_914_;
v___y_863_ = v___y_918_;
v___y_864_ = v___y_919_;
v___y_865_ = v___y_920_;
v___y_866_ = v___y_921_;
v___y_867_ = v___y_922_;
v___y_868_ = v___y_923_;
goto v___jp_860_;
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v_e_848_);
v_a_935_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_931_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
v___jp_943_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_box(7);
lean_inc_ref(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc_ref(v___y_948_);
v___x_962_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v___y_948_, v___y_946_, v___x_961_, v___y_947_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_962_);
if (lean_obj_tag(v_a_963_) == 1)
{
lean_object* v_val_964_; uint8_t v___x_965_; 
v_val_964_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_val_964_);
lean_dec_ref(v_a_963_);
v___x_965_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_950_, v_val_964_);
lean_dec_ref(v_patternsFoundSoFar_950_);
if (v___x_965_ == 0)
{
lean_dec(v_val_964_);
v___y_908_ = v___y_944_;
v___y_909_ = v___y_945_;
v___y_910_ = v___y_946_;
v___y_911_ = v___y_947_;
v___y_912_ = v___y_948_;
v___y_913_ = v___y_949_;
v___y_914_ = v___y_951_;
v___y_915_ = v___y_952_;
v___y_916_ = v___y_953_;
v___y_917_ = v___y_954_;
v___y_918_ = v___y_955_;
v___y_919_ = v___y_956_;
v___y_920_ = v___y_957_;
v___y_921_ = v___y_958_;
v___y_922_ = v___y_959_;
v___y_923_ = v___y_960_;
goto v___jp_907_;
}
else
{
lean_object* v___x_966_; 
lean_inc(v___y_945_);
v___x_966_ = l_Lean_Meta_Grind_activateTheorem(v_val_964_, v___y_945_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_dec_ref(v___x_966_);
v___y_908_ = v___y_944_;
v___y_909_ = v___y_945_;
v___y_910_ = v___y_946_;
v___y_911_ = v___y_947_;
v___y_912_ = v___y_948_;
v___y_913_ = v___y_949_;
v___y_914_ = v___y_951_;
v___y_915_ = v___y_952_;
v___y_916_ = v___y_953_;
v___y_917_ = v___y_954_;
v___y_918_ = v___y_955_;
v___y_919_ = v___y_956_;
v___y_920_ = v___y_957_;
v___y_921_ = v___y_958_;
v___y_922_ = v___y_959_;
v___y_923_ = v___y_960_;
goto v___jp_907_;
}
else
{
lean_dec_ref(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v_e_848_);
return v___x_966_;
}
}
}
else
{
lean_dec(v_a_963_);
lean_dec_ref(v_patternsFoundSoFar_950_);
v___y_908_ = v___y_944_;
v___y_909_ = v___y_945_;
v___y_910_ = v___y_946_;
v___y_911_ = v___y_947_;
v___y_912_ = v___y_948_;
v___y_913_ = v___y_949_;
v___y_914_ = v___y_951_;
v___y_915_ = v___y_952_;
v___y_916_ = v___y_953_;
v___y_917_ = v___y_954_;
v___y_918_ = v___y_955_;
v___y_919_ = v___y_956_;
v___y_920_ = v___y_957_;
v___y_921_ = v___y_958_;
v___y_922_ = v___y_959_;
v___y_923_ = v___y_960_;
goto v___jp_907_;
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_patternsFoundSoFar_950_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v_e_848_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* v_e_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec(v_a_1155_);
return v_res_1166_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1172_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_1173_ = l_Lean_Name_append(v___x_1172_, v___x_1171_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__3));
v___x_1176_ = l_Lean_stringToMessageData(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__10));
v___x_1192_ = l_Lean_mkConst(v___x_1191_, v___x_1190_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__13));
v___x_1200_ = l_Lean_mkConst(v___x_1199_, v___x_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
if (lean_obj_tag(v_e_1201_) == 7)
{
lean_object* v_binderName_1213_; lean_object* v_binderType_1214_; lean_object* v_body_1215_; uint8_t v_binderInfo_1216_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___x_1325_; 
v_binderName_1213_ = lean_ctor_get(v_e_1201_, 0);
v_binderType_1214_ = lean_ctor_get(v_e_1201_, 1);
v_body_1215_ = lean_ctor_get(v_e_1201_, 2);
v_binderInfo_1216_ = lean_ctor_get_uint8(v_e_1201_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_1201_);
v___x_1325_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1201_, v_a_1202_, v_a_1206_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; uint8_t v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = lean_unbox(v_a_1326_);
lean_dec(v_a_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_inc_ref(v_e_1201_);
v___x_1328_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1201_, v_a_1202_, v_a_1206_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1412_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1412_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1412_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_unbox(v_a_1329_);
lean_dec(v_a_1329_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec_ref(v_e_1201_);
v___x_1334_ = lean_box(0);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1334_);
v___x_1336_ = v___x_1331_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v___x_1338_; 
lean_del_object(v___x_1331_);
lean_inc_ref(v_e_1201_);
v___x_1338_ = l_Lean_Meta_Grind_eqResolution(v_e_1201_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref(v___x_1338_);
if (lean_obj_tag(v_a_1339_) == 1)
{
lean_object* v_val_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1403_; 
v_val_1340_ = lean_ctor_get(v_a_1339_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_a_1339_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1342_ = v_a_1339_;
v_isShared_1343_ = v_isSharedCheck_1403_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_val_1340_);
lean_dec(v_a_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1403_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1402_; 
v_fst_1344_ = lean_ctor_get(v_val_1340_, 0);
v_snd_1345_ = lean_ctor_get(v_val_1340_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_val_1340_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1347_ = v_val_1340_;
v_isShared_1348_ = v_isSharedCheck_1402_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1344_);
lean_dec(v_val_1340_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1402_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v_options_1387_; uint8_t v_hasTrace_1388_; 
v_options_1387_ = lean_ctor_get(v_a_1210_, 2);
v_hasTrace_1388_ = lean_ctor_get_uint8(v_options_1387_, sizeof(void*)*1);
if (v_hasTrace_1388_ == 0)
{
lean_del_object(v___x_1347_);
v___y_1350_ = v_a_1202_;
v___y_1351_ = v_a_1203_;
v___y_1352_ = v_a_1204_;
v___y_1353_ = v_a_1205_;
v___y_1354_ = v_a_1206_;
v___y_1355_ = v_a_1207_;
v___y_1356_ = v_a_1208_;
v___y_1357_ = v_a_1209_;
v___y_1358_ = v_a_1210_;
v___y_1359_ = v_a_1211_;
goto v___jp_1349_;
}
else
{
lean_object* v_inheritedTraceOptions_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_inheritedTraceOptions_1389_ = lean_ctor_get(v_a_1210_, 13);
v___x_1390_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1391_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__2, &l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2);
v___x_1392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1389_, v_options_1387_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_del_object(v___x_1347_);
v___y_1350_ = v_a_1202_;
v___y_1351_ = v_a_1203_;
v___y_1352_ = v_a_1204_;
v___y_1353_ = v_a_1205_;
v___y_1354_ = v_a_1206_;
v___y_1355_ = v_a_1207_;
v___y_1356_ = v_a_1208_;
v___y_1357_ = v_a_1209_;
v___y_1358_ = v_a_1210_;
v___y_1359_ = v_a_1211_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Meta_Grind_updateLastTag(v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
lean_dec_ref(v___x_1393_);
lean_inc_ref(v_e_1201_);
v___x_1394_ = l_Lean_MessageData_ofExpr(v_e_1201_);
v___x_1395_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__4, &l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 7);
lean_ctor_set(v___x_1347_, 1, v___x_1395_);
lean_ctor_set(v___x_1347_, 0, v___x_1394_);
v___x_1397_ = v___x_1347_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_inc(v_fst_1344_);
v___x_1398_ = l_Lean_MessageData_ofExpr(v_fst_1344_);
v___x_1399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v___x_1390_, v___x_1399_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_dec_ref(v___x_1400_);
v___y_1350_ = v_a_1202_;
v___y_1351_ = v_a_1203_;
v___y_1352_ = v_a_1204_;
v___y_1353_ = v_a_1205_;
v___y_1354_ = v_a_1206_;
v___y_1355_ = v_a_1207_;
v___y_1356_ = v_a_1208_;
v___y_1357_ = v_a_1209_;
v___y_1358_ = v_a_1210_;
v___y_1359_ = v_a_1211_;
goto v___jp_1349_;
}
else
{
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_e_1201_);
return v___x_1400_;
}
}
}
else
{
lean_del_object(v___x_1347_);
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_e_1201_);
return v___x_1393_;
}
}
}
v___jp_1349_:
{
lean_object* v___x_1360_; 
lean_inc_ref(v_e_1201_);
v___x_1360_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1201_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1201_, v___y_1350_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
lean_inc_ref_n(v_e_1201_, 2);
v___x_1364_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1201_, v_a_1361_);
v___x_1365_ = l_Lean_Expr_app___override(v_snd_1345_, v___x_1364_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 4);
lean_ctor_set(v___x_1342_, 0, v_e_1201_);
v___x_1367_ = v___x_1342_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_e_1201_);
v___x_1367_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(1);
v___x_1369_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1365_, v_fst_1344_, v_a_1363_, v___x_1367_, v___x_1368_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec_ref(v___x_1369_);
v___y_1271_ = v___y_1350_;
v___y_1272_ = v___y_1351_;
v___y_1273_ = v___y_1352_;
v___y_1274_ = v___y_1353_;
v___y_1275_ = v___y_1354_;
v___y_1276_ = v___y_1355_;
v___y_1277_ = v___y_1356_;
v___y_1278_ = v___y_1357_;
v___y_1279_ = v___y_1358_;
v___y_1280_ = v___y_1359_;
goto v___jp_1270_;
}
else
{
lean_dec_ref(v_e_1201_);
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_a_1361_);
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_e_1201_);
v_a_1371_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1362_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1362_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_del_object(v___x_1342_);
lean_dec_ref(v_e_1201_);
v_a_1379_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1360_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1360_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1339_);
v___y_1271_ = v_a_1202_;
v___y_1272_ = v_a_1203_;
v___y_1273_ = v_a_1204_;
v___y_1274_ = v_a_1205_;
v___y_1275_ = v_a_1206_;
v___y_1276_ = v_a_1207_;
v___y_1277_ = v_a_1208_;
v___y_1278_ = v_a_1209_;
v___y_1279_ = v_a_1210_;
v___y_1280_ = v_a_1211_;
goto v___jp_1270_;
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_e_1201_);
v_a_1404_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1338_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1338_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_e_1201_);
v_a_1413_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1328_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1328_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v___x_1421_; 
lean_inc_ref(v_binderType_1214_);
v___x_1421_ = l_Lean_Meta_isProp(v_binderType_1214_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; uint8_t v___x_1468_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v___x_1468_ = l_Lean_Expr_hasLooseBVars(v_body_1215_);
if (v___x_1468_ == 0)
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_unbox(v_a_1422_);
lean_dec(v_a_1422_);
if (v___x_1469_ == 0)
{
goto v___jp_1423_;
}
else
{
if (v___x_1468_ == 0)
{
lean_object* v___x_1470_; 
lean_inc_ref(v_body_1215_);
lean_inc_ref(v_binderType_1214_);
v___x_1470_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc_n(v_a_1471_, 2);
lean_dec_ref(v___x_1470_);
v___x_1472_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__11, &l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
lean_inc_ref(v_body_1215_);
lean_inc_ref_n(v_binderType_1214_, 2);
v___x_1473_ = l_Lean_mkApp3(v___x_1472_, v_binderType_1214_, v_body_1215_, v_a_1471_);
v___x_1474_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_binderType_1214_, v___x_1473_, v_a_1202_, v_a_1204_, v_a_1206_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec_ref(v___x_1474_);
v___x_1475_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__14, &l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14);
lean_inc_ref(v_body_1215_);
v___x_1476_ = l_Lean_mkApp3(v___x_1475_, v_binderType_1214_, v_body_1215_, v_a_1471_);
v___x_1477_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_body_1215_, v___x_1476_, v_a_1202_, v_a_1204_, v_a_1206_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1477_;
}
else
{
lean_dec(v_a_1471_);
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
return v___x_1474_;
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
v_a_1478_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1470_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1470_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
goto v___jp_1423_;
}
}
}
else
{
lean_dec(v_a_1422_);
goto v___jp_1423_;
}
v___jp_1423_:
{
lean_object* v___x_1424_; 
lean_inc_ref(v_binderType_1214_);
v___x_1424_ = l_Lean_Meta_getLevel(v_binderType_1214_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1424_);
lean_inc_ref(v_e_1201_);
v___x_1426_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref(v___x_1426_);
lean_inc_ref(v_body_1215_);
v___x_1428_ = l_Lean_mkNot(v_body_1215_);
lean_inc_ref(v_binderType_1214_);
lean_inc(v_binderName_1213_);
v___x_1429_ = l_Lean_mkLambda(v_binderName_1213_, v_binderInfo_1216_, v_binderType_1214_, v___x_1428_);
v___x_1430_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_a_1425_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
lean_inc_ref(v___x_1434_);
v___x_1435_ = l_Lean_mkConst(v___x_1432_, v___x_1434_);
lean_inc_ref_n(v_binderType_1214_, 3);
v___x_1436_ = l_Lean_mkAppB(v___x_1435_, v_binderType_1214_, v___x_1429_);
lean_inc_ref(v_body_1215_);
lean_inc(v_binderName_1213_);
v___x_1437_ = l_Lean_mkLambda(v_binderName_1213_, v_binderInfo_1216_, v_binderType_1214_, v_body_1215_);
v___x_1438_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__8));
v___x_1439_ = l_Lean_mkConst(v___x_1438_, v___x_1434_);
v___x_1440_ = l_Lean_mkApp3(v___x_1439_, v_binderType_1214_, v___x_1437_, v_a_1427_);
v___x_1441_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_e_1201_);
v___x_1442_ = lean_box(1);
v___x_1443_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1440_, v___x_1436_, v_a_1431_, v___x_1441_, v___x_1442_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1443_;
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v___x_1429_);
lean_dec(v_a_1427_);
lean_dec(v_a_1425_);
lean_dec_ref(v_e_1201_);
v_a_1444_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1430_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1430_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_a_1425_);
lean_dec_ref(v_e_1201_);
v_a_1452_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1426_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1426_);
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
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v_e_1201_);
v_a_1460_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1424_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1424_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_e_1201_);
v_a_1486_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1421_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1421_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_e_1201_);
v_a_1494_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1325_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1325_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
v___jp_1217_:
{
if (lean_obj_tag(v___y_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1261_; 
v_a_1229_ = lean_ctor_get(v___y_1228_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___y_1228_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1231_ = v___y_1228_;
v_isShared_1232_ = v_isSharedCheck_1261_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___y_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1261_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_unbox(v_a_1229_);
lean_dec(v_a_1229_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
lean_dec_ref(v_e_1201_);
v___x_1234_ = lean_box(0);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
else
{
lean_object* v___x_1238_; 
lean_del_object(v___x_1231_);
v___x_1238_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1201_, v___y_1218_, v___y_1223_, v___y_1225_, v___y_1227_, v___y_1219_, v___y_1222_, v___y_1221_, v___y_1224_, v___y_1220_, v___y_1226_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
lean_inc_ref(v_body_1215_);
v___x_1240_ = l_Lean_Meta_Grind_mkEqFalseProof(v_body_1215_, v___y_1218_, v___y_1223_, v___y_1225_, v___y_1227_, v___y_1219_, v___y_1222_, v___y_1221_, v___y_1224_, v___y_1220_, v___y_1226_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(v_binderType_1214_);
v___x_1243_ = l_Lean_mkApp4(v___x_1242_, v_binderType_1214_, v_body_1215_, v_a_1239_, v_a_1241_);
v___x_1244_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_binderType_1214_, v___x_1243_, v___y_1218_, v___y_1225_, v___y_1219_, v___y_1221_, v___y_1224_, v___y_1220_, v___y_1226_);
return v___x_1244_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_a_1239_);
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
v_a_1245_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1240_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1240_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
v_a_1253_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1238_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1238_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
lean_dec_ref(v_e_1201_);
v_a_1262_ = lean_ctor_get(v___y_1228_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___y_1228_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___y_1228_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___y_1228_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
v___jp_1270_:
{
uint8_t v___x_1281_; 
v___x_1281_ = l_Lean_Expr_hasLooseBVars(v_body_1215_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_inc_ref(v_body_1215_);
lean_inc_ref(v_binderType_1214_);
v___x_1282_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_body_1215_, v___y_1271_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1296_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1296_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1296_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_unbox(v_a_1283_);
lean_dec(v_a_1283_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
lean_dec_ref(v_e_1201_);
v___x_1288_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
lean_object* v___x_1292_; 
lean_del_object(v___x_1285_);
lean_inc_ref(v_body_1215_);
v___x_1292_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_1215_, v___y_1271_, v___y_1275_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; uint8_t v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
v___x_1294_ = lean_unbox(v_a_1293_);
lean_dec(v_a_1293_);
if (v___x_1294_ == 0)
{
v___y_1218_ = v___y_1271_;
v___y_1219_ = v___y_1275_;
v___y_1220_ = v___y_1279_;
v___y_1221_ = v___y_1277_;
v___y_1222_ = v___y_1276_;
v___y_1223_ = v___y_1272_;
v___y_1224_ = v___y_1278_;
v___y_1225_ = v___y_1273_;
v___y_1226_ = v___y_1280_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v___x_1292_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1295_; 
lean_dec_ref(v___x_1292_);
lean_inc_ref(v_binderType_1214_);
v___x_1295_ = l_Lean_Meta_isProp(v_binderType_1214_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v___y_1218_ = v___y_1271_;
v___y_1219_ = v___y_1275_;
v___y_1220_ = v___y_1279_;
v___y_1221_ = v___y_1277_;
v___y_1222_ = v___y_1276_;
v___y_1223_ = v___y_1272_;
v___y_1224_ = v___y_1278_;
v___y_1225_ = v___y_1273_;
v___y_1226_ = v___y_1280_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v___x_1295_;
goto v___jp_1217_;
}
}
else
{
v___y_1218_ = v___y_1271_;
v___y_1219_ = v___y_1275_;
v___y_1220_ = v___y_1279_;
v___y_1221_ = v___y_1277_;
v___y_1222_ = v___y_1276_;
v___y_1223_ = v___y_1272_;
v___y_1224_ = v___y_1278_;
v___y_1225_ = v___y_1273_;
v___y_1226_ = v___y_1280_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v___x_1292_;
goto v___jp_1217_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_body_1215_);
lean_dec_ref(v_binderType_1214_);
lean_dec_ref(v_e_1201_);
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
else
{
lean_object* v___x_1305_; 
lean_inc_ref(v_binderType_1214_);
v___x_1305_ = l_Lean_Meta_isProp(v_binderType_1214_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1316_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_del_object(v___x_1308_);
v___x_1311_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1201_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec_ref(v_e_1201_);
v___x_1312_ = lean_box(0);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1312_);
v___x_1314_ = v___x_1308_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
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
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_e_1201_);
v_a_1317_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1305_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1305_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec_ref(v_e_1201_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Meta_Grind_propagateForallPropDown(v_e_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec(v_a_1505_);
return v_res_1516_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1522_ = l_Lean_mkConst(v___x_1521_, v___x_1520_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = l_Lean_Expr_bvar___override(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1546_; 
lean_inc_ref(v_e_1531_);
v___x_1546_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1531_, v_a_1532_, v_a_1536_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1601_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1601_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1601_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_unbox(v_a_1547_);
lean_dec(v_a_1547_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec_ref(v_e_1531_);
v___x_1552_ = lean_box(0);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
lean_del_object(v___x_1549_);
lean_inc_ref(v_e_1531_);
v___x_1556_ = l_Lean_Expr_cleanupAnnotations(v_e_1531_);
v___x_1557_ = l_Lean_Expr_isApp(v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec_ref(v___x_1556_);
lean_dec_ref(v_e_1531_);
goto v___jp_1543_;
}
else
{
lean_object* v_arg_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_arg_1558_ = lean_ctor_get(v___x_1556_, 1);
lean_inc_ref(v_arg_1558_);
v___x_1559_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1556_);
v___x_1560_ = l_Lean_Expr_isApp(v___x_1559_);
if (v___x_1560_ == 0)
{
lean_dec_ref(v___x_1559_);
lean_dec_ref(v_arg_1558_);
lean_dec_ref(v_e_1531_);
goto v___jp_1543_;
}
else
{
lean_object* v_arg_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_arg_1561_ = lean_ctor_get(v___x_1559_, 1);
lean_inc_ref(v_arg_1561_);
v___x_1562_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1559_);
v___x_1563_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1564_ = l_Lean_Expr_isConstOf(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v___x_1562_);
lean_dec_ref(v_arg_1561_);
lean_dec_ref(v_arg_1558_);
lean_dec_ref(v_e_1531_);
goto v___jp_1543_;
}
else
{
lean_object* v___x_1565_; 
lean_inc_ref(v_e_1531_);
v___x_1565_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1531_, v_a_1532_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__2, &l_Lean_Meta_Grind_propagateExistsDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2);
v___x_1570_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__3, &l_Lean_Meta_Grind_propagateExistsDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3);
lean_inc_ref(v_arg_1558_);
v___x_1571_ = l_Lean_Expr_app___override(v_arg_1558_, v___x_1570_);
v___x_1572_ = l_Lean_Expr_headBeta(v___x_1571_);
v___x_1573_ = l_Lean_Expr_app___override(v___x_1569_, v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__5));
v___x_1575_ = 0;
lean_inc_ref(v_arg_1561_);
v___x_1576_ = l_Lean_mkForall(v___x_1574_, v___x_1575_, v_arg_1561_, v___x_1573_);
v___x_1577_ = l_Lean_Expr_constLevels_x21(v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1578_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__7));
v___x_1579_ = l_Lean_mkConst(v___x_1578_, v___x_1577_);
lean_inc_ref(v_e_1531_);
v___x_1580_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1531_, v_a_1566_);
v___x_1581_ = l_Lean_mkApp3(v___x_1579_, v_arg_1561_, v_arg_1558_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_e_1531_);
v___x_1583_ = lean_box(1);
v___x_1584_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1581_, v___x_1576_, v_a_1568_, v___x_1582_, v___x_1583_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
return v___x_1584_;
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_a_1566_);
lean_dec_ref(v___x_1562_);
lean_dec_ref(v_arg_1561_);
lean_dec_ref(v_arg_1558_);
lean_dec_ref(v_e_1531_);
v_a_1585_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1567_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1567_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v___x_1562_);
lean_dec_ref(v_arg_1561_);
lean_dec_ref(v_arg_1558_);
lean_dec_ref(v_e_1531_);
v_a_1593_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1565_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1565_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
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
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_e_1531_);
v_a_1602_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1546_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1546_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
v___jp_1543_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* v_e_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Meta_Grind_propagateExistsDown(v_e_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec(v_a_1611_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1625_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 12, 0);
v___x_1626_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1624_, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8____boxed(lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8_();
return v_res_1628_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = lean_box(0);
v___x_1636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_1637_ = l_Lean_mkConst(v___x_1636_, v___x_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object* v_e_1638_){
_start:
{
if (lean_obj_tag(v_e_1638_) == 7)
{
lean_object* v_binderName_1639_; lean_object* v_binderType_1640_; lean_object* v_body_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_binderName_1639_ = lean_ctor_get(v_e_1638_, 0);
v_binderType_1640_ = lean_ctor_get(v_e_1638_, 1);
v_body_1641_ = lean_ctor_get(v_e_1638_, 2);
lean_inc_ref(v_body_1641_);
lean_inc_ref(v_binderType_1640_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_binderType_1640_);
lean_ctor_set(v___x_1642_, 1, v_body_1641_);
lean_inc(v_binderName_1639_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_binderName_1639_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1646_ = lean_unsigned_to_nat(1u);
v___x_1647_ = l_Lean_Expr_isAppOfArity(v_e_1638_, v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_box(0);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1));
v___x_1650_ = l_Lean_Expr_appArg_x21(v_e_1638_);
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1649_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object* v_e_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_e_1655_);
lean_dec_ref(v_e_1655_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* v_fst_1657_, lean_object* v_a_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_expr_instantiate1(v_fst_1657_, v_a_1658_);
v___x_1668_ = l_Lean_Meta_getLevel(v___x_1667_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* v_fst_1669_, lean_object* v_a_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Meta_Grind_simpForall___lam__0(v_fst_1669_, v_a_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v_a_1670_);
lean_dec_ref(v_fst_1669_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v_b_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
v___x_1690_ = lean_apply_9(v_k_1680_, v_b_1684_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, lean_box(0));
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(v_k_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v_b_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* v_name_1702_, uint8_t v_bi_1703_, lean_object* v_type_1704_, lean_object* v_k_1705_, uint8_t v_kind_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___f_1715_; lean_object* v___x_1716_; 
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
v___f_1715_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1715_, 0, v_k_1705_);
lean_closure_set(v___f_1715_, 1, v___y_1707_);
lean_closure_set(v___f_1715_, 2, v___y_1708_);
lean_closure_set(v___f_1715_, 3, v___y_1709_);
v___x_1716_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1702_, v_bi_1703_, v_type_1704_, v___f_1715_, v_kind_1706_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1716_) == 0)
{
return v___x_1716_;
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_1725_, lean_object* v_bi_1726_, lean_object* v_type_1727_, lean_object* v_k_1728_, lean_object* v_kind_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v_bi_boxed_1738_; uint8_t v_kind_boxed_1739_; lean_object* v_res_1740_; 
v_bi_boxed_1738_ = lean_unbox(v_bi_1726_);
v_kind_boxed_1739_ = lean_unbox(v_kind_1729_);
v_res_1740_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1725_, v_bi_boxed_1738_, v_type_1727_, v_k_1728_, v_kind_boxed_1739_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* v_name_1741_, lean_object* v_type_1742_, lean_object* v_k_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = 0;
v___x_1753_ = 0;
v___x_1754_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1741_, v___x_1752_, v_type_1742_, v_k_1743_, v___x_1753_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* v_name_1755_, lean_object* v_type_1756_, lean_object* v_k_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_1755_, v_type_1756_, v_k_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__13(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_box(0);
v___x_1794_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_1795_ = l_Lean_mkConst(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__16(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__15));
v___x_1803_ = l_Lean_mkConst(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__21(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_box(0);
v___x_1815_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__20));
v___x_1816_ = l_Lean_mkConst(v___x_1815_, v___x_1814_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__24(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_box(0);
v___x_1823_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__23));
v___x_1824_ = l_Lean_mkConst(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__27(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__26));
v___x_1832_ = l_Lean_mkConst(v___x_1831_, v___x_1830_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__30(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__29));
v___x_1840_ = l_Lean_mkConst(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__33(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_box(0);
v___x_1846_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__32));
v___x_1847_ = l_Lean_mkConst(v___x_1846_, v___x_1845_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__36(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_box(0);
v___x_1854_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__35));
v___x_1855_ = l_Lean_mkConst(v___x_1854_, v___x_1853_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__37(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = l_Lean_Level_ofNat(v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__38(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__37, &l_Lean_Meta_Grind_simpForall___closed__37_once, _init_l_Lean_Meta_Grind_simpForall___closed__37);
v___x_1859_ = l_Lean_mkSort(v___x_1858_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__41(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_box(0);
v___x_1864_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__40));
v___x_1865_ = l_Lean_mkConst(v___x_1864_, v___x_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* v_e_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
if (lean_obj_tag(v_e_1866_) == 7)
{
lean_object* v_binderName_1878_; lean_object* v_binderType_1879_; lean_object* v_body_1880_; uint8_t v_binderInfo_1881_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; uint8_t v___y_1890_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; uint8_t v___x_2090_; 
v_binderName_1878_ = lean_ctor_get(v_e_1866_, 0);
lean_inc(v_binderName_1878_);
v_binderType_1879_ = lean_ctor_get(v_e_1866_, 1);
lean_inc_ref(v_binderType_1879_);
v_body_1880_ = lean_ctor_get(v_e_1866_, 2);
lean_inc_ref(v_body_1880_);
v_binderInfo_1881_ = lean_ctor_get_uint8(v_e_1866_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1866_);
v___x_2090_ = l_Lean_Expr_hasLooseBVars(v_body_1880_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_inc_ref(v_binderType_1879_);
v___x_2091_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1879_, v_a_1871_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; uint8_t v___x_2093_; lean_object* v___y_2095_; lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = 1;
v___x_2119_ = l_Lean_Expr_cleanupAnnotations(v_a_2092_);
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2121_ = l_Lean_Expr_isConstOf(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_2123_ = l_Lean_Expr_isConstOf(v___x_2119_, v___x_2122_);
lean_dec_ref(v___x_2119_);
if (v___x_2123_ == 0)
{
if (lean_obj_tag(v_binderType_1879_) == 7)
{
lean_object* v_binderName_2124_; lean_object* v_binderType_2125_; lean_object* v_body_2126_; uint8_t v_binderInfo_2127_; uint8_t v_a_2129_; uint8_t v___x_2162_; 
v_binderName_2124_ = lean_ctor_get(v_binderType_1879_, 0);
v_binderType_2125_ = lean_ctor_get(v_binderType_1879_, 1);
v_body_2126_ = lean_ctor_get(v_binderType_1879_, 2);
v_binderInfo_2127_ = lean_ctor_get_uint8(v_binderType_1879_, sizeof(void*)*3 + 8);
v___x_2162_ = l_Lean_Expr_hasLooseBVars(v_body_2126_);
if (v___x_2162_ == 0)
{
v_a_2129_ = v___x_2162_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2163_; 
lean_inc_ref(v_binderType_1879_);
v___x_2163_ = l_Lean_Meta_isProp(v_binderType_1879_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; uint8_t v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = lean_unbox(v_a_2164_);
lean_dec(v_a_2164_);
v_a_2129_ = v___x_2165_;
goto v___jp_2128_;
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_binderType_1879_);
lean_dec_ref(v_body_1880_);
lean_dec(v_binderName_1878_);
v_a_2166_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2163_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2163_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
v___jp_2128_:
{
if (v_a_2129_ == 0)
{
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_inc_ref_n(v_body_2126_, 2);
lean_inc_ref_n(v_binderType_2125_, 3);
lean_inc_n(v_binderName_2124_, 2);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v___x_2130_ = l_Lean_mkLambda(v_binderName_2124_, v_binderInfo_2127_, v_binderType_2125_, v_body_2126_);
v___x_2131_ = l_Lean_Meta_getLevel(v_binderType_2125_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2153_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2153_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2153_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2136_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2137_ = lean_box(0);
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_a_2132_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
lean_inc_ref(v___x_2138_);
v___x_2139_ = l_Lean_mkConst(v___x_2136_, v___x_2138_);
v___x_2140_ = l_Lean_mkNot(v_body_2126_);
lean_inc_ref_n(v_binderType_2125_, 2);
v___x_2141_ = l_Lean_mkLambda(v_binderName_2124_, v_binderInfo_2127_, v_binderType_2125_, v___x_2140_);
v___x_2142_ = l_Lean_mkAppB(v___x_2139_, v_binderType_2125_, v___x_2141_);
lean_inc_ref(v_body_1880_);
v___x_2143_ = l_Lean_mkOr(v___x_2142_, v_body_1880_);
v___x_2144_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__18));
v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2138_);
v___x_2146_ = l_Lean_mkApp3(v___x_2145_, v_binderType_2125_, v___x_2130_, v_body_1880_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2143_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*2, v___x_2093_);
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2149_);
v___x_2151_ = v___x_2134_;
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
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v___x_2130_);
lean_dec_ref(v_body_2126_);
lean_dec_ref(v_binderType_2125_);
lean_dec(v_binderName_2124_);
lean_dec_ref(v_body_1880_);
v_a_2154_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2131_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2131_);
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
}
else
{
lean_object* v___x_2174_; 
lean_inc_ref(v_body_1880_);
v___x_2174_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_1880_, v_a_1871_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = l_Lean_Expr_cleanupAnnotations(v_a_2175_);
v___x_2177_ = l_Lean_Expr_isConstOf(v___x_2176_, v___x_2120_);
if (v___x_2177_ == 0)
{
uint8_t v___x_2178_; 
v___x_2178_ = l_Lean_Expr_isConstOf(v___x_2176_, v___x_2122_);
lean_dec_ref(v___x_2176_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; 
lean_inc_ref(v_binderType_1879_);
v___x_2179_ = l_Lean_Meta_isProp(v_binderType_1879_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; uint8_t v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
v___x_2181_ = lean_unbox(v_a_2180_);
lean_dec(v_a_2180_);
if (v___x_2181_ == 0)
{
v___y_2095_ = v___x_2179_;
goto v___jp_2094_;
}
else
{
lean_object* v___x_2182_; 
lean_dec_ref(v___x_2179_);
lean_inc_ref(v_body_1880_);
lean_inc_ref(v_binderType_1879_);
v___x_2182_ = l_Lean_Meta_isExprDefEq(v_binderType_1879_, v_body_1880_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
v___y_2095_ = v___x_2182_;
goto v___jp_2094_;
}
}
else
{
v___y_2095_ = v___x_2179_;
goto v___jp_2094_;
}
}
else
{
lean_object* v___x_2183_; 
lean_inc_ref(v_binderType_1879_);
v___x_2183_ = l_Lean_Meta_isProp(v_binderType_1879_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2198_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2198_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2198_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
uint8_t v___x_2188_; 
v___x_2188_ = lean_unbox(v_a_2184_);
lean_dec(v_a_2184_);
if (v___x_2188_ == 0)
{
lean_del_object(v___x_2186_);
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_dec_ref(v_body_1880_);
lean_dec(v_binderName_1878_);
v___x_2189_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2190_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__21, &l_Lean_Meta_Grind_simpForall___closed__21_once, _init_l_Lean_Meta_Grind_simpForall___closed__21);
v___x_2191_ = l_Lean_Expr_app___override(v___x_2190_, v_binderType_1879_);
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2193_, 0, v___x_2189_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
lean_ctor_set_uint8(v___x_2193_, sizeof(void*)*2, v___x_2093_);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2194_);
v___x_2196_ = v___x_2186_;
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
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2199_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2183_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2183_);
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
else
{
lean_object* v___x_2207_; 
lean_dec_ref(v___x_2176_);
lean_inc_ref(v_binderType_1879_);
v___x_2207_ = l_Lean_Meta_isProp(v_binderType_1879_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2222_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2222_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2222_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_unbox(v_a_2208_);
lean_dec(v_a_2208_);
if (v___x_2212_ == 0)
{
lean_del_object(v___x_2210_);
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_dec_ref(v_body_1880_);
lean_dec(v_binderName_1878_);
lean_inc_ref(v_binderType_1879_);
v___x_2213_ = l_Lean_mkNot(v_binderType_1879_);
v___x_2214_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__24, &l_Lean_Meta_Grind_simpForall___closed__24_once, _init_l_Lean_Meta_Grind_simpForall___closed__24);
v___x_2215_ = l_Lean_Expr_app___override(v___x_2214_, v_binderType_1879_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2217_, 0, v___x_2213_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*2, v___x_2093_);
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2218_);
v___x_2220_ = v___x_2210_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2223_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2207_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2207_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2231_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2174_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2174_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
else
{
lean_object* v___x_2239_; 
lean_inc_ref(v_body_1880_);
v___x_2239_ = l_Lean_Meta_isProp(v_body_1880_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2253_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2253_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2253_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_unbox(v_a_2240_);
lean_dec(v_a_2240_);
if (v___x_2244_ == 0)
{
lean_del_object(v___x_2242_);
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v___x_2245_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__27, &l_Lean_Meta_Grind_simpForall___closed__27_once, _init_l_Lean_Meta_Grind_simpForall___closed__27);
lean_inc_ref(v_body_1880_);
v___x_2246_ = l_Lean_Expr_app___override(v___x_2245_, v_body_1880_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2248_, 0, v_body_1880_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*2, v___x_2093_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2249_);
v___x_2251_ = v___x_2242_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2254_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2239_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2239_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
else
{
lean_object* v___x_2262_; 
lean_dec_ref(v___x_2119_);
lean_inc_ref(v_body_1880_);
v___x_2262_ = l_Lean_Meta_isProp(v_body_1880_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2277_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_unbox(v_a_2263_);
lean_dec(v_a_2263_);
if (v___x_2267_ == 0)
{
lean_del_object(v___x_2265_);
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v___x_2268_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2269_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__30, &l_Lean_Meta_Grind_simpForall___closed__30_once, _init_l_Lean_Meta_Grind_simpForall___closed__30);
v___x_2270_ = l_Lean_Expr_app___override(v___x_2269_, v_body_1880_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2272_, 0, v___x_2268_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*2, v___x_2093_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2273_);
v___x_2275_ = v___x_2265_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2278_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2262_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2262_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
v___jp_2094_:
{
if (lean_obj_tag(v___y_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2110_; 
v_a_2096_ = lean_ctor_get(v___y_2095_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___y_2095_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2098_ = v___y_2095_;
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___y_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_unbox(v_a_2096_);
lean_dec(v_a_2096_);
if (v___x_2100_ == 0)
{
lean_del_object(v___x_2098_);
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_dec_ref(v_body_1880_);
lean_dec(v_binderName_1878_);
v___x_2101_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2102_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__16, &l_Lean_Meta_Grind_simpForall___closed__16_once, _init_l_Lean_Meta_Grind_simpForall___closed__16);
v___x_2103_ = l_Lean_Expr_app___override(v___x_2102_, v_binderType_1879_);
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2105_, 0, v___x_2101_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*2, v___x_2093_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2106_);
v___x_2108_ = v___x_2098_;
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
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2111_ = lean_ctor_get(v___y_2095_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___y_2095_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___y_2095_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___y_2095_);
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
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2286_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2091_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2091_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v___x_2294_; 
lean_inc_ref(v_binderType_1879_);
v___x_2294_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1879_, v_a_1871_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = l_Lean_Expr_cleanupAnnotations(v_a_2295_);
v___x_2297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2298_ = l_Lean_Expr_isConstOf(v___x_2296_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_2300_ = l_Lean_Expr_isConstOf(v___x_2296_, v___x_2299_);
lean_dec_ref(v___x_2296_);
if (v___x_2300_ == 0)
{
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__33, &l_Lean_Meta_Grind_simpForall___closed__33_once, _init_l_Lean_Meta_Grind_simpForall___closed__33);
v___x_2302_ = lean_expr_instantiate1(v_body_1880_, v___x_2301_);
lean_inc_ref(v___x_2302_);
v___x_2303_ = l_Lean_Meta_isProp(v___x_2302_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2318_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2318_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2318_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_unbox(v_a_2304_);
lean_dec(v_a_2304_);
if (v___x_2308_ == 0)
{
lean_del_object(v___x_2306_);
lean_dec_ref(v___x_2302_);
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2309_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_body_1880_);
v___x_2310_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__36, &l_Lean_Meta_Grind_simpForall___closed__36_once, _init_l_Lean_Meta_Grind_simpForall___closed__36);
v___x_2311_ = l_Lean_Expr_app___override(v___x_2310_, v___x_2309_);
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
v___x_2313_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2313_, 0, v___x_2302_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
lean_ctor_set_uint8(v___x_2313_, sizeof(void*)*2, v___x_2090_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2314_);
v___x_2316_ = v___x_2306_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v___x_2302_);
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2319_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2303_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2303_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec_ref(v___x_2296_);
lean_inc_ref(v_body_1880_);
lean_inc_ref(v_binderType_1879_);
lean_inc(v_binderName_1878_);
v___x_2327_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_body_1880_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
lean_inc_ref(v___x_2327_);
v___x_2328_ = lean_infer_type(v___x_2327_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__38, &l_Lean_Meta_Grind_simpForall___closed__38_once, _init_l_Lean_Meta_Grind_simpForall___closed__38);
lean_inc_ref(v_binderType_1879_);
lean_inc(v_binderName_1878_);
v___x_2331_ = l_Lean_mkForall(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v___x_2330_);
v___x_2332_ = l_Lean_Meta_isExprDefEq(v_a_2329_, v___x_2331_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2347_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2347_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2347_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
uint8_t v___x_2337_; 
v___x_2337_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
if (v___x_2337_ == 0)
{
lean_del_object(v___x_2335_);
lean_dec_ref(v___x_2327_);
v___y_2079_ = v_a_1867_;
v___y_2080_ = v_a_1868_;
v___y_2081_ = v_a_1869_;
v___y_2082_ = v_a_1870_;
v___y_2083_ = v_a_1871_;
v___y_2084_ = v_a_1872_;
v___y_2085_ = v_a_1873_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v___x_2338_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2339_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__41, &l_Lean_Meta_Grind_simpForall___closed__41_once, _init_l_Lean_Meta_Grind_simpForall___closed__41);
v___x_2340_ = l_Lean_Expr_app___override(v___x_2339_, v___x_2327_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2338_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*2, v___x_2090_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2343_);
v___x_2345_ = v___x_2335_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
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
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2348_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2332_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2332_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2356_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2328_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2328_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
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
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2364_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2294_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2294_);
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
v___jp_1882_:
{
if (v___y_1890_ == 0)
{
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
goto v___jp_1875_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = l_Lean_Expr_appFn_x21(v_body_1880_);
v___x_1892_ = l_Lean_Expr_appFn_x21(v___x_1891_);
if (lean_obj_tag(v___x_1892_) == 4)
{
lean_object* v_declName_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_declName_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_declName_1893_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_1895_ = lean_name_eq(v_declName_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_1897_ = lean_name_eq(v_declName_1893_, v___x_1896_);
lean_dec(v_declName_1893_);
if (v___x_1897_ == 0)
{
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
goto v___jp_1875_;
}
else
{
lean_object* v_pRaw_1898_; lean_object* v_qRaw_1899_; lean_object* v_p_1900_; lean_object* v_q_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_pRaw_1898_ = l_Lean_Expr_appArg_x21(v___x_1891_);
lean_dec_ref(v___x_1891_);
v_qRaw_1899_ = l_Lean_Expr_appArg_x21(v_body_1880_);
lean_dec_ref(v_body_1880_);
lean_inc_ref(v_pRaw_1898_);
lean_inc_ref_n(v_binderType_1879_, 5);
lean_inc_n(v_binderName_1878_, 3);
v_p_1900_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_pRaw_1898_);
lean_inc_ref(v_qRaw_1899_);
v_q_1901_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_qRaw_1899_);
v___x_1902_ = l_Lean_mkForall(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_pRaw_1898_);
v___x_1903_ = l_Lean_mkForall(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_qRaw_1899_);
v___x_1904_ = l_Lean_Meta_getLevel(v_binderType_1879_, v___y_1889_, v___y_1883_, v___y_1887_, v___y_1886_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1921_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1921_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1921_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_expr_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v_expr_1909_ = l_Lean_mkAnd(v___x_1902_, v___x_1903_);
v___x_1910_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__6));
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_a_1905_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = l_Lean_mkConst(v___x_1910_, v___x_1912_);
v___x_1914_ = l_Lean_mkApp3(v___x_1913_, v_binderType_1879_, v_p_1900_, v_q_1901_);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1916_, 0, v_expr_1909_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*2, v___y_1890_);
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1917_);
v___x_1919_ = v___x_1907_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v___x_1903_);
lean_dec_ref(v___x_1902_);
lean_dec_ref(v_q_1901_);
lean_dec_ref(v_p_1900_);
lean_dec_ref(v_binderType_1879_);
v_a_1922_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1904_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1904_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
else
{
lean_object* v_pRaw_1930_; lean_object* v_pRaw_1931_; lean_object* v___x_1932_; 
lean_dec(v_declName_1893_);
v_pRaw_1930_ = l_Lean_Expr_appArg_x21(v___x_1891_);
lean_dec_ref(v___x_1891_);
v_pRaw_1931_ = l_Lean_Expr_appArg_x21(v_body_1880_);
lean_dec_ref(v_body_1880_);
v___x_1932_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1930_);
if (lean_obj_tag(v___x_1932_) == 1)
{
lean_object* v_val_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_pRaw_1930_);
v_val_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_2003_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_val_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_2003_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_snd_1937_; lean_object* v_fst_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_2002_; 
v_snd_1937_ = lean_ctor_get(v_val_1933_, 1);
v_fst_1938_ = lean_ctor_get(v_val_1933_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_val_1933_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1940_ = v_val_1933_;
v_isShared_1941_ = v_isSharedCheck_2002_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_snd_1937_);
lean_inc(v_fst_1938_);
lean_dec(v_val_1933_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_2002_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_2001_; 
v_fst_1942_ = lean_ctor_get(v_snd_1937_, 0);
v_snd_1943_ = lean_ctor_get(v_snd_1937_, 1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_snd_1937_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1945_ = v_snd_1937_;
v_isShared_1946_ = v_isSharedCheck_2001_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_inc(v_fst_1942_);
lean_dec(v_snd_1937_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_2001_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_p_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v_q_1950_; lean_object* v_00_u03b2_1951_; lean_object* v___x_1952_; 
lean_inc_ref(v_pRaw_1931_);
lean_inc_ref_n(v_binderType_1879_, 4);
lean_inc_n(v_binderName_1878_, 3);
v_p_1947_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_pRaw_1931_);
v___x_1948_ = 0;
lean_inc(v_snd_1943_);
lean_inc_n(v_fst_1942_, 2);
lean_inc(v_fst_1938_);
v___x_1949_ = l_Lean_mkLambda(v_fst_1938_, v___x_1948_, v_fst_1942_, v_snd_1943_);
v_q_1950_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v___x_1949_);
v_00_u03b2_1951_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_fst_1942_);
v___x_1952_ = l_Lean_Meta_getLevel(v_binderType_1879_, v___y_1889_, v___y_1883_, v___y_1887_, v___y_1886_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
lean_inc(v_fst_1942_);
v___f_1954_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1954_, 0, v_fst_1942_);
lean_inc_ref(v_binderType_1879_);
lean_inc(v_binderName_1878_);
v___x_1955_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1878_, v_binderType_1879_, v___f_1954_, v___y_1885_, v___y_1888_, v___y_1884_, v___y_1889_, v___y_1883_, v___y_1887_, v___y_1886_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1984_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1984_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1984_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_expr_lift_loose_bvars(v_pRaw_1931_, v___x_1960_, v___x_1961_);
lean_dec_ref(v_pRaw_1931_);
v___x_1963_ = l_Lean_mkOr(v_snd_1943_, v___x_1962_);
v___x_1964_ = l_Lean_mkForall(v_fst_1938_, v___x_1948_, v_fst_1942_, v___x_1963_);
lean_inc_ref(v_binderType_1879_);
v___x_1965_ = l_Lean_mkForall(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_1967_ = lean_box(0);
if (v_isShared_1946_ == 0)
{
lean_ctor_set_tag(v___x_1945_, 1);
lean_ctor_set(v___x_1945_, 1, v___x_1967_);
lean_ctor_set(v___x_1945_, 0, v_a_1956_);
v___x_1969_ = v___x_1945_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1956_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 1);
lean_ctor_set(v___x_1940_, 1, v___x_1969_);
lean_ctor_set(v___x_1940_, 0, v_a_1953_);
v___x_1971_ = v___x_1940_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1953_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1972_ = l_Lean_mkConst(v___x_1966_, v___x_1971_);
v___x_1973_ = l_Lean_mkApp4(v___x_1972_, v_binderType_1879_, v_00_u03b2_1951_, v_p_1947_, v_q_1950_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1973_);
v___x_1975_ = v___x_1935_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1976_, 0, v___x_1965_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*2, v___y_1890_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1977_);
v___x_1979_ = v___x_1958_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_a_1953_);
lean_dec_ref(v_00_u03b2_1951_);
lean_dec_ref(v_q_1950_);
lean_dec_ref(v_p_1947_);
lean_del_object(v___x_1945_);
lean_dec(v_snd_1943_);
lean_dec(v_fst_1942_);
lean_del_object(v___x_1940_);
lean_dec(v_fst_1938_);
lean_del_object(v___x_1935_);
lean_dec_ref(v_pRaw_1931_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_1985_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1955_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1955_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_00_u03b2_1951_);
lean_dec_ref(v_q_1950_);
lean_dec_ref(v_p_1947_);
lean_del_object(v___x_1945_);
lean_dec(v_snd_1943_);
lean_dec(v_fst_1942_);
lean_del_object(v___x_1940_);
lean_dec(v_fst_1938_);
lean_del_object(v___x_1935_);
lean_dec_ref(v_pRaw_1931_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_1993_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1952_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1952_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v___x_1932_);
v___x_2004_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1931_);
lean_dec_ref(v_pRaw_1931_);
if (lean_obj_tag(v___x_2004_) == 1)
{
lean_object* v_val_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2075_; 
v_val_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2075_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_val_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2075_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_snd_2009_; lean_object* v_fst_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2074_; 
v_snd_2009_ = lean_ctor_get(v_val_2005_, 1);
v_fst_2010_ = lean_ctor_get(v_val_2005_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_val_2005_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2012_ = v_val_2005_;
v_isShared_2013_ = v_isSharedCheck_2074_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snd_2009_);
lean_inc(v_fst_2010_);
lean_dec(v_val_2005_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2074_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2073_; 
v_fst_2014_ = lean_ctor_get(v_snd_2009_, 0);
v_snd_2015_ = lean_ctor_get(v_snd_2009_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_snd_2009_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2017_ = v_snd_2009_;
v_isShared_2018_ = v_isSharedCheck_2073_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_inc(v_fst_2014_);
lean_dec(v_snd_2009_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2073_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_p_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v_q_2022_; lean_object* v_00_u03b2_2023_; lean_object* v___x_2024_; 
lean_inc_ref(v_pRaw_1930_);
lean_inc_ref_n(v_binderType_1879_, 4);
lean_inc_n(v_binderName_1878_, 3);
v_p_2019_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_pRaw_1930_);
v___x_2020_ = 0;
lean_inc(v_snd_2015_);
lean_inc_n(v_fst_2014_, 2);
lean_inc(v_fst_2010_);
v___x_2021_ = l_Lean_mkLambda(v_fst_2010_, v___x_2020_, v_fst_2014_, v_snd_2015_);
v_q_2022_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v___x_2021_);
v_00_u03b2_2023_ = l_Lean_mkLambda(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v_fst_2014_);
v___x_2024_ = l_Lean_Meta_getLevel(v_binderType_1879_, v___y_1889_, v___y_1883_, v___y_1887_, v___y_1886_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
lean_inc(v_fst_2014_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2026_, 0, v_fst_2014_);
lean_inc_ref(v_binderType_1879_);
lean_inc(v_binderName_1878_);
v___x_2027_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1878_, v_binderType_1879_, v___f_2026_, v___y_1885_, v___y_1888_, v___y_1884_, v___y_1889_, v___y_1883_, v___y_1887_, v___y_1886_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2056_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2056_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2056_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_expr_lift_loose_bvars(v_pRaw_1930_, v___x_2032_, v___x_2033_);
lean_dec_ref(v_pRaw_1930_);
v___x_2035_ = l_Lean_mkOr(v___x_2034_, v_snd_2015_);
v___x_2036_ = l_Lean_mkForall(v_fst_2010_, v___x_2020_, v_fst_2014_, v___x_2035_);
lean_inc_ref(v_binderType_1879_);
v___x_2037_ = l_Lean_mkForall(v_binderName_1878_, v_binderInfo_1881_, v_binderType_1879_, v___x_2036_);
v___x_2038_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__10));
v___x_2039_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 1);
lean_ctor_set(v___x_2017_, 1, v___x_2039_);
lean_ctor_set(v___x_2017_, 0, v_a_2028_);
v___x_2041_ = v___x_2017_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2028_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 1);
lean_ctor_set(v___x_2012_, 1, v___x_2041_);
lean_ctor_set(v___x_2012_, 0, v_a_2025_);
v___x_2043_ = v___x_2012_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2025_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = l_Lean_mkConst(v___x_2038_, v___x_2043_);
v___x_2045_ = l_Lean_mkApp4(v___x_2044_, v_binderType_1879_, v_00_u03b2_2023_, v_p_2019_, v_q_2022_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2045_);
v___x_2047_ = v___x_2007_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2048_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2048_, 0, v___x_2037_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*2, v___y_1890_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2049_);
v___x_2051_ = v___x_2030_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_2025_);
lean_dec_ref(v_00_u03b2_2023_);
lean_dec_ref(v_q_2022_);
lean_dec_ref(v_p_2019_);
lean_del_object(v___x_2017_);
lean_dec(v_snd_2015_);
lean_dec(v_fst_2014_);
lean_del_object(v___x_2012_);
lean_dec(v_fst_2010_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_pRaw_1930_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2057_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2027_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2027_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_00_u03b2_2023_);
lean_dec_ref(v_q_2022_);
lean_dec_ref(v_p_2019_);
lean_del_object(v___x_2017_);
lean_dec(v_snd_2015_);
lean_dec(v_fst_2014_);
lean_del_object(v___x_2012_);
lean_dec(v_fst_2010_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_pRaw_1930_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v_a_2065_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2024_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2024_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2004_);
lean_dec_ref(v_pRaw_1930_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
goto v___jp_1875_;
}
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref(v___x_1892_);
lean_dec_ref(v___x_1891_);
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
v___x_2076_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
}
v___jp_2078_:
{
uint8_t v___x_2086_; 
v___x_2086_ = l_Lean_Expr_isApp(v_body_1880_);
if (v___x_2086_ == 0)
{
v___y_1883_ = v___y_2083_;
v___y_1884_ = v___y_2081_;
v___y_1885_ = v___y_2079_;
v___y_1886_ = v___y_2085_;
v___y_1887_ = v___y_2084_;
v___y_1888_ = v___y_2080_;
v___y_1889_ = v___y_2082_;
v___y_1890_ = v___x_2086_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = l_Lean_Expr_getAppNumArgs(v_body_1880_);
v___x_2088_ = lean_unsigned_to_nat(2u);
v___x_2089_ = lean_nat_dec_eq(v___x_2087_, v___x_2088_);
lean_dec(v___x_2087_);
v___y_1883_ = v___y_2083_;
v___y_1884_ = v___y_2081_;
v___y_1885_ = v___y_2079_;
v___y_1886_ = v___y_2085_;
v___y_1887_ = v___y_2084_;
v___y_1888_ = v___y_2080_;
v___y_1889_ = v___y_2082_;
v___y_1890_ = v___x_2089_;
goto v___jp_1882_;
}
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_dec_ref(v_e_1866_);
v___x_2372_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
v___jp_1875_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* v_e_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Meta_Grind_simpForall(v_e_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* v_00_u03b1_2384_, lean_object* v_name_2385_, uint8_t v_bi_2386_, lean_object* v_type_2387_, lean_object* v_k_2388_, uint8_t v_kind_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_2385_, v_bi_2386_, v_type_2387_, v_k_2388_, v_kind_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2399_, lean_object* v_name_2400_, lean_object* v_bi_2401_, lean_object* v_type_2402_, lean_object* v_k_2403_, lean_object* v_kind_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_bi_boxed_2413_; uint8_t v_kind_boxed_2414_; lean_object* v_res_2415_; 
v_bi_boxed_2413_ = lean_unbox(v_bi_2401_);
v_kind_boxed_2414_ = lean_unbox(v_kind_2404_);
v_res_2415_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(v_00_u03b1_2399_, v_name_2400_, v_bi_boxed_2413_, v_type_2402_, v_k_2403_, v_kind_boxed_2414_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* v_00_u03b1_2416_, lean_object* v_name_2417_, lean_object* v_type_2418_, lean_object* v_k_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_2417_, v_type_2418_, v_k_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object* v_00_u03b1_2429_, lean_object* v_name_2430_, lean_object* v_type_2431_, lean_object* v_k_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(v_00_u03b1_2429_, v_name_2430_, v_type_2431_, v_k_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_));
v___x_2457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_));
v___x_2458_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___boxed), 9, 0);
v___x_2459_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2456_, v___x_2457_, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11____boxed(lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
return v_res_2461_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = lean_box(0);
v___x_2476_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__5));
v___x_2477_ = l_Lean_mkConst(v___x_2476_, v___x_2475_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* v_e_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = l_Lean_Expr_cleanupAnnotations(v_e_2493_);
v___x_2506_ = l_Lean_Expr_isApp(v___x_2505_);
if (v___x_2506_ == 0)
{
lean_dec_ref(v___x_2505_);
goto v___jp_2499_;
}
else
{
lean_object* v_arg_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v_arg_2507_ = lean_ctor_get(v___x_2505_, 1);
lean_inc_ref(v_arg_2507_);
v___x_2508_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2505_);
v___x_2509_ = l_Lean_Expr_isApp(v___x_2508_);
if (v___x_2509_ == 0)
{
lean_dec_ref(v___x_2508_);
lean_dec_ref(v_arg_2507_);
goto v___jp_2499_;
}
else
{
lean_object* v_arg_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_arg_2510_ = lean_ctor_get(v___x_2508_, 1);
lean_inc_ref(v_arg_2510_);
v___x_2511_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2508_);
v___x_2512_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2513_ = l_Lean_Expr_isConstOf(v___x_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_arg_2510_);
lean_dec_ref(v_arg_2507_);
goto v___jp_2499_;
}
else
{
if (lean_obj_tag(v_arg_2507_) == 6)
{
lean_object* v_binderName_2514_; lean_object* v_body_2515_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; uint8_t v___y_2584_; uint8_t v___y_2611_; uint8_t v___x_2640_; 
v_binderName_2514_ = lean_ctor_get(v_arg_2507_, 0);
lean_inc(v_binderName_2514_);
v_body_2515_ = lean_ctor_get(v_arg_2507_, 2);
lean_inc_ref(v_body_2515_);
lean_dec_ref(v_arg_2507_);
v___x_2640_ = l_Lean_Expr_isApp(v_body_2515_);
if (v___x_2640_ == 0)
{
v___y_2611_ = v___x_2640_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2641_ = l_Lean_Expr_getAppNumArgs(v_body_2515_);
v___x_2642_ = lean_unsigned_to_nat(2u);
v___x_2643_ = lean_nat_dec_eq(v___x_2641_, v___x_2642_);
lean_dec(v___x_2641_);
v___y_2611_ = v___x_2643_;
goto v___jp_2610_;
}
v___jp_2516_:
{
uint8_t v___x_2521_; 
v___x_2521_ = l_Lean_Expr_hasLooseBVars(v_body_2515_);
if (v___x_2521_ == 0)
{
if (v___x_2513_ == 0)
{
lean_dec_ref(v_body_2515_);
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_arg_2510_);
goto v___jp_2502_;
}
else
{
lean_object* v___x_2522_; 
lean_inc_ref(v_arg_2510_);
v___x_2522_ = l_Lean_Meta_isProp(v_arg_2510_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2571_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2571_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2571_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_unbox(v_a_2523_);
lean_dec(v_a_2523_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_del_object(v___x_2525_);
v___x_2528_ = l_Lean_Expr_constLevels_x21(v___x_2511_);
lean_dec_ref(v___x_2511_);
v___x_2529_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__1));
lean_inc(v___x_2528_);
v___x_2530_ = l_Lean_mkConst(v___x_2529_, v___x_2528_);
lean_inc_ref(v_arg_2510_);
v___x_2531_ = l_Lean_Expr_app___override(v___x_2530_, v_arg_2510_);
v___x_2532_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2531_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2553_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2553_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2553_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
if (lean_obj_tag(v_a_2533_) == 1)
{
lean_object* v_val_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2552_; 
v_val_2537_ = lean_ctor_get(v_a_2533_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_a_2533_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2539_ = v_a_2533_;
v_isShared_2540_ = v_isSharedCheck_2552_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_val_2537_);
lean_dec(v_a_2533_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2552_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2541_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__3));
v___x_2542_ = l_Lean_mkConst(v___x_2541_, v___x_2528_);
lean_inc_ref(v_body_2515_);
v___x_2543_ = l_Lean_mkApp3(v___x_2542_, v_arg_2510_, v_val_2537_, v_body_2515_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2543_);
v___x_2545_ = v___x_2539_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2546_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2546_, 0, v_body_2515_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
lean_ctor_set_uint8(v___x_2546_, sizeof(void*)*2, v___x_2513_);
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2547_);
v___x_2549_ = v___x_2535_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_del_object(v___x_2535_);
lean_dec(v_a_2533_);
lean_dec(v___x_2528_);
lean_dec_ref(v_body_2515_);
lean_dec_ref(v_arg_2510_);
goto v___jp_2502_;
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v___x_2528_);
lean_dec_ref(v_body_2515_);
lean_dec_ref(v_arg_2510_);
v_a_2554_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2532_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2532_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2569_; 
lean_dec_ref(v___x_2511_);
lean_inc_ref(v_body_2515_);
lean_inc_ref(v_arg_2510_);
v___x_2562_ = l_Lean_mkAnd(v_arg_2510_, v_body_2515_);
v___x_2563_ = lean_obj_once(&l_Lean_Meta_Grind_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6);
v___x_2564_ = l_Lean_mkAppB(v___x_2563_, v_arg_2510_, v_body_2515_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2562_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*2, v___x_2513_);
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2567_);
v___x_2569_ = v___x_2525_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v_body_2515_);
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_arg_2510_);
v_a_2572_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2522_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2522_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_dec_ref(v_body_2515_);
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_arg_2510_);
goto v___jp_2502_;
}
}
v___jp_2580_:
{
if (v___y_2584_ == 0)
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_Expr_hasLooseBVars(v___y_2582_);
if (v___x_2585_ == 0)
{
if (v___y_2581_ == 0)
{
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v_binderName_2514_);
v___y_2517_ = v_a_2494_;
v___y_2518_ = v_a_2495_;
v___y_2519_ = v_a_2496_;
v___y_2520_ = v_a_2497_;
goto v___jp_2516_;
}
else
{
uint8_t v___x_2586_; lean_object* v_p_2587_; lean_object* v___x_2588_; lean_object* v_expr_2589_; lean_object* v_u_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec_ref(v_body_2515_);
v___x_2586_ = 0;
lean_inc_ref_n(v_arg_2510_, 2);
v_p_2587_ = l_Lean_mkLambda(v_binderName_2514_, v___x_2586_, v_arg_2510_, v___y_2583_);
lean_inc_ref(v_p_2587_);
lean_inc_ref(v___x_2511_);
v___x_2588_ = l_Lean_mkAppB(v___x_2511_, v_arg_2510_, v_p_2587_);
lean_inc_ref(v___y_2582_);
v_expr_2589_ = l_Lean_mkAnd(v___x_2588_, v___y_2582_);
v_u_2590_ = l_Lean_Expr_constLevels_x21(v___x_2511_);
lean_dec_ref(v___x_2511_);
v___x_2591_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__8));
v___x_2592_ = l_Lean_mkConst(v___x_2591_, v_u_2590_);
v___x_2593_ = l_Lean_mkApp3(v___x_2592_, v_arg_2510_, v_p_2587_, v___y_2582_);
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2595_, 0, v_expr_2589_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*2, v___x_2513_);
v___x_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
else
{
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v_binderName_2514_);
v___y_2517_ = v_a_2494_;
v___y_2518_ = v_a_2495_;
v___y_2519_ = v_a_2496_;
v___y_2520_ = v_a_2497_;
goto v___jp_2516_;
}
}
else
{
uint8_t v___x_2598_; lean_object* v_p_2599_; lean_object* v___x_2600_; lean_object* v_expr_2601_; lean_object* v_u_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec_ref(v_body_2515_);
v___x_2598_ = 0;
lean_inc_ref_n(v_arg_2510_, 2);
v_p_2599_ = l_Lean_mkLambda(v_binderName_2514_, v___x_2598_, v_arg_2510_, v___y_2582_);
lean_inc_ref(v_p_2599_);
lean_inc_ref(v___x_2511_);
v___x_2600_ = l_Lean_mkAppB(v___x_2511_, v_arg_2510_, v_p_2599_);
lean_inc_ref(v___y_2583_);
v_expr_2601_ = l_Lean_mkAnd(v___y_2583_, v___x_2600_);
v_u_2602_ = l_Lean_Expr_constLevels_x21(v___x_2511_);
lean_dec_ref(v___x_2511_);
v___x_2603_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__10));
v___x_2604_ = l_Lean_mkConst(v___x_2603_, v_u_2602_);
v___x_2605_ = l_Lean_mkApp3(v___x_2604_, v_arg_2510_, v_p_2599_, v___y_2583_);
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2607_, 0, v_expr_2601_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_ctor_set_uint8(v___x_2607_, sizeof(void*)*2, v___x_2513_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
return v___x_2609_;
}
}
v___jp_2610_:
{
if (v___y_2611_ == 0)
{
lean_dec(v_binderName_2514_);
v___y_2517_ = v_a_2494_;
v___y_2518_ = v_a_2495_;
v___y_2519_ = v_a_2496_;
v___y_2520_ = v_a_2497_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = l_Lean_Expr_appFn_x21(v_body_2515_);
v___x_2613_ = l_Lean_Expr_appFn_x21(v___x_2612_);
if (lean_obj_tag(v___x_2613_) == 4)
{
lean_object* v_declName_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_declName_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_declName_2614_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_2616_ = lean_name_eq(v_declName_2614_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_2618_ = lean_name_eq(v_declName_2614_, v___x_2617_);
lean_dec(v_declName_2614_);
if (v___x_2618_ == 0)
{
lean_dec_ref(v___x_2612_);
lean_dec(v_binderName_2514_);
v___y_2517_ = v_a_2494_;
v___y_2518_ = v_a_2495_;
v___y_2519_ = v_a_2496_;
v___y_2520_ = v_a_2497_;
goto v___jp_2516_;
}
else
{
lean_object* v_b_2619_; lean_object* v_b_2620_; uint8_t v___x_2621_; 
v_b_2619_ = l_Lean_Expr_appArg_x21(v___x_2612_);
lean_dec_ref(v___x_2612_);
v_b_2620_ = l_Lean_Expr_appArg_x21(v_body_2515_);
v___x_2621_ = l_Lean_Expr_hasLooseBVars(v_b_2619_);
if (v___x_2621_ == 0)
{
v___y_2581_ = v___x_2618_;
v___y_2582_ = v_b_2620_;
v___y_2583_ = v_b_2619_;
v___y_2584_ = v___x_2618_;
goto v___jp_2580_;
}
else
{
v___y_2581_ = v___x_2618_;
v___y_2582_ = v_b_2620_;
v___y_2583_ = v_b_2619_;
v___y_2584_ = v___x_2616_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v_pRaw_2622_; lean_object* v_qRaw_2623_; uint8_t v___x_2624_; lean_object* v_p_2625_; lean_object* v_q_2626_; lean_object* v_u_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_expr_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v_declName_2614_);
v_pRaw_2622_ = l_Lean_Expr_appArg_x21(v___x_2612_);
lean_dec_ref(v___x_2612_);
v_qRaw_2623_ = l_Lean_Expr_appArg_x21(v_body_2515_);
lean_dec_ref(v_body_2515_);
v___x_2624_ = 0;
lean_inc_ref_n(v_arg_2510_, 4);
lean_inc(v_binderName_2514_);
v_p_2625_ = l_Lean_mkLambda(v_binderName_2514_, v___x_2624_, v_arg_2510_, v_pRaw_2622_);
v_q_2626_ = l_Lean_mkLambda(v_binderName_2514_, v___x_2624_, v_arg_2510_, v_qRaw_2623_);
v_u_2627_ = l_Lean_Expr_constLevels_x21(v___x_2511_);
lean_inc_ref(v_p_2625_);
lean_inc_ref(v___x_2511_);
v___x_2628_ = l_Lean_mkAppB(v___x_2511_, v_arg_2510_, v_p_2625_);
lean_inc_ref(v_q_2626_);
v___x_2629_ = l_Lean_mkAppB(v___x_2511_, v_arg_2510_, v_q_2626_);
v_expr_2630_ = l_Lean_mkOr(v___x_2628_, v___x_2629_);
v___x_2631_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__12));
v___x_2632_ = l_Lean_mkConst(v___x_2631_, v_u_2627_);
v___x_2633_ = l_Lean_mkApp3(v___x_2632_, v_arg_2510_, v_p_2625_, v_q_2626_);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
v___x_2635_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2635_, 0, v_expr_2630_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*2, v___x_2513_);
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec_ref(v___x_2613_);
lean_dec_ref(v___x_2612_);
lean_dec_ref(v_body_2515_);
lean_dec(v_binderName_2514_);
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_arg_2510_);
v___x_2638_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
}
}
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec_ref(v___x_2511_);
lean_dec_ref(v_arg_2510_);
lean_dec_ref(v_arg_2507_);
v___x_2644_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
}
}
}
v___jp_2499_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
v___jp_2502_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object* v_e_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* v_e_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2653_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* v_e_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Meta_Grind_simpExists(v_e_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_));
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_));
v___x_2692_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
v___x_2693_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2690_, v___x_2691_, v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10____boxed(lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* v_s_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_));
v___x_2701_ = 1;
v___x_2702_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2696_, v___x_2700_, v___x_2701_, v_a_2697_, v_a_2698_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_));
v___x_2705_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2703_, v___x_2704_, v___x_2701_, v_a_2697_, v_a_2698_);
return v___x_2705_;
}
else
{
return v___x_2702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object* v_s_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Meta_Grind_addForallSimproc(v_s_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
return v_res_2710_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
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
