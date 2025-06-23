// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Internalize Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.EqResolution
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__7;
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__3;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__4;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__14;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__1;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__6;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__0;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__12;
lean_object* l_Lean_Meta_Grind_pushEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__8;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__7;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__0;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__13;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp___hyg_2884_(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__11;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_imp_eq_true", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_eq_of_eq_true_right", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_eq_of_eq_true_left", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_eq_of_eq_false_left", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_45; uint8_t x_74; lean_object* x_75; lean_object* x_100; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_3, x_4, x_12);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
uint8_t x_131; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_128, 0);
lean_dec(x_132);
x_133 = lean_box(0);
lean_ctor_set(x_128, 0, x_133);
return x_128;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_dec(x_128);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_dec(x_128);
lean_inc(x_2);
x_138 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_6, x_10, x_11, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
x_100 = x_138;
goto block_127;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_142 = l_Lean_Meta_isProp(x_3, x_8, x_9, x_10, x_11, x_141);
x_100 = x_142;
goto block_127;
}
}
else
{
x_100 = x_138;
goto block_127;
}
}
block_44:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc(x_2);
x_30 = l_Lean_mkApp4(x_29, x_2, x_3, x_24, x_27);
x_31 = l_Lean_Meta_Grind_pushEqFalse(x_2, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
block_73:
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
lean_inc(x_3);
x_49 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_6, x_10, x_11, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
x_13 = x_49;
goto block_44;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
lean_inc(x_1);
x_53 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_6, x_10, x_11, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
x_13 = x_53;
goto block_44;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_57 = l_Lean_Meta_isProp(x_2, x_8, x_9, x_10, x_11, x_56);
x_13 = x_57;
goto block_44;
}
}
else
{
x_13 = x_53;
goto block_44;
}
}
}
else
{
x_13 = x_49;
goto block_44;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec(x_45);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
x_63 = l_Lean_mkApp3(x_62, x_2, x_3, x_60);
x_64 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_59);
if (x_65 == 0)
{
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_45);
if (x_69 == 0)
{
return x_45;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_45, 0);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_45);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_99:
{
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_inc(x_3);
x_79 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_6, x_10, x_11, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
x_45 = x_79;
goto block_73;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_83 = l_Lean_Meta_isProp(x_2, x_8, x_9, x_10, x_11, x_82);
x_45 = x_83;
goto block_73;
}
}
else
{
x_45 = x_79;
goto block_73;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_85 = l_Lean_Meta_Grind_mkEqTrueProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
lean_inc(x_3);
x_89 = l_Lean_mkApp3(x_88, x_2, x_3, x_86);
x_90 = l_Lean_Meta_Grind_pushEqCore(x_1, x_3, x_89, x_74, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_87);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_85);
if (x_91 == 0)
{
return x_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_85, 0);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_85);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_75);
if (x_95 == 0)
{
return x_75;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_75, 0);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_75);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
block_127:
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
lean_inc(x_2);
x_104 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_6, x_10, x_11, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = lean_unbox(x_101);
lean_dec(x_101);
x_74 = x_107;
x_75 = x_104;
goto block_99;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_dec(x_104);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_109 = l_Lean_Meta_isProp(x_3, x_8, x_9, x_10, x_11, x_108);
x_110 = lean_unbox(x_101);
lean_dec(x_101);
x_74 = x_110;
x_75 = x_109;
goto block_99;
}
}
else
{
uint8_t x_111; 
x_111 = lean_unbox(x_101);
lean_dec(x_101);
x_74 = x_111;
x_75 = x_104;
goto block_99;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_101);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_dec(x_100);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_113 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
x_117 = l_Lean_mkApp3(x_116, x_2, x_3, x_114);
x_118 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_115);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_113);
if (x_119 == 0)
{
return x_113;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_113, 0);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_113);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_100);
if (x_123 == 0)
{
return x_100;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_100, 0);
x_125 = lean_ctor_get(x_100, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_100);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_propagator", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__0;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropUp___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forallPropagator", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__5;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp___closed__4;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("q': ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" for", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isEqTrue, ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_40 = l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
x_234 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_40, x_8, x_10);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_8;
x_174 = x_9;
x_175 = x_237;
goto block_233;
}
else
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_234);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_234, 1);
x_240 = lean_ctor_get(x_234, 0);
lean_dec(x_240);
x_241 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_239);
if (lean_obj_tag(x_241) == 0)
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_241, 1);
x_244 = lean_ctor_get(x_241, 0);
lean_dec(x_244);
x_245 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc(x_1);
x_246 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_241, 7);
lean_ctor_set(x_241, 1, x_246);
lean_ctor_set(x_241, 0, x_245);
lean_ctor_set_tag(x_234, 7);
lean_ctor_set(x_234, 1, x_245);
lean_ctor_set(x_234, 0, x_241);
x_247 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_234, x_6, x_7, x_8, x_9, x_243);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_8;
x_174 = x_9;
x_175 = x_248;
goto block_233;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_241, 1);
lean_inc(x_249);
lean_dec(x_241);
x_250 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc(x_1);
x_251 = l_Lean_MessageData_ofExpr(x_1);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set_tag(x_234, 7);
lean_ctor_set(x_234, 1, x_250);
lean_ctor_set(x_234, 0, x_252);
x_253 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_234, x_6, x_7, x_8, x_9, x_249);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_8;
x_174 = x_9;
x_175 = x_254;
goto block_233;
}
}
else
{
lean_free_object(x_234);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_241;
}
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_234, 1);
lean_inc(x_255);
lean_dec(x_234);
x_256 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
x_259 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc(x_1);
x_260 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_258)) {
 x_261 = lean_alloc_ctor(7, 2, 0);
} else {
 x_261 = x_258;
 lean_ctor_set_tag(x_261, 7);
}
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_259);
x_263 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_262, x_6, x_7, x_8, x_9, x_257);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_8;
x_174 = x_9;
x_175 = x_264;
goto block_233;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_256;
}
}
}
block_39:
{
lean_object* x_29; 
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_29 = l_Lean_Meta_Simp_Result_getProof(x_18, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
lean_inc(x_17);
x_33 = l_Lean_mkApp5(x_32, x_12, x_15, x_17, x_16, x_30);
x_34 = l_Lean_Meta_Grind_pushEqCore(x_1, x_17, x_33, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_31);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_166:
{
lean_object* x_51; 
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_12);
x_51 = l_Lean_Meta_Grind_mkEqTrueProof(x_12, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
lean_inc(x_12);
x_54 = l_Lean_Meta_mkOfEqTrueCore(x_12, x_52);
x_55 = lean_expr_instantiate1(x_13, x_54);
lean_dec(x_54);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_56 = l_Lean_Meta_Grind_preprocess(x_55, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_1);
x_59 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_42, x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_box(0);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_63);
x_65 = lean_grind_internalize(x_63, x_61, x_64, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_62);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_65, 1);
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_40, x_48, x_67);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_12);
x_73 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_74 = lean_unbox(x_71);
lean_dec(x_71);
if (x_74 == 0)
{
lean_free_object(x_69);
lean_free_object(x_65);
lean_free_object(x_59);
x_15 = x_73;
x_16 = x_52;
x_17 = x_63;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_72;
goto block_39;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_Meta_Grind_updateLastTag(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_72);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_75, 1);
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc(x_63);
x_80 = l_Lean_MessageData_ofExpr(x_63);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_80);
lean_ctor_set(x_75, 0, x_79);
x_81 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_81);
lean_ctor_set(x_69, 0, x_75);
lean_inc(x_1);
x_82 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_82);
lean_ctor_set(x_65, 0, x_69);
x_83 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_83);
lean_ctor_set(x_59, 0, x_65);
x_84 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_59, x_46, x_47, x_48, x_49, x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_15 = x_73;
x_16 = x_52;
x_17 = x_63;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_85;
goto block_39;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_dec(x_75);
x_87 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc(x_63);
x_88 = l_Lean_MessageData_ofExpr(x_63);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_90);
lean_ctor_set(x_69, 0, x_89);
lean_inc(x_1);
x_91 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_91);
lean_ctor_set(x_65, 0, x_69);
x_92 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_92);
lean_ctor_set(x_59, 0, x_65);
x_93 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_59, x_46, x_47, x_48, x_49, x_86);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_15 = x_73;
x_16 = x_52;
x_17 = x_63;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_94;
goto block_39;
}
}
else
{
lean_dec(x_73);
lean_free_object(x_69);
lean_free_object(x_65);
lean_dec(x_63);
lean_free_object(x_59);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_1);
return x_75;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_69, 0);
x_96 = lean_ctor_get(x_69, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_69);
lean_inc(x_12);
x_97 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_98 = lean_unbox(x_95);
lean_dec(x_95);
if (x_98 == 0)
{
lean_free_object(x_65);
lean_free_object(x_59);
x_15 = x_97;
x_16 = x_52;
x_17 = x_63;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_96;
goto block_39;
}
else
{
lean_object* x_99; 
x_99 = l_Lean_Meta_Grind_updateLastTag(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_96);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc(x_63);
x_103 = l_Lean_MessageData_ofExpr(x_63);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_101;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_1);
x_107 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_107);
lean_ctor_set(x_65, 0, x_106);
x_108 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_108);
lean_ctor_set(x_59, 0, x_65);
x_109 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_59, x_46, x_47, x_48, x_49, x_100);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_15 = x_97;
x_16 = x_52;
x_17 = x_63;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_110;
goto block_39;
}
else
{
lean_dec(x_97);
lean_free_object(x_65);
lean_dec(x_63);
lean_free_object(x_59);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_1);
return x_99;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_111 = lean_ctor_get(x_65, 1);
lean_inc(x_111);
lean_dec(x_65);
x_112 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_40, x_48, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
lean_inc(x_12);
x_116 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_117 = lean_unbox(x_113);
lean_dec(x_113);
if (x_117 == 0)
{
lean_dec(x_115);
lean_free_object(x_59);
x_15 = x_116;
x_16 = x_52;
x_17 = x_63;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_114;
goto block_39;
}
else
{
lean_object* x_118; 
x_118 = l_Lean_Meta_Grind_updateLastTag(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_114);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc(x_63);
x_122 = l_Lean_MessageData_ofExpr(x_63);
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_120;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
if (lean_is_scalar(x_115)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_115;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
lean_inc(x_1);
x_126 = l_Lean_indentExpr(x_1);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_128);
lean_ctor_set(x_59, 0, x_127);
x_129 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_59, x_46, x_47, x_48, x_49, x_119);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_15 = x_116;
x_16 = x_52;
x_17 = x_63;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_130;
goto block_39;
}
else
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_63);
lean_free_object(x_59);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_1);
return x_118;
}
}
}
}
else
{
lean_dec(x_63);
lean_free_object(x_59);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_65;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_59, 0);
x_132 = lean_ctor_get(x_59, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_59);
x_133 = lean_ctor_get(x_57, 0);
lean_inc(x_133);
x_134 = lean_box(0);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_133);
x_135 = lean_grind_internalize(x_133, x_131, x_134, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_132);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_40, x_48, x_136);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
lean_inc(x_12);
x_142 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_143 = lean_unbox(x_139);
lean_dec(x_139);
if (x_143 == 0)
{
lean_dec(x_141);
lean_dec(x_137);
x_15 = x_142;
x_16 = x_52;
x_17 = x_133;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_140;
goto block_39;
}
else
{
lean_object* x_144; 
x_144 = l_Lean_Meta_Grind_updateLastTag(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
x_147 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc(x_133);
x_148 = l_Lean_MessageData_ofExpr(x_133);
if (lean_is_scalar(x_146)) {
 x_149 = lean_alloc_ctor(7, 2, 0);
} else {
 x_149 = x_146;
 lean_ctor_set_tag(x_149, 7);
}
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
if (lean_is_scalar(x_141)) {
 x_151 = lean_alloc_ctor(7, 2, 0);
} else {
 x_151 = x_141;
 lean_ctor_set_tag(x_151, 7);
}
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_1);
x_152 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_137)) {
 x_153 = lean_alloc_ctor(7, 2, 0);
} else {
 x_153 = x_137;
 lean_ctor_set_tag(x_153, 7);
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_155, x_46, x_47, x_48, x_49, x_145);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_15 = x_142;
x_16 = x_52;
x_17 = x_133;
x_18 = x_57;
x_19 = x_41;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_157;
goto block_39;
}
else
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_133);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_1);
return x_144;
}
}
}
else
{
lean_dec(x_133);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_135;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_56);
if (x_158 == 0)
{
return x_56;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_56, 0);
x_160 = lean_ctor_get(x_56, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_56);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_51);
if (x_162 == 0)
{
return x_51;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_51, 0);
x_164 = lean_ctor_get(x_51, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_51);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
block_233:
{
uint8_t x_176; 
x_176 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_11);
x_177 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_12, x_13, x_167, x_168, x_169, x_170, x_171, x_172, x_173, x_174, x_175);
return x_177;
}
else
{
lean_object* x_178; 
lean_inc(x_12);
x_178 = l_Lean_Meta_Grind_isEqTrue___redArg(x_12, x_167, x_169, x_173, x_174, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_unbox(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
uint8_t x_181; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_178);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_178, 0);
lean_dec(x_182);
x_183 = lean_box(0);
lean_ctor_set(x_178, 0, x_183);
return x_178;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
lean_dec(x_178);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_178, 1);
lean_inc(x_187);
lean_dec(x_178);
x_188 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_40, x_173, x_187);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_ctor_get(x_188, 1);
x_192 = lean_box(0);
x_193 = lean_unbox(x_190);
lean_dec(x_190);
if (x_193 == 0)
{
uint8_t x_194; 
lean_free_object(x_188);
x_194 = lean_unbox(x_192);
x_41 = x_194;
x_42 = x_167;
x_43 = x_168;
x_44 = x_169;
x_45 = x_170;
x_46 = x_171;
x_47 = x_172;
x_48 = x_173;
x_49 = x_174;
x_50 = x_191;
goto block_166;
}
else
{
lean_object* x_195; 
x_195 = l_Lean_Meta_Grind_updateLastTag(x_167, x_168, x_169, x_170, x_171, x_172, x_173, x_174, x_191);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_197 = lean_ctor_get(x_195, 1);
x_198 = lean_ctor_get(x_195, 0);
lean_dec(x_198);
x_199 = l_Lean_Meta_Grind_propagateForallPropUp___closed__14;
lean_inc(x_1);
x_200 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_195, 7);
lean_ctor_set(x_195, 1, x_200);
lean_ctor_set(x_195, 0, x_199);
x_201 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_ctor_set_tag(x_188, 7);
lean_ctor_set(x_188, 1, x_201);
lean_ctor_set(x_188, 0, x_195);
x_202 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_188, x_171, x_172, x_173, x_174, x_197);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_unbox(x_192);
x_41 = x_204;
x_42 = x_167;
x_43 = x_168;
x_44 = x_169;
x_45 = x_170;
x_46 = x_171;
x_47 = x_172;
x_48 = x_173;
x_49 = x_174;
x_50 = x_203;
goto block_166;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_205 = lean_ctor_get(x_195, 1);
lean_inc(x_205);
lean_dec(x_195);
x_206 = l_Lean_Meta_Grind_propagateForallPropUp___closed__14;
lean_inc(x_1);
x_207 = l_Lean_MessageData_ofExpr(x_1);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_ctor_set_tag(x_188, 7);
lean_ctor_set(x_188, 1, x_209);
lean_ctor_set(x_188, 0, x_208);
x_210 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_188, x_171, x_172, x_173, x_174, x_205);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_unbox(x_192);
x_41 = x_212;
x_42 = x_167;
x_43 = x_168;
x_44 = x_169;
x_45 = x_170;
x_46 = x_171;
x_47 = x_172;
x_48 = x_173;
x_49 = x_174;
x_50 = x_211;
goto block_166;
}
}
else
{
lean_free_object(x_188);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_195;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_188, 0);
x_214 = lean_ctor_get(x_188, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_188);
x_215 = lean_box(0);
x_216 = lean_unbox(x_213);
lean_dec(x_213);
if (x_216 == 0)
{
uint8_t x_217; 
x_217 = lean_unbox(x_215);
x_41 = x_217;
x_42 = x_167;
x_43 = x_168;
x_44 = x_169;
x_45 = x_170;
x_46 = x_171;
x_47 = x_172;
x_48 = x_173;
x_49 = x_174;
x_50 = x_214;
goto block_166;
}
else
{
lean_object* x_218; 
x_218 = l_Lean_Meta_Grind_updateLastTag(x_167, x_168, x_169, x_170, x_171, x_172, x_173, x_174, x_214);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
x_221 = l_Lean_Meta_Grind_propagateForallPropUp___closed__14;
lean_inc(x_1);
x_222 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_220)) {
 x_223 = lean_alloc_ctor(7, 2, 0);
} else {
 x_223 = x_220;
 lean_ctor_set_tag(x_223, 7);
}
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
x_225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_40, x_225, x_171, x_172, x_173, x_174, x_219);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_unbox(x_215);
x_41 = x_228;
x_42 = x_167;
x_43 = x_168;
x_44 = x_169;
x_45 = x_170;
x_46 = x_171;
x_47 = x_172;
x_48 = x_173;
x_49 = x_174;
x_50 = x_227;
goto block_166;
}
else
{
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_218;
}
}
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_178);
if (x_229 == 0)
{
return x_178;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_178, 0);
x_231 = lean_ctor_get(x_178, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_178);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
}
else
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = lean_box(0);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_10);
return x_266;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1;
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_box(0);
return x_15;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_1, x_9, x_2, x_3, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_24 = l_Lean_Exception_isInterrupt(x_14);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_14);
lean_dec(x_14);
x_16 = x_25;
goto block_23;
}
else
{
lean_dec(x_14);
x_16 = x_24;
goto block_23;
}
block_23:
{
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
else
{
lean_dec(x_15);
return x_13;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create E-match local theorem for", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(8, 0, 1);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("local", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_126; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_126 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_163; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_127);
x_163 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(x_127);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = lean_st_ref_take(x_2, x_128);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 12);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = !lean_is_exclusive(x_165);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_165, 12);
lean_dec(x_169);
x_170 = !lean_is_exclusive(x_166);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_166, 7);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_add(x_171, x_172);
lean_ctor_set(x_166, 7, x_173);
x_174 = lean_st_ref_set(x_2, x_165, x_167);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4;
x_177 = lean_name_append_index_after(x_176, x_171);
x_178 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_129 = x_178;
x_130 = x_2;
x_131 = x_3;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = x_175;
goto block_162;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_179 = lean_ctor_get(x_166, 0);
x_180 = lean_ctor_get(x_166, 1);
x_181 = lean_ctor_get(x_166, 2);
x_182 = lean_ctor_get(x_166, 3);
x_183 = lean_ctor_get(x_166, 4);
x_184 = lean_ctor_get(x_166, 5);
x_185 = lean_ctor_get(x_166, 6);
x_186 = lean_ctor_get(x_166, 7);
x_187 = lean_ctor_get(x_166, 8);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_166);
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_nat_add(x_186, x_188);
x_190 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_190, 0, x_179);
lean_ctor_set(x_190, 1, x_180);
lean_ctor_set(x_190, 2, x_181);
lean_ctor_set(x_190, 3, x_182);
lean_ctor_set(x_190, 4, x_183);
lean_ctor_set(x_190, 5, x_184);
lean_ctor_set(x_190, 6, x_185);
lean_ctor_set(x_190, 7, x_189);
lean_ctor_set(x_190, 8, x_187);
lean_ctor_set(x_165, 12, x_190);
x_191 = lean_st_ref_set(x_2, x_165, x_167);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4;
x_194 = lean_name_append_index_after(x_193, x_186);
x_195 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_129 = x_195;
x_130 = x_2;
x_131 = x_3;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = x_192;
goto block_162;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_196 = lean_ctor_get(x_165, 0);
x_197 = lean_ctor_get(x_165, 1);
x_198 = lean_ctor_get(x_165, 2);
x_199 = lean_ctor_get(x_165, 3);
x_200 = lean_ctor_get(x_165, 4);
x_201 = lean_ctor_get(x_165, 5);
x_202 = lean_ctor_get(x_165, 6);
x_203 = lean_ctor_get(x_165, 7);
x_204 = lean_ctor_get_uint8(x_165, sizeof(void*)*16);
x_205 = lean_ctor_get(x_165, 8);
x_206 = lean_ctor_get(x_165, 9);
x_207 = lean_ctor_get(x_165, 10);
x_208 = lean_ctor_get(x_165, 11);
x_209 = lean_ctor_get(x_165, 13);
x_210 = lean_ctor_get(x_165, 14);
x_211 = lean_ctor_get(x_165, 15);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_165);
x_212 = lean_ctor_get(x_166, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_166, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_166, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_166, 3);
lean_inc(x_215);
x_216 = lean_ctor_get(x_166, 4);
lean_inc(x_216);
x_217 = lean_ctor_get(x_166, 5);
lean_inc(x_217);
x_218 = lean_ctor_get(x_166, 6);
lean_inc(x_218);
x_219 = lean_ctor_get(x_166, 7);
lean_inc(x_219);
x_220 = lean_ctor_get(x_166, 8);
lean_inc(x_220);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 lean_ctor_release(x_166, 5);
 lean_ctor_release(x_166, 6);
 lean_ctor_release(x_166, 7);
 lean_ctor_release(x_166, 8);
 x_221 = x_166;
} else {
 lean_dec_ref(x_166);
 x_221 = lean_box(0);
}
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_nat_add(x_219, x_222);
if (lean_is_scalar(x_221)) {
 x_224 = lean_alloc_ctor(0, 9, 0);
} else {
 x_224 = x_221;
}
lean_ctor_set(x_224, 0, x_212);
lean_ctor_set(x_224, 1, x_213);
lean_ctor_set(x_224, 2, x_214);
lean_ctor_set(x_224, 3, x_215);
lean_ctor_set(x_224, 4, x_216);
lean_ctor_set(x_224, 5, x_217);
lean_ctor_set(x_224, 6, x_218);
lean_ctor_set(x_224, 7, x_223);
lean_ctor_set(x_224, 8, x_220);
x_225 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_225, 0, x_196);
lean_ctor_set(x_225, 1, x_197);
lean_ctor_set(x_225, 2, x_198);
lean_ctor_set(x_225, 3, x_199);
lean_ctor_set(x_225, 4, x_200);
lean_ctor_set(x_225, 5, x_201);
lean_ctor_set(x_225, 6, x_202);
lean_ctor_set(x_225, 7, x_203);
lean_ctor_set(x_225, 8, x_205);
lean_ctor_set(x_225, 9, x_206);
lean_ctor_set(x_225, 10, x_207);
lean_ctor_set(x_225, 11, x_208);
lean_ctor_set(x_225, 12, x_224);
lean_ctor_set(x_225, 13, x_209);
lean_ctor_set(x_225, 14, x_210);
lean_ctor_set(x_225, 15, x_211);
lean_ctor_set_uint8(x_225, sizeof(void*)*16, x_204);
x_226 = lean_st_ref_set(x_2, x_225, x_167);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4;
x_229 = lean_name_append_index_after(x_228, x_219);
x_230 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_129 = x_230;
x_130 = x_2;
x_131 = x_3;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = x_227;
goto block_162;
}
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_163);
if (x_231 == 0)
{
x_129 = x_163;
x_130 = x_2;
x_131 = x_3;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = x_128;
goto block_162;
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_163, 0);
lean_inc(x_232);
lean_dec(x_163);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_129 = x_233;
x_130 = x_2;
x_131 = x_3;
x_132 = x_4;
x_133 = x_5;
x_134 = x_6;
x_135 = x_7;
x_136 = x_8;
x_137 = x_9;
x_138 = x_128;
goto block_162;
}
}
block_162:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_139 = lean_st_ref_get(x_130, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_1);
x_142 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_130, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_1);
x_145 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_127);
x_146 = lean_box(6);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_145);
lean_inc(x_129);
x_147 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_129, x_145, x_146, x_134, x_135, x_136, x_137, x_144);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_140, 12);
lean_inc(x_148);
lean_dec(x_140);
x_149 = lean_ctor_get(x_148, 3);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_ctor_get(x_149, 2);
lean_inc(x_152);
lean_dec(x_149);
x_100 = x_152;
x_101 = x_145;
x_102 = x_143;
x_103 = x_129;
x_104 = x_130;
x_105 = x_131;
x_106 = x_132;
x_107 = x_133;
x_108 = x_134;
x_109 = x_135;
x_110 = x_136;
x_111 = x_137;
x_112 = x_151;
goto block_125;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_dec(x_147);
x_154 = lean_ctor_get(x_149, 2);
lean_inc(x_154);
lean_dec(x_149);
x_155 = lean_ctor_get(x_150, 0);
lean_inc(x_155);
lean_dec(x_150);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_143);
x_156 = l_Lean_Meta_Grind_activateTheorem(x_155, x_143, x_130, x_131, x_132, x_133, x_134, x_135, x_136, x_137, x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_100 = x_154;
x_101 = x_145;
x_102 = x_143;
x_103 = x_129;
x_104 = x_130;
x_105 = x_131;
x_106 = x_132;
x_107 = x_133;
x_108 = x_134;
x_109 = x_135;
x_110 = x_136;
x_111 = x_137;
x_112 = x_157;
goto block_125;
}
else
{
lean_dec(x_154);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_1);
return x_156;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_147);
if (x_158 == 0)
{
return x_147;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_147, 0);
x_160 = lean_ctor_get(x_147, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_147);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_126);
if (x_234 == 0)
{
return x_126;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_126, 0);
x_236 = lean_ctor_get(x_126, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_126);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
block_66:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_st_ref_get(x_12, x_20);
lean_dec(x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 12);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_nat_dec_eq(x_28, x_11);
lean_dec(x_11);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_free_object(x_21);
x_31 = l_Lean_Meta_Grind_getConfig___redArg(x_14, x_26);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*6 + 11);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_42 = l_Lean_indentExpr(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_Grind_reportIssue(x_45, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_40);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_dec(x_21);
x_48 = lean_ctor_get(x_24, 2);
lean_inc(x_48);
lean_dec(x_24);
x_49 = lean_nat_dec_eq(x_48, x_11);
lean_dec(x_11);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Meta_Grind_getConfig___redArg(x_14, x_47);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*6 + 11);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_61 = l_Lean_indentExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_Grind_reportIssue(x_64, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_59);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_65;
}
}
}
}
block_99:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_80 = lean_st_ref_get(x_71, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 12);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_ctor_get(x_83, 2);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_nat_dec_eq(x_85, x_68);
lean_dec(x_85);
if (x_86 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
x_11 = x_68;
x_12 = x_71;
x_13 = x_72;
x_14 = x_73;
x_15 = x_74;
x_16 = x_75;
x_17 = x_76;
x_18 = x_77;
x_19 = x_78;
x_20 = x_84;
goto block_66;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2;
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
x_88 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_70, x_67, x_87, x_75, x_76, x_77, x_78, x_84);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
lean_dec(x_69);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_11 = x_68;
x_12 = x_71;
x_13 = x_72;
x_14 = x_73;
x_15 = x_74;
x_16 = x_75;
x_17 = x_76;
x_18 = x_77;
x_19 = x_78;
x_20 = x_90;
goto block_66;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_93 = l_Lean_Meta_Grind_activateTheorem(x_92, x_69, x_71, x_72, x_73, x_74, x_75, x_76, x_77, x_78, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_11 = x_68;
x_12 = x_71;
x_13 = x_72;
x_14 = x_73;
x_15 = x_74;
x_16 = x_75;
x_17 = x_76;
x_18 = x_77;
x_19 = x_78;
x_20 = x_94;
goto block_66;
}
else
{
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_1);
return x_93;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_88);
if (x_95 == 0)
{
return x_88;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_88, 0);
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_88);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
block_125:
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_box(7);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_101);
lean_inc(x_103);
x_114 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_103, x_101, x_113, x_108, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_67 = x_101;
x_68 = x_100;
x_69 = x_102;
x_70 = x_103;
x_71 = x_104;
x_72 = x_105;
x_73 = x_106;
x_74 = x_107;
x_75 = x_108;
x_76 = x_109;
x_77 = x_110;
x_78 = x_111;
x_79 = x_116;
goto block_99;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_102);
x_119 = l_Lean_Meta_Grind_activateTheorem(x_118, x_102, x_104, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_67 = x_101;
x_68 = x_100;
x_69 = x_102;
x_70 = x_103;
x_71 = x_104;
x_72 = x_105;
x_73 = x_106;
x_74 = x_107;
x_75 = x_108;
x_76 = x_109;
x_77 = x_110;
x_78 = x_111;
x_79 = x_120;
goto block_99;
}
else
{
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_1);
return x_119;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_114);
if (x_121 == 0)
{
return x_114;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_114, 0);
x_123 = lean_ctor_get(x_114, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_114);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqResolution", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__0;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Exists", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_forall_eq_false", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true_of_imp_eq_false", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__8;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_imp_eq_false", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__11;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__12;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_47; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_47 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_11);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
lean_inc(x_1);
x_51 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_61 = l_Lean_Meta_Grind_eqResolution(x_1, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_13, x_2, x_63);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_65, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_ctor_set(x_65, 0, x_70);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_dec(x_65);
lean_inc(x_13);
x_75 = l_Lean_Meta_Grind_isEqFalse___redArg(x_13, x_2, x_4, x_8, x_9, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
x_15 = x_75;
goto block_46;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_79 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9, x_78);
x_15 = x_79;
goto block_46;
}
}
else
{
x_15 = x_75;
goto block_46;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_13);
lean_dec(x_12);
x_80 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_63);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_13);
lean_dec(x_12);
x_81 = lean_ctor_get(x_62, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_82 = x_62;
} else {
 lean_dec_ref(x_62);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_61, 1);
lean_inc(x_83);
lean_dec(x_61);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
x_111 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_112 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_111, x_8, x_83);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_free_object(x_81);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
x_92 = x_7;
x_93 = x_8;
x_94 = x_9;
x_95 = x_115;
goto block_110;
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_112);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_112, 1);
x_118 = lean_ctor_get(x_112, 0);
lean_dec(x_118);
x_119 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_117);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_121 = lean_ctor_get(x_119, 1);
x_122 = lean_ctor_get(x_119, 0);
lean_dec(x_122);
x_123 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc(x_1);
x_124 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_119, 7);
lean_ctor_set(x_119, 1, x_124);
lean_ctor_set(x_119, 0, x_123);
x_125 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
lean_ctor_set_tag(x_112, 7);
lean_ctor_set(x_112, 1, x_125);
lean_ctor_set(x_112, 0, x_119);
lean_inc(x_85);
x_126 = l_Lean_MessageData_ofExpr(x_85);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_126);
lean_ctor_set(x_81, 0, x_112);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_81);
lean_ctor_set(x_127, 1, x_123);
x_128 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_111, x_127, x_6, x_7, x_8, x_9, x_121);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
x_92 = x_7;
x_93 = x_8;
x_94 = x_9;
x_95 = x_129;
goto block_110;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_119, 1);
lean_inc(x_130);
lean_dec(x_119);
x_131 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc(x_1);
x_132 = l_Lean_MessageData_ofExpr(x_1);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
lean_ctor_set_tag(x_112, 7);
lean_ctor_set(x_112, 1, x_134);
lean_ctor_set(x_112, 0, x_133);
lean_inc(x_85);
x_135 = l_Lean_MessageData_ofExpr(x_85);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_135);
lean_ctor_set(x_81, 0, x_112);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_81);
lean_ctor_set(x_136, 1, x_131);
x_137 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_111, x_136, x_6, x_7, x_8, x_9, x_130);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
x_92 = x_7;
x_93 = x_8;
x_94 = x_9;
x_95 = x_138;
goto block_110;
}
}
else
{
lean_free_object(x_112);
lean_free_object(x_81);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_119;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_112, 1);
lean_inc(x_139);
lean_dec(x_112);
x_140 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc(x_1);
x_144 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(7, 2, 0);
} else {
 x_145 = x_142;
 lean_ctor_set_tag(x_145, 7);
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_inc(x_85);
x_148 = l_Lean_MessageData_ofExpr(x_85);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_148);
lean_ctor_set(x_81, 0, x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_81);
lean_ctor_set(x_149, 1, x_143);
x_150 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_111, x_149, x_6, x_7, x_8, x_9, x_141);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_87 = x_2;
x_88 = x_3;
x_89 = x_4;
x_90 = x_5;
x_91 = x_6;
x_92 = x_7;
x_93 = x_8;
x_94 = x_9;
x_95 = x_151;
goto block_110;
}
else
{
lean_free_object(x_81);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_140;
}
}
}
block_110:
{
lean_object* x_96; 
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_1);
x_96 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_1);
x_99 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_87, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_1);
x_102 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_97);
x_103 = l_Lean_Expr_app___override(x_86, x_102);
if (lean_is_scalar(x_82)) {
 x_104 = lean_alloc_ctor(4, 1, 0);
} else {
 x_104 = x_82;
 lean_ctor_set_tag(x_104, 4);
}
lean_ctor_set(x_104, 0, x_1);
x_105 = l_Lean_Meta_Grind_addNewRawFact(x_103, x_85, x_100, x_104, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_101);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_96);
if (x_106 == 0)
{
return x_96;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_96, 0);
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_96);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_152 = lean_ctor_get(x_81, 0);
x_153 = lean_ctor_get(x_81, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_81);
x_178 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_179 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_178, x_8, x_83);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_unbox(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_154 = x_2;
x_155 = x_3;
x_156 = x_4;
x_157 = x_5;
x_158 = x_6;
x_159 = x_7;
x_160 = x_8;
x_161 = x_9;
x_162 = x_182;
goto block_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_184 = x_179;
} else {
 lean_dec_ref(x_179);
 x_184 = lean_box(0);
}
x_185 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_183);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
x_188 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc(x_1);
x_189 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(7, 2, 0);
} else {
 x_190 = x_187;
 lean_ctor_set_tag(x_190, 7);
}
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
if (lean_is_scalar(x_184)) {
 x_192 = lean_alloc_ctor(7, 2, 0);
} else {
 x_192 = x_184;
 lean_ctor_set_tag(x_192, 7);
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_152);
x_193 = l_Lean_MessageData_ofExpr(x_152);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_188);
x_196 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_178, x_195, x_6, x_7, x_8, x_9, x_186);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_154 = x_2;
x_155 = x_3;
x_156 = x_4;
x_157 = x_5;
x_158 = x_6;
x_159 = x_7;
x_160 = x_8;
x_161 = x_9;
x_162 = x_197;
goto block_177;
}
else
{
lean_dec(x_184);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_82);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_185;
}
}
block_177:
{
lean_object* x_163; 
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_1);
x_163 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_1);
x_166 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_154, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_1);
x_169 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_164);
x_170 = l_Lean_Expr_app___override(x_153, x_169);
if (lean_is_scalar(x_82)) {
 x_171 = lean_alloc_ctor(4, 1, 0);
} else {
 x_171 = x_82;
 lean_ctor_set_tag(x_171, 4);
}
lean_ctor_set(x_171, 0, x_1);
x_172 = l_Lean_Meta_Grind_addNewRawFact(x_170, x_152, x_167, x_171, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_168);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_82);
lean_dec(x_1);
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_175 = x_163;
} else {
 lean_dec_ref(x_163);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_61);
if (x_198 == 0)
{
return x_61;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_61, 0);
x_200 = lean_ctor_get(x_61, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_61);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_51);
if (x_202 == 0)
{
return x_51;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_51, 0);
x_204 = lean_ctor_get(x_51, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_51);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_47, 1);
lean_inc(x_206);
lean_dec(x_47);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_207 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_256; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_256 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_256 == 0)
{
uint8_t x_257; 
x_257 = lean_unbox(x_208);
lean_dec(x_208);
if (x_257 == 0)
{
goto block_255;
}
else
{
if (x_256 == 0)
{
lean_object* x_258; 
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_258 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_209);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
lean_inc(x_259);
lean_inc(x_13);
lean_inc(x_12);
x_262 = l_Lean_mkApp3(x_261, x_12, x_13, x_259);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_263 = l_Lean_Meta_Grind_pushEqTrue(x_12, x_262, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_260);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
lean_inc(x_13);
x_266 = l_Lean_mkApp3(x_265, x_12, x_13, x_259);
x_267 = l_Lean_Meta_Grind_pushEqFalse(x_13, x_266, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_264);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_267;
}
else
{
lean_dec(x_259);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_263;
}
}
else
{
uint8_t x_268; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_268 = !lean_is_exclusive(x_258);
if (x_268 == 0)
{
return x_258;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_258, 0);
x_270 = lean_ctor_get(x_258, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_258);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
goto block_255;
}
}
}
else
{
lean_dec(x_208);
goto block_255;
}
block_255:
{
lean_object* x_210; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_210 = l_Lean_Meta_getLevel(x_12, x_6, x_7, x_8, x_9, x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_213 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_1);
x_216 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_215);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_218 = lean_ctor_get(x_216, 0);
x_219 = lean_ctor_get(x_216, 1);
x_220 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_221 = lean_box(0);
lean_ctor_set_tag(x_216, 1);
lean_ctor_set(x_216, 1, x_221);
lean_ctor_set(x_216, 0, x_211);
lean_inc(x_216);
x_222 = l_Lean_Expr_const___override(x_220, x_216);
lean_inc(x_13);
x_223 = l_Lean_mkNot(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_224 = l_Lean_Expr_lam___override(x_11, x_12, x_223, x_14);
lean_inc(x_12);
x_225 = l_Lean_mkAppB(x_222, x_12, x_224);
x_226 = l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
x_227 = l_Lean_Expr_const___override(x_226, x_216);
lean_inc(x_12);
x_228 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_229 = l_Lean_mkApp3(x_227, x_12, x_228, x_214);
x_230 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_230, 0, x_1);
x_231 = l_Lean_Meta_Grind_addNewRawFact(x_229, x_225, x_218, x_230, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_219);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_232 = lean_ctor_get(x_216, 0);
x_233 = lean_ctor_get(x_216, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_216);
x_234 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_235 = lean_box(0);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_211);
lean_ctor_set(x_236, 1, x_235);
lean_inc(x_236);
x_237 = l_Lean_Expr_const___override(x_234, x_236);
lean_inc(x_13);
x_238 = l_Lean_mkNot(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_239 = l_Lean_Expr_lam___override(x_11, x_12, x_238, x_14);
lean_inc(x_12);
x_240 = l_Lean_mkAppB(x_237, x_12, x_239);
x_241 = l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
x_242 = l_Lean_Expr_const___override(x_241, x_236);
lean_inc(x_12);
x_243 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_244 = l_Lean_mkApp3(x_242, x_12, x_243, x_214);
x_245 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_245, 0, x_1);
x_246 = l_Lean_Meta_Grind_addNewRawFact(x_244, x_240, x_232, x_245, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_233);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_dec(x_211);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_213);
if (x_247 == 0)
{
return x_213;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_213, 0);
x_249 = lean_ctor_get(x_213, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_213);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_210);
if (x_251 == 0)
{
return x_210;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_210, 0);
x_253 = lean_ctor_get(x_210, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_210);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_207);
if (x_272 == 0)
{
return x_207;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_207, 0);
x_274 = lean_ctor_get(x_207, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_207);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_47);
if (x_276 == 0)
{
return x_47;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_47, 0);
x_278 = lean_ctor_get(x_47, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_47);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
block_46:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_28 = l_Lean_Meta_Grind_mkEqFalseProof(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc(x_12);
x_32 = l_Lean_mkApp4(x_31, x_12, x_13, x_26, x_29);
x_33 = l_Lean_Meta_Grind_pushEqFalse(x_12, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_10);
return x_281;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateExistsDown___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateExistsDown___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateExistsDown___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_not_of_not_exists", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateExistsDown___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_1);
x_37 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec(x_31);
x_41 = l_Lean_Meta_Grind_propagateExistsDown___closed__2;
x_42 = l_Lean_Meta_Grind_propagateExistsDown___closed__3;
lean_inc(x_27);
x_43 = l_Lean_Expr_app___override(x_27, x_42);
x_44 = l_Lean_Expr_headBeta(x_43);
x_45 = l_Lean_Expr_app___override(x_41, x_44);
x_46 = l_Lean_Meta_Grind_propagateExistsDown___closed__5;
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
lean_inc(x_30);
x_49 = l_Lean_Expr_forallE___override(x_46, x_30, x_45, x_48);
x_50 = l_Lean_Meta_Grind_propagateExistsDown___closed__7;
x_51 = l_Lean_Expr_const___override(x_50, x_40);
lean_inc(x_1);
x_52 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_35);
x_53 = l_Lean_mkApp3(x_51, x_30, x_27, x_52);
x_54 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_54, 0, x_1);
x_55 = l_Lean_Meta_Grind_addNewRawFact(x_53, x_49, x_38, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_34);
if (x_56 == 0)
{
return x_34;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp___hyg_2884_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12);
l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13 = _init_l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13);
l_Lean_Meta_Grind_propagateForallPropUp___closed__0 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__0);
l_Lean_Meta_Grind_propagateForallPropUp___closed__1 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__1);
l_Lean_Meta_Grind_propagateForallPropUp___closed__2 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
l_Lean_Meta_Grind_propagateForallPropUp___closed__3 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__3);
l_Lean_Meta_Grind_propagateForallPropUp___closed__4 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__4);
l_Lean_Meta_Grind_propagateForallPropUp___closed__5 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__5);
l_Lean_Meta_Grind_propagateForallPropUp___closed__6 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__6);
l_Lean_Meta_Grind_propagateForallPropUp___closed__7 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
l_Lean_Meta_Grind_propagateForallPropUp___closed__8 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__8);
l_Lean_Meta_Grind_propagateForallPropUp___closed__9 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
l_Lean_Meta_Grind_propagateForallPropUp___closed__10 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__10);
l_Lean_Meta_Grind_propagateForallPropUp___closed__11 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
l_Lean_Meta_Grind_propagateForallPropUp___closed__12 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__12);
l_Lean_Meta_Grind_propagateForallPropUp___closed__13 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__13);
l_Lean_Meta_Grind_propagateForallPropUp___closed__14 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__14);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__4);
l_Lean_Meta_Grind_propagateForallPropDown___closed__0 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__0);
l_Lean_Meta_Grind_propagateForallPropDown___closed__1 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__1);
l_Lean_Meta_Grind_propagateForallPropDown___closed__2 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__2);
l_Lean_Meta_Grind_propagateForallPropDown___closed__3 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__3);
l_Lean_Meta_Grind_propagateForallPropDown___closed__4 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__4);
l_Lean_Meta_Grind_propagateForallPropDown___closed__5 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__5);
l_Lean_Meta_Grind_propagateForallPropDown___closed__6 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__6);
l_Lean_Meta_Grind_propagateForallPropDown___closed__7 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__7);
l_Lean_Meta_Grind_propagateForallPropDown___closed__8 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__8);
l_Lean_Meta_Grind_propagateForallPropDown___closed__9 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__9);
l_Lean_Meta_Grind_propagateForallPropDown___closed__10 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__10);
l_Lean_Meta_Grind_propagateForallPropDown___closed__11 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
l_Lean_Meta_Grind_propagateForallPropDown___closed__12 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__12);
l_Lean_Meta_Grind_propagateForallPropDown___closed__13 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__13);
l_Lean_Meta_Grind_propagateExistsDown___closed__0 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__0);
l_Lean_Meta_Grind_propagateExistsDown___closed__1 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__1);
l_Lean_Meta_Grind_propagateExistsDown___closed__2 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__2);
l_Lean_Meta_Grind_propagateExistsDown___closed__3 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__3);
l_Lean_Meta_Grind_propagateExistsDown___closed__4 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__4);
l_Lean_Meta_Grind_propagateExistsDown___closed__5 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__5);
l_Lean_Meta_Grind_propagateExistsDown___closed__6 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__6);
l_Lean_Meta_Grind_propagateExistsDown___closed__7 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__7);
if (builtin) {res = l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp___hyg_2884_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
