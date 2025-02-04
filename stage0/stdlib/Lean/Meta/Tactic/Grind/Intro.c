// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.Combinators
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
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAll___closed__1;
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_intros___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_saveCases(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_Grind_GrindTactic_iterate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__1;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__2;
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed(lean_object**);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__3;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Meta_Grind_markAsMatchCond(x_1);
x_14 = l_Lean_Meta_Grind_preprocess(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_num___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
x_29 = lean_ctor_get(x_14, 7);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_5);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
lean_ctor_set(x_30, 7, x_29);
x_31 = lean_st_ref_set(x_1, x_30, x_15);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_36);
lean_inc(x_35);
x_37 = l_Lean_Name_num___override(x_35, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_36, x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_st_ref_take(x_1, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 7);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 lean_ctor_release(x_42, 5);
 lean_ctor_release(x_42, 6);
 lean_ctor_release(x_42, 7);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 8, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_47);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_49);
lean_ctor_set(x_52, 7, x_50);
x_53 = lean_st_ref_set(x_1, x_52, x_43);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_37);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg___boxed), 2, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_FVarId_getDecl(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_FVarId_getDecl(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_value(x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_fvar___override(x_1);
x_20 = l_Lean_Meta_Grind_shareCommon(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_17);
x_23 = l_Lean_Meta_Simp_Result_getProof(x_17, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
lean_inc(x_3);
x_27 = l_Lean_Meta_Grind_addNewEq(x_21, x_26, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_3, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_st_ref_get(x_3, x_31);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_ctor_set(x_29, 1, x_34);
lean_ctor_set(x_32, 0, x_29);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_29, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_st_ref_get(x_3, x_39);
lean_dec(x_3);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_41);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_23, 0);
x_52 = lean_ctor_get(x_23, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_23);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
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
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_16, 0);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_16);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
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
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, uint8_t x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36, lean_object* x_37, lean_object* x_38, lean_object* x_39, lean_object* x_40) {
_start:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_LocalDecl_type(x_32);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_41);
x_42 = l_Lean_Meta_isProp(x_41, x_36, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
lean_inc(x_1);
x_48 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_4);
lean_ctor_set(x_48, 4, x_5);
lean_ctor_set(x_48, 5, x_6);
lean_ctor_set(x_48, 6, x_7);
lean_ctor_set(x_48, 7, x_9);
lean_ctor_set(x_48, 8, x_10);
lean_ctor_set(x_48, 9, x_11);
lean_ctor_set(x_48, 10, x_12);
lean_ctor_set(x_48, 11, x_13);
lean_ctor_set(x_48, 12, x_14);
lean_ctor_set(x_48, 13, x_15);
lean_ctor_set(x_48, 14, x_16);
lean_ctor_set(x_48, 15, x_17);
lean_ctor_set(x_48, 16, x_18);
lean_ctor_set(x_48, 17, x_19);
lean_ctor_set(x_48, 18, x_20);
lean_ctor_set(x_48, 19, x_21);
lean_ctor_set(x_48, 20, x_22);
lean_ctor_set(x_48, 21, x_23);
lean_ctor_set(x_48, 22, x_24);
lean_ctor_set(x_48, 23, x_25);
lean_ctor_set(x_48, 24, x_26);
lean_ctor_set(x_48, 25, x_27);
lean_ctor_set_uint8(x_48, sizeof(void*)*26, x_8);
if (x_28 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isLetFun(x_29);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_1);
x_50 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_50, 0, x_30);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_42);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_51, 0, x_48);
lean_inc(x_30);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_52, 0, x_30);
lean_closure_set(x_52, 1, x_31);
x_53 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_53, 0, x_51);
lean_closure_set(x_53, 1, x_52);
x_54 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_55 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_55, 0, x_53);
lean_closure_set(x_55, 1, x_54);
x_56 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_55, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_46);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_59, 0, x_30);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_62, 0, x_30);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_30);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_56, 0);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_56);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_free_object(x_42);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_68, 0, x_48);
lean_inc(x_30);
x_69 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_69, 0, x_30);
lean_closure_set(x_69, 1, x_31);
x_70 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_69);
x_71 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_72 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_72, 0, x_70);
lean_closure_set(x_72, 1, x_71);
x_73 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_72, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_46);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_79, 0, x_30);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_30);
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
return x_73;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_73);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_42, 1);
lean_inc(x_85);
lean_dec(x_42);
lean_inc(x_1);
x_86 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_2);
lean_ctor_set(x_86, 2, x_3);
lean_ctor_set(x_86, 3, x_4);
lean_ctor_set(x_86, 4, x_5);
lean_ctor_set(x_86, 5, x_6);
lean_ctor_set(x_86, 6, x_7);
lean_ctor_set(x_86, 7, x_9);
lean_ctor_set(x_86, 8, x_10);
lean_ctor_set(x_86, 9, x_11);
lean_ctor_set(x_86, 10, x_12);
lean_ctor_set(x_86, 11, x_13);
lean_ctor_set(x_86, 12, x_14);
lean_ctor_set(x_86, 13, x_15);
lean_ctor_set(x_86, 14, x_16);
lean_ctor_set(x_86, 15, x_17);
lean_ctor_set(x_86, 16, x_18);
lean_ctor_set(x_86, 17, x_19);
lean_ctor_set(x_86, 18, x_20);
lean_ctor_set(x_86, 19, x_21);
lean_ctor_set(x_86, 20, x_22);
lean_ctor_set(x_86, 21, x_23);
lean_ctor_set(x_86, 22, x_24);
lean_ctor_set(x_86, 23, x_25);
lean_ctor_set(x_86, 24, x_26);
lean_ctor_set(x_86, 25, x_27);
lean_ctor_set_uint8(x_86, sizeof(void*)*26, x_8);
if (x_28 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Expr_isLetFun(x_29);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_1);
x_88 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_88, 0, x_30);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_90, 0, x_86);
lean_inc(x_30);
x_91 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_91, 0, x_30);
lean_closure_set(x_91, 1, x_31);
x_92 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_92, 0, x_90);
lean_closure_set(x_92, 1, x_91);
x_93 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_94 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_94, 0, x_92);
lean_closure_set(x_94, 1, x_93);
x_95 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_94, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_85);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_99, 0, x_30);
lean_ctor_set(x_99, 1, x_96);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_30);
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_103 = x_95;
} else {
 lean_dec_ref(x_95);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_105, 0, x_86);
lean_inc(x_30);
x_106 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_106, 0, x_30);
lean_closure_set(x_106, 1, x_31);
x_107 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_107, 0, x_105);
lean_closure_set(x_107, 1, x_106);
x_108 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_109 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_109, 0, x_107);
lean_closure_set(x_109, 1, x_108);
x_110 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_109, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_85);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_114, 0, x_30);
lean_ctor_set(x_114, 1, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_30);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_120 = lean_ctor_get(x_42, 1);
lean_inc(x_120);
lean_dec(x_42);
x_121 = l_Lean_LocalDecl_userName(x_32);
x_122 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_121, x_38, x_39, x_120);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Expr_fvar___override(x_30);
x_126 = l_Lean_MVarId_assert(x_1, x_123, x_41, x_125, x_36, x_37, x_38, x_39, x_124);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 2, x_3);
lean_ctor_set(x_129, 3, x_4);
lean_ctor_set(x_129, 4, x_5);
lean_ctor_set(x_129, 5, x_6);
lean_ctor_set(x_129, 6, x_7);
lean_ctor_set(x_129, 7, x_9);
lean_ctor_set(x_129, 8, x_10);
lean_ctor_set(x_129, 9, x_11);
lean_ctor_set(x_129, 10, x_12);
lean_ctor_set(x_129, 11, x_13);
lean_ctor_set(x_129, 12, x_14);
lean_ctor_set(x_129, 13, x_15);
lean_ctor_set(x_129, 14, x_16);
lean_ctor_set(x_129, 15, x_17);
lean_ctor_set(x_129, 16, x_18);
lean_ctor_set(x_129, 17, x_19);
lean_ctor_set(x_129, 18, x_20);
lean_ctor_set(x_129, 19, x_21);
lean_ctor_set(x_129, 20, x_22);
lean_ctor_set(x_129, 21, x_23);
lean_ctor_set(x_129, 22, x_24);
lean_ctor_set(x_129, 23, x_25);
lean_ctor_set(x_129, 24, x_26);
lean_ctor_set(x_129, 25, x_27);
lean_ctor_set_uint8(x_129, sizeof(void*)*26, x_8);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_126, 0, x_130);
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_126, 0);
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_126);
x_133 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_2);
lean_ctor_set(x_133, 2, x_3);
lean_ctor_set(x_133, 3, x_4);
lean_ctor_set(x_133, 4, x_5);
lean_ctor_set(x_133, 5, x_6);
lean_ctor_set(x_133, 6, x_7);
lean_ctor_set(x_133, 7, x_9);
lean_ctor_set(x_133, 8, x_10);
lean_ctor_set(x_133, 9, x_11);
lean_ctor_set(x_133, 10, x_12);
lean_ctor_set(x_133, 11, x_13);
lean_ctor_set(x_133, 12, x_14);
lean_ctor_set(x_133, 13, x_15);
lean_ctor_set(x_133, 14, x_16);
lean_ctor_set(x_133, 15, x_17);
lean_ctor_set(x_133, 16, x_18);
lean_ctor_set(x_133, 17, x_19);
lean_ctor_set(x_133, 18, x_20);
lean_ctor_set(x_133, 19, x_21);
lean_ctor_set(x_133, 20, x_22);
lean_ctor_set(x_133, 21, x_23);
lean_ctor_set(x_133, 22, x_24);
lean_ctor_set(x_133, 23, x_25);
lean_ctor_set(x_133, 24, x_26);
lean_ctor_set(x_133, 25, x_27);
lean_ctor_set_uint8(x_133, sizeof(void*)*26, x_8);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_126);
if (x_136 == 0)
{
return x_126;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_126, 0);
x_138 = lean_ctor_get(x_126, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_126);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_42);
if (x_140 == 0)
{
return x_42;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_42, 0);
x_142 = lean_ctor_get(x_42, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_42);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_11, x_12, x_11, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro_with_eq", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_st_ref_get(x_10, x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_ctor_get(x_25, 3);
x_31 = lean_ctor_get(x_25, 4);
x_32 = lean_ctor_get(x_25, 5);
x_33 = lean_ctor_get(x_25, 6);
x_34 = lean_ctor_get_uint8(x_25, sizeof(void*)*26);
x_35 = lean_ctor_get(x_25, 7);
x_36 = lean_ctor_get(x_25, 8);
x_37 = lean_ctor_get(x_25, 9);
x_38 = lean_ctor_get(x_25, 10);
x_39 = lean_ctor_get(x_25, 11);
x_40 = lean_ctor_get(x_25, 12);
x_41 = lean_ctor_get(x_25, 13);
x_42 = lean_ctor_get(x_25, 14);
x_43 = lean_ctor_get(x_25, 15);
x_44 = lean_ctor_get(x_25, 16);
x_45 = lean_ctor_get(x_25, 17);
x_46 = lean_ctor_get(x_25, 18);
x_47 = lean_ctor_get(x_25, 19);
x_48 = lean_ctor_get(x_25, 20);
x_49 = lean_ctor_get(x_25, 21);
x_50 = lean_ctor_get(x_25, 22);
x_51 = lean_ctor_get(x_25, 23);
x_52 = lean_ctor_get(x_25, 24);
x_53 = lean_ctor_get(x_25, 25);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
x_54 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_28);
lean_ctor_set(x_54, 2, x_29);
lean_ctor_set(x_54, 3, x_30);
lean_ctor_set(x_54, 4, x_31);
lean_ctor_set(x_54, 5, x_32);
lean_ctor_set(x_54, 6, x_33);
lean_ctor_set(x_54, 7, x_35);
lean_ctor_set(x_54, 8, x_36);
lean_ctor_set(x_54, 9, x_37);
lean_ctor_set(x_54, 10, x_38);
lean_ctor_set(x_54, 11, x_39);
lean_ctor_set(x_54, 12, x_40);
lean_ctor_set(x_54, 13, x_41);
lean_ctor_set(x_54, 14, x_42);
lean_ctor_set(x_54, 15, x_43);
lean_ctor_set(x_54, 16, x_44);
lean_ctor_set(x_54, 17, x_45);
lean_ctor_set(x_54, 18, x_46);
lean_ctor_set(x_54, 19, x_47);
lean_ctor_set(x_54, 20, x_48);
lean_ctor_set(x_54, 21, x_49);
lean_ctor_set(x_54, 22, x_50);
lean_ctor_set(x_54, 23, x_51);
lean_ctor_set(x_54, 24, x_52);
lean_ctor_set(x_54, 25, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*26, x_34);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_54);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_55 = lean_ctor_get(x_23, 0);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_23);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 6);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_55, sizeof(void*)*26);
x_64 = lean_ctor_get(x_55, 7);
lean_inc(x_64);
x_65 = lean_ctor_get(x_55, 8);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 9);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 10);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 11);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 12);
lean_inc(x_69);
x_70 = lean_ctor_get(x_55, 13);
lean_inc(x_70);
x_71 = lean_ctor_get(x_55, 14);
lean_inc(x_71);
x_72 = lean_ctor_get(x_55, 15);
lean_inc(x_72);
x_73 = lean_ctor_get(x_55, 16);
lean_inc(x_73);
x_74 = lean_ctor_get(x_55, 17);
lean_inc(x_74);
x_75 = lean_ctor_get(x_55, 18);
lean_inc(x_75);
x_76 = lean_ctor_get(x_55, 19);
lean_inc(x_76);
x_77 = lean_ctor_get(x_55, 20);
lean_inc(x_77);
x_78 = lean_ctor_get(x_55, 21);
lean_inc(x_78);
x_79 = lean_ctor_get(x_55, 22);
lean_inc(x_79);
x_80 = lean_ctor_get(x_55, 23);
lean_inc(x_80);
x_81 = lean_ctor_get(x_55, 24);
lean_inc(x_81);
x_82 = lean_ctor_get(x_55, 25);
lean_inc(x_82);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 lean_ctor_release(x_55, 7);
 lean_ctor_release(x_55, 8);
 lean_ctor_release(x_55, 9);
 lean_ctor_release(x_55, 10);
 lean_ctor_release(x_55, 11);
 lean_ctor_release(x_55, 12);
 lean_ctor_release(x_55, 13);
 lean_ctor_release(x_55, 14);
 lean_ctor_release(x_55, 15);
 lean_ctor_release(x_55, 16);
 lean_ctor_release(x_55, 17);
 lean_ctor_release(x_55, 18);
 lean_ctor_release(x_55, 19);
 lean_ctor_release(x_55, 20);
 lean_ctor_release(x_55, 21);
 lean_ctor_release(x_55, 22);
 lean_ctor_release(x_55, 23);
 lean_ctor_release(x_55, 24);
 lean_ctor_release(x_55, 25);
 x_83 = x_55;
} else {
 lean_dec_ref(x_55);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 26, 1);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_3);
lean_ctor_set(x_84, 1, x_57);
lean_ctor_set(x_84, 2, x_58);
lean_ctor_set(x_84, 3, x_59);
lean_ctor_set(x_84, 4, x_60);
lean_ctor_set(x_84, 5, x_61);
lean_ctor_set(x_84, 6, x_62);
lean_ctor_set(x_84, 7, x_64);
lean_ctor_set(x_84, 8, x_65);
lean_ctor_set(x_84, 9, x_66);
lean_ctor_set(x_84, 10, x_67);
lean_ctor_set(x_84, 11, x_68);
lean_ctor_set(x_84, 12, x_69);
lean_ctor_set(x_84, 13, x_70);
lean_ctor_set(x_84, 14, x_71);
lean_ctor_set(x_84, 15, x_72);
lean_ctor_set(x_84, 16, x_73);
lean_ctor_set(x_84, 17, x_74);
lean_ctor_set(x_84, 18, x_75);
lean_ctor_set(x_84, 19, x_76);
lean_ctor_set(x_84, 20, x_77);
lean_ctor_set(x_84, 21, x_78);
lean_ctor_set(x_84, 22, x_79);
lean_ctor_set(x_84, 23, x_80);
lean_ctor_set(x_84, 24, x_81);
lean_ctor_set(x_84, 25, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*26, x_63);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_84);
lean_ctor_set(x_19, 0, x_4);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_19);
lean_ctor_set(x_85, 1, x_56);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_86 = lean_ctor_get(x_19, 1);
lean_inc(x_86);
lean_dec(x_19);
x_87 = lean_st_ref_get(x_10, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_88, 6);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_88, sizeof(void*)*26);
x_98 = lean_ctor_get(x_88, 7);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 8);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 9);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 10);
lean_inc(x_101);
x_102 = lean_ctor_get(x_88, 11);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 12);
lean_inc(x_103);
x_104 = lean_ctor_get(x_88, 13);
lean_inc(x_104);
x_105 = lean_ctor_get(x_88, 14);
lean_inc(x_105);
x_106 = lean_ctor_get(x_88, 15);
lean_inc(x_106);
x_107 = lean_ctor_get(x_88, 16);
lean_inc(x_107);
x_108 = lean_ctor_get(x_88, 17);
lean_inc(x_108);
x_109 = lean_ctor_get(x_88, 18);
lean_inc(x_109);
x_110 = lean_ctor_get(x_88, 19);
lean_inc(x_110);
x_111 = lean_ctor_get(x_88, 20);
lean_inc(x_111);
x_112 = lean_ctor_get(x_88, 21);
lean_inc(x_112);
x_113 = lean_ctor_get(x_88, 22);
lean_inc(x_113);
x_114 = lean_ctor_get(x_88, 23);
lean_inc(x_114);
x_115 = lean_ctor_get(x_88, 24);
lean_inc(x_115);
x_116 = lean_ctor_get(x_88, 25);
lean_inc(x_116);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 lean_ctor_release(x_88, 8);
 lean_ctor_release(x_88, 9);
 lean_ctor_release(x_88, 10);
 lean_ctor_release(x_88, 11);
 lean_ctor_release(x_88, 12);
 lean_ctor_release(x_88, 13);
 lean_ctor_release(x_88, 14);
 lean_ctor_release(x_88, 15);
 lean_ctor_release(x_88, 16);
 lean_ctor_release(x_88, 17);
 lean_ctor_release(x_88, 18);
 lean_ctor_release(x_88, 19);
 lean_ctor_release(x_88, 20);
 lean_ctor_release(x_88, 21);
 lean_ctor_release(x_88, 22);
 lean_ctor_release(x_88, 23);
 lean_ctor_release(x_88, 24);
 lean_ctor_release(x_88, 25);
 x_117 = x_88;
} else {
 lean_dec_ref(x_88);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 26, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_3);
lean_ctor_set(x_118, 1, x_91);
lean_ctor_set(x_118, 2, x_92);
lean_ctor_set(x_118, 3, x_93);
lean_ctor_set(x_118, 4, x_94);
lean_ctor_set(x_118, 5, x_95);
lean_ctor_set(x_118, 6, x_96);
lean_ctor_set(x_118, 7, x_98);
lean_ctor_set(x_118, 8, x_99);
lean_ctor_set(x_118, 9, x_100);
lean_ctor_set(x_118, 10, x_101);
lean_ctor_set(x_118, 11, x_102);
lean_ctor_set(x_118, 12, x_103);
lean_ctor_set(x_118, 13, x_104);
lean_ctor_set(x_118, 14, x_105);
lean_ctor_set(x_118, 15, x_106);
lean_ctor_set(x_118, 16, x_107);
lean_ctor_set(x_118, 17, x_108);
lean_ctor_set(x_118, 18, x_109);
lean_ctor_set(x_118, 19, x_110);
lean_ctor_set(x_118, 20, x_111);
lean_ctor_set(x_118, 21, x_112);
lean_ctor_set(x_118, 22, x_113);
lean_ctor_set(x_118, 23, x_114);
lean_ctor_set(x_118, 24, x_115);
lean_ctor_set(x_118, 25, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*26, x_97);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_4);
lean_ctor_set(x_119, 1, x_118);
if (lean_is_scalar(x_90)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_90;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_89);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_121 = lean_ctor_get(x_1, 0);
x_122 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4;
lean_inc(x_5);
x_123 = l_Lean_Expr_const___override(x_122, x_5);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_9);
lean_ctor_set(x_124, 1, x_5);
lean_inc(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_6);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_7);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_8);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_array_mk(x_128);
x_130 = l_Lean_mkAppN(x_123, x_129);
lean_dec(x_129);
x_131 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_2, x_130, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_131, 1);
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
x_135 = lean_st_ref_get(x_10, x_133);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_137, 0);
lean_dec(x_139);
lean_ctor_set(x_137, 0, x_3);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_137);
lean_ctor_set(x_131, 0, x_4);
lean_ctor_set(x_135, 0, x_131);
return x_135;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_140 = lean_ctor_get(x_137, 1);
x_141 = lean_ctor_get(x_137, 2);
x_142 = lean_ctor_get(x_137, 3);
x_143 = lean_ctor_get(x_137, 4);
x_144 = lean_ctor_get(x_137, 5);
x_145 = lean_ctor_get(x_137, 6);
x_146 = lean_ctor_get_uint8(x_137, sizeof(void*)*26);
x_147 = lean_ctor_get(x_137, 7);
x_148 = lean_ctor_get(x_137, 8);
x_149 = lean_ctor_get(x_137, 9);
x_150 = lean_ctor_get(x_137, 10);
x_151 = lean_ctor_get(x_137, 11);
x_152 = lean_ctor_get(x_137, 12);
x_153 = lean_ctor_get(x_137, 13);
x_154 = lean_ctor_get(x_137, 14);
x_155 = lean_ctor_get(x_137, 15);
x_156 = lean_ctor_get(x_137, 16);
x_157 = lean_ctor_get(x_137, 17);
x_158 = lean_ctor_get(x_137, 18);
x_159 = lean_ctor_get(x_137, 19);
x_160 = lean_ctor_get(x_137, 20);
x_161 = lean_ctor_get(x_137, 21);
x_162 = lean_ctor_get(x_137, 22);
x_163 = lean_ctor_get(x_137, 23);
x_164 = lean_ctor_get(x_137, 24);
x_165 = lean_ctor_get(x_137, 25);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_137);
x_166 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_166, 0, x_3);
lean_ctor_set(x_166, 1, x_140);
lean_ctor_set(x_166, 2, x_141);
lean_ctor_set(x_166, 3, x_142);
lean_ctor_set(x_166, 4, x_143);
lean_ctor_set(x_166, 5, x_144);
lean_ctor_set(x_166, 6, x_145);
lean_ctor_set(x_166, 7, x_147);
lean_ctor_set(x_166, 8, x_148);
lean_ctor_set(x_166, 9, x_149);
lean_ctor_set(x_166, 10, x_150);
lean_ctor_set(x_166, 11, x_151);
lean_ctor_set(x_166, 12, x_152);
lean_ctor_set(x_166, 13, x_153);
lean_ctor_set(x_166, 14, x_154);
lean_ctor_set(x_166, 15, x_155);
lean_ctor_set(x_166, 16, x_156);
lean_ctor_set(x_166, 17, x_157);
lean_ctor_set(x_166, 18, x_158);
lean_ctor_set(x_166, 19, x_159);
lean_ctor_set(x_166, 20, x_160);
lean_ctor_set(x_166, 21, x_161);
lean_ctor_set(x_166, 22, x_162);
lean_ctor_set(x_166, 23, x_163);
lean_ctor_set(x_166, 24, x_164);
lean_ctor_set(x_166, 25, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*26, x_146);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_166);
lean_ctor_set(x_131, 0, x_4);
lean_ctor_set(x_135, 0, x_131);
return x_135;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_167 = lean_ctor_get(x_135, 0);
x_168 = lean_ctor_get(x_135, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_135);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_167, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 5);
lean_inc(x_173);
x_174 = lean_ctor_get(x_167, 6);
lean_inc(x_174);
x_175 = lean_ctor_get_uint8(x_167, sizeof(void*)*26);
x_176 = lean_ctor_get(x_167, 7);
lean_inc(x_176);
x_177 = lean_ctor_get(x_167, 8);
lean_inc(x_177);
x_178 = lean_ctor_get(x_167, 9);
lean_inc(x_178);
x_179 = lean_ctor_get(x_167, 10);
lean_inc(x_179);
x_180 = lean_ctor_get(x_167, 11);
lean_inc(x_180);
x_181 = lean_ctor_get(x_167, 12);
lean_inc(x_181);
x_182 = lean_ctor_get(x_167, 13);
lean_inc(x_182);
x_183 = lean_ctor_get(x_167, 14);
lean_inc(x_183);
x_184 = lean_ctor_get(x_167, 15);
lean_inc(x_184);
x_185 = lean_ctor_get(x_167, 16);
lean_inc(x_185);
x_186 = lean_ctor_get(x_167, 17);
lean_inc(x_186);
x_187 = lean_ctor_get(x_167, 18);
lean_inc(x_187);
x_188 = lean_ctor_get(x_167, 19);
lean_inc(x_188);
x_189 = lean_ctor_get(x_167, 20);
lean_inc(x_189);
x_190 = lean_ctor_get(x_167, 21);
lean_inc(x_190);
x_191 = lean_ctor_get(x_167, 22);
lean_inc(x_191);
x_192 = lean_ctor_get(x_167, 23);
lean_inc(x_192);
x_193 = lean_ctor_get(x_167, 24);
lean_inc(x_193);
x_194 = lean_ctor_get(x_167, 25);
lean_inc(x_194);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 lean_ctor_release(x_167, 3);
 lean_ctor_release(x_167, 4);
 lean_ctor_release(x_167, 5);
 lean_ctor_release(x_167, 6);
 lean_ctor_release(x_167, 7);
 lean_ctor_release(x_167, 8);
 lean_ctor_release(x_167, 9);
 lean_ctor_release(x_167, 10);
 lean_ctor_release(x_167, 11);
 lean_ctor_release(x_167, 12);
 lean_ctor_release(x_167, 13);
 lean_ctor_release(x_167, 14);
 lean_ctor_release(x_167, 15);
 lean_ctor_release(x_167, 16);
 lean_ctor_release(x_167, 17);
 lean_ctor_release(x_167, 18);
 lean_ctor_release(x_167, 19);
 lean_ctor_release(x_167, 20);
 lean_ctor_release(x_167, 21);
 lean_ctor_release(x_167, 22);
 lean_ctor_release(x_167, 23);
 lean_ctor_release(x_167, 24);
 lean_ctor_release(x_167, 25);
 x_195 = x_167;
} else {
 lean_dec_ref(x_167);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 26, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_3);
lean_ctor_set(x_196, 1, x_169);
lean_ctor_set(x_196, 2, x_170);
lean_ctor_set(x_196, 3, x_171);
lean_ctor_set(x_196, 4, x_172);
lean_ctor_set(x_196, 5, x_173);
lean_ctor_set(x_196, 6, x_174);
lean_ctor_set(x_196, 7, x_176);
lean_ctor_set(x_196, 8, x_177);
lean_ctor_set(x_196, 9, x_178);
lean_ctor_set(x_196, 10, x_179);
lean_ctor_set(x_196, 11, x_180);
lean_ctor_set(x_196, 12, x_181);
lean_ctor_set(x_196, 13, x_182);
lean_ctor_set(x_196, 14, x_183);
lean_ctor_set(x_196, 15, x_184);
lean_ctor_set(x_196, 16, x_185);
lean_ctor_set(x_196, 17, x_186);
lean_ctor_set(x_196, 18, x_187);
lean_ctor_set(x_196, 19, x_188);
lean_ctor_set(x_196, 20, x_189);
lean_ctor_set(x_196, 21, x_190);
lean_ctor_set(x_196, 22, x_191);
lean_ctor_set(x_196, 23, x_192);
lean_ctor_set(x_196, 24, x_193);
lean_ctor_set(x_196, 25, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*26, x_175);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_196);
lean_ctor_set(x_131, 0, x_4);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_131);
lean_ctor_set(x_197, 1, x_168);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_198 = lean_ctor_get(x_131, 1);
lean_inc(x_198);
lean_dec(x_131);
x_199 = lean_st_ref_get(x_10, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 6);
lean_inc(x_208);
x_209 = lean_ctor_get_uint8(x_200, sizeof(void*)*26);
x_210 = lean_ctor_get(x_200, 7);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 8);
lean_inc(x_211);
x_212 = lean_ctor_get(x_200, 9);
lean_inc(x_212);
x_213 = lean_ctor_get(x_200, 10);
lean_inc(x_213);
x_214 = lean_ctor_get(x_200, 11);
lean_inc(x_214);
x_215 = lean_ctor_get(x_200, 12);
lean_inc(x_215);
x_216 = lean_ctor_get(x_200, 13);
lean_inc(x_216);
x_217 = lean_ctor_get(x_200, 14);
lean_inc(x_217);
x_218 = lean_ctor_get(x_200, 15);
lean_inc(x_218);
x_219 = lean_ctor_get(x_200, 16);
lean_inc(x_219);
x_220 = lean_ctor_get(x_200, 17);
lean_inc(x_220);
x_221 = lean_ctor_get(x_200, 18);
lean_inc(x_221);
x_222 = lean_ctor_get(x_200, 19);
lean_inc(x_222);
x_223 = lean_ctor_get(x_200, 20);
lean_inc(x_223);
x_224 = lean_ctor_get(x_200, 21);
lean_inc(x_224);
x_225 = lean_ctor_get(x_200, 22);
lean_inc(x_225);
x_226 = lean_ctor_get(x_200, 23);
lean_inc(x_226);
x_227 = lean_ctor_get(x_200, 24);
lean_inc(x_227);
x_228 = lean_ctor_get(x_200, 25);
lean_inc(x_228);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 lean_ctor_release(x_200, 6);
 lean_ctor_release(x_200, 7);
 lean_ctor_release(x_200, 8);
 lean_ctor_release(x_200, 9);
 lean_ctor_release(x_200, 10);
 lean_ctor_release(x_200, 11);
 lean_ctor_release(x_200, 12);
 lean_ctor_release(x_200, 13);
 lean_ctor_release(x_200, 14);
 lean_ctor_release(x_200, 15);
 lean_ctor_release(x_200, 16);
 lean_ctor_release(x_200, 17);
 lean_ctor_release(x_200, 18);
 lean_ctor_release(x_200, 19);
 lean_ctor_release(x_200, 20);
 lean_ctor_release(x_200, 21);
 lean_ctor_release(x_200, 22);
 lean_ctor_release(x_200, 23);
 lean_ctor_release(x_200, 24);
 lean_ctor_release(x_200, 25);
 x_229 = x_200;
} else {
 lean_dec_ref(x_200);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 26, 1);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_3);
lean_ctor_set(x_230, 1, x_203);
lean_ctor_set(x_230, 2, x_204);
lean_ctor_set(x_230, 3, x_205);
lean_ctor_set(x_230, 4, x_206);
lean_ctor_set(x_230, 5, x_207);
lean_ctor_set(x_230, 6, x_208);
lean_ctor_set(x_230, 7, x_210);
lean_ctor_set(x_230, 8, x_211);
lean_ctor_set(x_230, 9, x_212);
lean_ctor_set(x_230, 10, x_213);
lean_ctor_set(x_230, 11, x_214);
lean_ctor_set(x_230, 12, x_215);
lean_ctor_set(x_230, 13, x_216);
lean_ctor_set(x_230, 14, x_217);
lean_ctor_set(x_230, 15, x_218);
lean_ctor_set(x_230, 16, x_219);
lean_ctor_set(x_230, 17, x_220);
lean_ctor_set(x_230, 18, x_221);
lean_ctor_set(x_230, 19, x_222);
lean_ctor_set(x_230, 20, x_223);
lean_ctor_set(x_230, 21, x_224);
lean_ctor_set(x_230, 22, x_225);
lean_ctor_set(x_230, 23, x_226);
lean_ctor_set(x_230, 24, x_227);
lean_ctor_set(x_230, 25, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*26, x_209);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_4);
lean_ctor_set(x_231, 1, x_230);
if (lean_is_scalar(x_202)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_202;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_201);
return x_232;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_st_ref_get(x_2, x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_bindingDomain_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_26);
x_27 = l_Lean_Meta_isProp(x_26, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = 1;
x_32 = l_Lean_Meta_intro1Core(x_25, x_31, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_st_ref_get(x_2, x_34);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set_tag(x_37, 3);
lean_ctor_set(x_37, 1, x_39);
lean_ctor_set(x_37, 0, x_35);
x_11 = x_37;
x_12 = x_41;
goto block_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_39, 2);
x_46 = lean_ctor_get(x_39, 3);
x_47 = lean_ctor_get(x_39, 4);
x_48 = lean_ctor_get(x_39, 5);
x_49 = lean_ctor_get(x_39, 6);
x_50 = lean_ctor_get_uint8(x_39, sizeof(void*)*26);
x_51 = lean_ctor_get(x_39, 7);
x_52 = lean_ctor_get(x_39, 8);
x_53 = lean_ctor_get(x_39, 9);
x_54 = lean_ctor_get(x_39, 10);
x_55 = lean_ctor_get(x_39, 11);
x_56 = lean_ctor_get(x_39, 12);
x_57 = lean_ctor_get(x_39, 13);
x_58 = lean_ctor_get(x_39, 14);
x_59 = lean_ctor_get(x_39, 15);
x_60 = lean_ctor_get(x_39, 16);
x_61 = lean_ctor_get(x_39, 17);
x_62 = lean_ctor_get(x_39, 18);
x_63 = lean_ctor_get(x_39, 19);
x_64 = lean_ctor_get(x_39, 20);
x_65 = lean_ctor_get(x_39, 21);
x_66 = lean_ctor_get(x_39, 22);
x_67 = lean_ctor_get(x_39, 23);
x_68 = lean_ctor_get(x_39, 24);
x_69 = lean_ctor_get(x_39, 25);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_70 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_70, 0, x_36);
lean_ctor_set(x_70, 1, x_44);
lean_ctor_set(x_70, 2, x_45);
lean_ctor_set(x_70, 3, x_46);
lean_ctor_set(x_70, 4, x_47);
lean_ctor_set(x_70, 5, x_48);
lean_ctor_set(x_70, 6, x_49);
lean_ctor_set(x_70, 7, x_51);
lean_ctor_set(x_70, 8, x_52);
lean_ctor_set(x_70, 9, x_53);
lean_ctor_set(x_70, 10, x_54);
lean_ctor_set(x_70, 11, x_55);
lean_ctor_set(x_70, 12, x_56);
lean_ctor_set(x_70, 13, x_57);
lean_ctor_set(x_70, 14, x_58);
lean_ctor_set(x_70, 15, x_59);
lean_ctor_set(x_70, 16, x_60);
lean_ctor_set(x_70, 17, x_61);
lean_ctor_set(x_70, 18, x_62);
lean_ctor_set(x_70, 19, x_63);
lean_ctor_set(x_70, 20, x_64);
lean_ctor_set(x_70, 21, x_65);
lean_ctor_set(x_70, 22, x_66);
lean_ctor_set(x_70, 23, x_67);
lean_ctor_set(x_70, 24, x_68);
lean_ctor_set(x_70, 25, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*26, x_50);
lean_ctor_set_tag(x_37, 3);
lean_ctor_set(x_37, 1, x_70);
lean_ctor_set(x_37, 0, x_35);
x_11 = x_37;
x_12 = x_43;
goto block_21;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_71 = lean_ctor_get(x_37, 0);
x_72 = lean_ctor_get(x_37, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_37);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 6);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_71, sizeof(void*)*26);
x_80 = lean_ctor_get(x_71, 7);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 8);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 9);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 10);
lean_inc(x_83);
x_84 = lean_ctor_get(x_71, 11);
lean_inc(x_84);
x_85 = lean_ctor_get(x_71, 12);
lean_inc(x_85);
x_86 = lean_ctor_get(x_71, 13);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 14);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 15);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 16);
lean_inc(x_89);
x_90 = lean_ctor_get(x_71, 17);
lean_inc(x_90);
x_91 = lean_ctor_get(x_71, 18);
lean_inc(x_91);
x_92 = lean_ctor_get(x_71, 19);
lean_inc(x_92);
x_93 = lean_ctor_get(x_71, 20);
lean_inc(x_93);
x_94 = lean_ctor_get(x_71, 21);
lean_inc(x_94);
x_95 = lean_ctor_get(x_71, 22);
lean_inc(x_95);
x_96 = lean_ctor_get(x_71, 23);
lean_inc(x_96);
x_97 = lean_ctor_get(x_71, 24);
lean_inc(x_97);
x_98 = lean_ctor_get(x_71, 25);
lean_inc(x_98);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 lean_ctor_release(x_71, 6);
 lean_ctor_release(x_71, 7);
 lean_ctor_release(x_71, 8);
 lean_ctor_release(x_71, 9);
 lean_ctor_release(x_71, 10);
 lean_ctor_release(x_71, 11);
 lean_ctor_release(x_71, 12);
 lean_ctor_release(x_71, 13);
 lean_ctor_release(x_71, 14);
 lean_ctor_release(x_71, 15);
 lean_ctor_release(x_71, 16);
 lean_ctor_release(x_71, 17);
 lean_ctor_release(x_71, 18);
 lean_ctor_release(x_71, 19);
 lean_ctor_release(x_71, 20);
 lean_ctor_release(x_71, 21);
 lean_ctor_release(x_71, 22);
 lean_ctor_release(x_71, 23);
 lean_ctor_release(x_71, 24);
 lean_ctor_release(x_71, 25);
 x_99 = x_71;
} else {
 lean_dec_ref(x_71);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 26, 1);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_36);
lean_ctor_set(x_100, 1, x_73);
lean_ctor_set(x_100, 2, x_74);
lean_ctor_set(x_100, 3, x_75);
lean_ctor_set(x_100, 4, x_76);
lean_ctor_set(x_100, 5, x_77);
lean_ctor_set(x_100, 6, x_78);
lean_ctor_set(x_100, 7, x_80);
lean_ctor_set(x_100, 8, x_81);
lean_ctor_set(x_100, 9, x_82);
lean_ctor_set(x_100, 10, x_83);
lean_ctor_set(x_100, 11, x_84);
lean_ctor_set(x_100, 12, x_85);
lean_ctor_set(x_100, 13, x_86);
lean_ctor_set(x_100, 14, x_87);
lean_ctor_set(x_100, 15, x_88);
lean_ctor_set(x_100, 16, x_89);
lean_ctor_set(x_100, 17, x_90);
lean_ctor_set(x_100, 18, x_91);
lean_ctor_set(x_100, 19, x_92);
lean_ctor_set(x_100, 20, x_93);
lean_ctor_set(x_100, 21, x_94);
lean_ctor_set(x_100, 22, x_95);
lean_ctor_set(x_100, 23, x_96);
lean_ctor_set(x_100, 24, x_97);
lean_ctor_set(x_100, 25, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*26, x_79);
x_101 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_101, 0, x_35);
lean_ctor_set(x_101, 1, x_100);
x_11 = x_101;
x_12 = x_72;
goto block_21;
}
}
else
{
uint8_t x_102; 
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_32);
if (x_102 == 0)
{
return x_32;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_32, 0);
x_104 = lean_ctor_get(x_32, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_32);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_27, 1);
lean_inc(x_106);
lean_dec(x_27);
lean_inc(x_25);
x_107 = l_Lean_MVarId_getTag(x_25, x_6, x_7, x_8, x_9, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Expr_bindingBody_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_26);
x_111 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_6, 2);
lean_inc(x_117);
x_118 = l_Lean_Expr_bindingName_x21(x_1);
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
lean_dec(x_112);
x_121 = l_Lean_Expr_bindingInfo_x21(x_1);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
x_123 = 0;
lean_inc(x_119);
lean_inc(x_115);
x_124 = l_Lean_LocalContext_mkLocalDecl(x_117, x_115, x_118, x_119, x_122, x_123);
x_125 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_116);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = 2;
x_129 = lean_unsigned_to_nat(0u);
lean_inc(x_110);
x_130 = l_Lean_Meta_mkFreshExprMVarAt(x_124, x_126, x_110, x_128, x_108, x_129, x_6, x_7, x_8, x_9, x_127);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ctor_get(x_130, 1);
x_134 = l_Lean_Expr_mvarId_x21(x_132);
lean_inc(x_115);
x_135 = l_Lean_Expr_fvar___override(x_115);
x_136 = lean_box(0);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 1, x_136);
lean_ctor_set(x_130, 0, x_135);
x_137 = lean_array_mk(x_130);
x_138 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_138, 0, x_137);
lean_closure_set(x_138, 1, x_132);
x_139 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_139, 0, x_138);
lean_inc(x_134);
x_140 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 18, 8);
lean_closure_set(x_140, 0, x_120);
lean_closure_set(x_140, 1, x_25);
lean_closure_set(x_140, 2, x_134);
lean_closure_set(x_140, 3, x_115);
lean_closure_set(x_140, 4, x_136);
lean_closure_set(x_140, 5, x_110);
lean_closure_set(x_140, 6, x_119);
lean_closure_set(x_140, 7, x_26);
x_141 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_141, 0, x_139);
lean_closure_set(x_141, 1, x_140);
lean_inc(x_2);
x_142 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(x_134, x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_133);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_11 = x_143;
x_12 = x_144;
goto block_21;
}
else
{
uint8_t x_145; 
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_142);
if (x_145 == 0)
{
return x_142;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_149 = lean_ctor_get(x_130, 0);
x_150 = lean_ctor_get(x_130, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_130);
x_151 = l_Lean_Expr_mvarId_x21(x_149);
lean_inc(x_115);
x_152 = l_Lean_Expr_fvar___override(x_115);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_array_mk(x_154);
x_156 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_156, 0, x_155);
lean_closure_set(x_156, 1, x_149);
x_157 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_157, 0, x_156);
lean_inc(x_151);
x_158 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 18, 8);
lean_closure_set(x_158, 0, x_120);
lean_closure_set(x_158, 1, x_25);
lean_closure_set(x_158, 2, x_151);
lean_closure_set(x_158, 3, x_115);
lean_closure_set(x_158, 4, x_153);
lean_closure_set(x_158, 5, x_110);
lean_closure_set(x_158, 6, x_119);
lean_closure_set(x_158, 7, x_26);
x_159 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_159, 0, x_157);
lean_closure_set(x_159, 1, x_158);
lean_inc(x_2);
x_160 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(x_151, x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_150);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_11 = x_161;
x_12 = x_162;
goto block_21;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_2);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_165 = x_160;
} else {
 lean_dec_ref(x_160);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_111);
if (x_167 == 0)
{
return x_111;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_111, 0);
x_169 = lean_ctor_get(x_111, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_111);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = !lean_is_exclusive(x_107);
if (x_171 == 0)
{
return x_107;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_107, 0);
x_173 = lean_ctor_get(x_107, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_107);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_27);
if (x_175 == 0)
{
return x_27;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_27, 0);
x_177 = lean_ctor_get(x_27, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_27);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
block_21:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_2, x_12);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 6);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*26);
x_19 = lean_ctor_get(x_1, 7);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 8);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 9);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 10);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 11);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 12);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 13);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 14);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 15);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 16);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 17);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 18);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 19);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 20);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 21);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 22);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 23);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 24);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 25);
lean_inc(x_37);
lean_inc(x_11);
x_38 = l_Lean_MVarId_getType(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lean_Expr_isArrow(x_40);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = l_Lean_Expr_isLet(x_40);
if (x_43 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Expr_isForall(x_40);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Expr_isLetFun(x_40);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
x_64 = lean_box(0);
lean_ctor_set(x_38, 0, x_64);
return x_38;
}
else
{
lean_object* x_65; 
lean_free_object(x_38);
x_65 = lean_box(0);
x_44 = x_65;
goto block_61;
}
}
else
{
lean_object* x_66; 
lean_free_object(x_38);
x_66 = lean_box(0);
x_44 = x_66;
goto block_61;
}
}
else
{
lean_object* x_67; 
lean_free_object(x_38);
x_67 = lean_box(0);
x_44 = x_67;
goto block_61;
}
block_61:
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_44);
x_45 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Meta_intro1Core(x_11, x_45, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
lean_inc(x_49);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_51, 0, x_49);
x_52 = lean_box(x_18);
x_53 = lean_box(x_43);
lean_inc(x_50);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 40, 31);
lean_closure_set(x_54, 0, x_50);
lean_closure_set(x_54, 1, x_12);
lean_closure_set(x_54, 2, x_13);
lean_closure_set(x_54, 3, x_14);
lean_closure_set(x_54, 4, x_15);
lean_closure_set(x_54, 5, x_16);
lean_closure_set(x_54, 6, x_17);
lean_closure_set(x_54, 7, x_52);
lean_closure_set(x_54, 8, x_19);
lean_closure_set(x_54, 9, x_20);
lean_closure_set(x_54, 10, x_21);
lean_closure_set(x_54, 11, x_22);
lean_closure_set(x_54, 12, x_23);
lean_closure_set(x_54, 13, x_24);
lean_closure_set(x_54, 14, x_25);
lean_closure_set(x_54, 15, x_26);
lean_closure_set(x_54, 16, x_27);
lean_closure_set(x_54, 17, x_28);
lean_closure_set(x_54, 18, x_29);
lean_closure_set(x_54, 19, x_30);
lean_closure_set(x_54, 20, x_31);
lean_closure_set(x_54, 21, x_32);
lean_closure_set(x_54, 22, x_33);
lean_closure_set(x_54, 23, x_34);
lean_closure_set(x_54, 24, x_35);
lean_closure_set(x_54, 25, x_36);
lean_closure_set(x_54, 26, x_37);
lean_closure_set(x_54, 27, x_53);
lean_closure_set(x_54, 28, x_40);
lean_closure_set(x_54, 29, x_49);
lean_closure_set(x_54, 30, x_2);
x_55 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_55, 0, x_51);
lean_closure_set(x_55, 1, x_54);
x_56 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_50, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_68, 0, x_1);
x_69 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 10, 1);
lean_closure_set(x_69, 0, x_40);
x_70 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_69);
x_71 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
return x_71;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_71, 0);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_71);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_38, 0);
x_84 = lean_ctor_get(x_38, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_38);
x_85 = l_Lean_Expr_isArrow(x_83);
if (x_85 == 0)
{
uint8_t x_86; lean_object* x_87; 
lean_dec(x_1);
x_86 = l_Lean_Expr_isLet(x_83);
if (x_86 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Expr_isForall(x_83);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_isLetFun(x_83);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_83);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_84);
return x_108;
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_87 = x_109;
goto block_104;
}
}
else
{
lean_object* x_110; 
x_110 = lean_box(0);
x_87 = x_110;
goto block_104;
}
}
else
{
lean_object* x_111; 
x_111 = lean_box(0);
x_87 = x_111;
goto block_104;
}
block_104:
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_87);
x_88 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_89 = l_Lean_Meta_intro1Core(x_11, x_88, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
lean_inc(x_92);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_94, 0, x_92);
x_95 = lean_box(x_18);
x_96 = lean_box(x_86);
lean_inc(x_93);
x_97 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 40, 31);
lean_closure_set(x_97, 0, x_93);
lean_closure_set(x_97, 1, x_12);
lean_closure_set(x_97, 2, x_13);
lean_closure_set(x_97, 3, x_14);
lean_closure_set(x_97, 4, x_15);
lean_closure_set(x_97, 5, x_16);
lean_closure_set(x_97, 6, x_17);
lean_closure_set(x_97, 7, x_95);
lean_closure_set(x_97, 8, x_19);
lean_closure_set(x_97, 9, x_20);
lean_closure_set(x_97, 10, x_21);
lean_closure_set(x_97, 11, x_22);
lean_closure_set(x_97, 12, x_23);
lean_closure_set(x_97, 13, x_24);
lean_closure_set(x_97, 14, x_25);
lean_closure_set(x_97, 15, x_26);
lean_closure_set(x_97, 16, x_27);
lean_closure_set(x_97, 17, x_28);
lean_closure_set(x_97, 18, x_29);
lean_closure_set(x_97, 19, x_30);
lean_closure_set(x_97, 20, x_31);
lean_closure_set(x_97, 21, x_32);
lean_closure_set(x_97, 22, x_33);
lean_closure_set(x_97, 23, x_34);
lean_closure_set(x_97, 24, x_35);
lean_closure_set(x_97, 25, x_36);
lean_closure_set(x_97, 26, x_37);
lean_closure_set(x_97, 27, x_96);
lean_closure_set(x_97, 28, x_83);
lean_closure_set(x_97, 29, x_92);
lean_closure_set(x_97, 30, x_2);
x_98 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_98, 0, x_94);
lean_closure_set(x_98, 1, x_97);
x_99 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_93, x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_83);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
x_100 = lean_ctor_get(x_89, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_102 = x_89;
} else {
 lean_dec_ref(x_89);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_112 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_112, 0, x_1);
x_113 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 10, 1);
lean_closure_set(x_113, 0, x_83);
x_114 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_114, 0, x_112);
lean_closure_set(x_114, 1, x_113);
x_115 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_115, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_123 = x_115;
} else {
 lean_dec_ref(x_115);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
x_125 = !lean_is_exclusive(x_38);
if (x_125 == 0)
{
return x_38;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_38, 0);
x_127 = lean_ctor_get(x_38, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_38);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
lean_object* x_34 = _args[33];
lean_object* x_35 = _args[34];
lean_object* x_36 = _args[35];
lean_object* x_37 = _args[36];
lean_object* x_38 = _args[37];
lean_object* x_39 = _args[38];
lean_object* x_40 = _args[39];
_start:
{
uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_unbox(x_8);
lean_dec(x_8);
x_42 = lean_unbox(x_28);
lean_dec(x_28);
x_43 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_42, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
lean_dec(x_32);
lean_dec(x_29);
return x_43;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 10);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(x_5, x_4);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*26);
x_15 = lean_ctor_get(x_1, 7);
x_16 = lean_ctor_get(x_1, 8);
x_17 = lean_ctor_get(x_1, 9);
x_18 = lean_ctor_get(x_1, 10);
x_19 = lean_ctor_get(x_1, 11);
x_20 = lean_ctor_get(x_1, 12);
x_21 = lean_ctor_get(x_1, 13);
x_22 = lean_ctor_get(x_1, 14);
x_23 = lean_ctor_get(x_1, 15);
x_24 = lean_ctor_get(x_1, 16);
x_25 = lean_ctor_get(x_1, 17);
x_26 = lean_ctor_get(x_1, 18);
x_27 = lean_ctor_get(x_1, 19);
x_28 = lean_ctor_get(x_1, 20);
x_29 = lean_ctor_get(x_1, 21);
x_30 = lean_ctor_get(x_1, 22);
x_31 = lean_ctor_get(x_1, 23);
x_32 = lean_ctor_get(x_1, 24);
x_33 = lean_ctor_get(x_1, 25);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_34 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_9);
lean_ctor_set(x_34, 3, x_10);
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 5, x_12);
lean_ctor_set(x_34, 6, x_13);
lean_ctor_set(x_34, 7, x_15);
lean_ctor_set(x_34, 8, x_16);
lean_ctor_set(x_34, 9, x_17);
lean_ctor_set(x_34, 10, x_18);
lean_ctor_set(x_34, 11, x_19);
lean_ctor_set(x_34, 12, x_20);
lean_ctor_set(x_34, 13, x_21);
lean_ctor_set(x_34, 14, x_22);
lean_ctor_set(x_34, 15, x_23);
lean_ctor_set(x_34, 16, x_24);
lean_ctor_set(x_34, 17, x_25);
lean_ctor_set(x_34, 18, x_26);
lean_ctor_set(x_34, 19, x_27);
lean_ctor_set(x_34, 20, x_28);
lean_ctor_set(x_34, 21, x_29);
lean_ctor_set(x_34, 22, x_30);
lean_ctor_set(x_34, 23, x_31);
lean_ctor_set(x_34, 24, x_32);
lean_ctor_set(x_34, 25, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*26, x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_34);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_1, 2);
x_40 = lean_ctor_get(x_1, 3);
x_41 = lean_ctor_get(x_1, 4);
x_42 = lean_ctor_get(x_1, 5);
x_43 = lean_ctor_get(x_1, 6);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*26);
x_45 = lean_ctor_get(x_1, 7);
x_46 = lean_ctor_get(x_1, 8);
x_47 = lean_ctor_get(x_1, 9);
x_48 = lean_ctor_get(x_1, 10);
x_49 = lean_ctor_get(x_1, 11);
x_50 = lean_ctor_get(x_1, 12);
x_51 = lean_ctor_get(x_1, 13);
x_52 = lean_ctor_get(x_1, 14);
x_53 = lean_ctor_get(x_1, 15);
x_54 = lean_ctor_get(x_1, 16);
x_55 = lean_ctor_get(x_1, 17);
x_56 = lean_ctor_get(x_1, 18);
x_57 = lean_ctor_get(x_1, 19);
x_58 = lean_ctor_get(x_1, 20);
x_59 = lean_ctor_get(x_1, 21);
x_60 = lean_ctor_get(x_1, 22);
x_61 = lean_ctor_get(x_1, 23);
x_62 = lean_ctor_get(x_1, 24);
x_63 = lean_ctor_get(x_1, 25);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
x_64 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_64, 0, x_36);
lean_ctor_set(x_64, 1, x_38);
lean_ctor_set(x_64, 2, x_39);
lean_ctor_set(x_64, 3, x_40);
lean_ctor_set(x_64, 4, x_41);
lean_ctor_set(x_64, 5, x_42);
lean_ctor_set(x_64, 6, x_43);
lean_ctor_set(x_64, 7, x_45);
lean_ctor_set(x_64, 8, x_46);
lean_ctor_set(x_64, 9, x_47);
lean_ctor_set(x_64, 10, x_48);
lean_ctor_set(x_64, 11, x_49);
lean_ctor_set(x_64, 12, x_50);
lean_ctor_set(x_64, 13, x_51);
lean_ctor_set(x_64, 14, x_52);
lean_ctor_set(x_64, 15, x_53);
lean_ctor_set(x_64, 16, x_54);
lean_ctor_set(x_64, 17, x_55);
lean_ctor_set(x_64, 18, x_56);
lean_ctor_set(x_64, 19, x_57);
lean_ctor_set(x_64, 20, x_58);
lean_ctor_set(x_64, 21, x_59);
lean_ctor_set(x_64, 22, x_60);
lean_ctor_set(x_64, 23, x_61);
lean_ctor_set(x_64, 24, x_62);
lean_ctor_set(x_64, 25, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*26, x_44);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
x_2 = x_37;
x_3 = x_65;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_FVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = l_Lean_Meta_Grind_cases(x_2, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_3, x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_3, x_20, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Meta_whnfD(x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; 
lean_free_object(x_13);
x_19 = l_Lean_Expr_getAppFn(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = l_Lean_Meta_Grind_saveCases(x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_2, x_3, x_1, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_23);
lean_dec(x_1);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_2, x_3, x_1, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_1);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
lean_inc(x_1);
x_30 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Expr_getAppFn(x_28);
lean_dec(x_28);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = 1;
x_36 = l_Lean_Meta_Grind_saveCases(x_34, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_2, x_3, x_1, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
lean_dec(x_37);
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_2, x_3, x_1, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_1);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed), 9, 1);
lean_closure_set(x_12, 0, x_2);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3___boxed), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get(x_1, 6);
x_16 = lean_ctor_get(x_1, 7);
x_17 = lean_ctor_get(x_1, 8);
x_18 = lean_ctor_get(x_1, 9);
x_19 = lean_ctor_get(x_1, 10);
x_20 = lean_ctor_get(x_1, 11);
x_21 = lean_ctor_get(x_1, 12);
x_22 = lean_ctor_get(x_1, 13);
x_23 = lean_ctor_get(x_1, 14);
x_24 = lean_ctor_get(x_1, 15);
x_25 = lean_ctor_get(x_1, 16);
x_26 = lean_ctor_get(x_1, 17);
x_27 = lean_ctor_get(x_1, 18);
x_28 = lean_ctor_get(x_1, 19);
x_29 = lean_ctor_get(x_1, 20);
x_30 = lean_ctor_get(x_1, 21);
x_31 = lean_ctor_get(x_1, 22);
x_32 = lean_ctor_get(x_1, 23);
x_33 = lean_ctor_get(x_1, 24);
x_34 = lean_ctor_get(x_1, 25);
x_35 = l_Lean_Meta_Grind_injection_x3f(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_free_object(x_1);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_35, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set(x_36, 0, x_1);
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
lean_dec(x_36);
lean_ctor_set(x_1, 0, x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_35, 0, x_48);
return x_35;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_dec(x_35);
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_51 = x_36;
} else {
 lean_dec_ref(x_36);
 x_51 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_50);
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_free_object(x_1);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_54 = !lean_is_exclusive(x_35);
if (x_54 == 0)
{
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_35, 0);
x_56 = lean_ctor_get(x_35, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_35);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 1);
x_60 = lean_ctor_get(x_1, 2);
x_61 = lean_ctor_get(x_1, 3);
x_62 = lean_ctor_get(x_1, 4);
x_63 = lean_ctor_get(x_1, 5);
x_64 = lean_ctor_get(x_1, 6);
x_65 = lean_ctor_get_uint8(x_1, sizeof(void*)*26);
x_66 = lean_ctor_get(x_1, 7);
x_67 = lean_ctor_get(x_1, 8);
x_68 = lean_ctor_get(x_1, 9);
x_69 = lean_ctor_get(x_1, 10);
x_70 = lean_ctor_get(x_1, 11);
x_71 = lean_ctor_get(x_1, 12);
x_72 = lean_ctor_get(x_1, 13);
x_73 = lean_ctor_get(x_1, 14);
x_74 = lean_ctor_get(x_1, 15);
x_75 = lean_ctor_get(x_1, 16);
x_76 = lean_ctor_get(x_1, 17);
x_77 = lean_ctor_get(x_1, 18);
x_78 = lean_ctor_get(x_1, 19);
x_79 = lean_ctor_get(x_1, 20);
x_80 = lean_ctor_get(x_1, 21);
x_81 = lean_ctor_get(x_1, 22);
x_82 = lean_ctor_get(x_1, 23);
x_83 = lean_ctor_get(x_1, 24);
x_84 = lean_ctor_get(x_1, 25);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_1);
x_85 = l_Lean_Meta_Grind_injection_x3f(x_58, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_94 = x_86;
} else {
 lean_dec_ref(x_86);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_59);
lean_ctor_set(x_95, 2, x_60);
lean_ctor_set(x_95, 3, x_61);
lean_ctor_set(x_95, 4, x_62);
lean_ctor_set(x_95, 5, x_63);
lean_ctor_set(x_95, 6, x_64);
lean_ctor_set(x_95, 7, x_66);
lean_ctor_set(x_95, 8, x_67);
lean_ctor_set(x_95, 9, x_68);
lean_ctor_set(x_95, 10, x_69);
lean_ctor_set(x_95, 11, x_70);
lean_ctor_set(x_95, 12, x_71);
lean_ctor_set(x_95, 13, x_72);
lean_ctor_set(x_95, 14, x_73);
lean_ctor_set(x_95, 15, x_74);
lean_ctor_set(x_95, 16, x_75);
lean_ctor_set(x_95, 17, x_76);
lean_ctor_set(x_95, 18, x_77);
lean_ctor_set(x_95, 19, x_78);
lean_ctor_set(x_95, 20, x_79);
lean_ctor_set(x_95, 21, x_80);
lean_ctor_set(x_95, 22, x_81);
lean_ctor_set(x_95, 23, x_82);
lean_ctor_set(x_95, 24, x_83);
lean_ctor_set(x_95, 25, x_84);
lean_ctor_set_uint8(x_95, sizeof(void*)*26, x_65);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
if (lean_is_scalar(x_92)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_92;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_98 = lean_ctor_get(x_85, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_100 = x_85;
} else {
 lean_dec_ref(x_85);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_intros_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_15;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_intros_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_15;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_3);
x_12 = l_Lean_Meta_Grind_addHypothesis(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_st_ref_get(x_3, x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_14, 1, x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_14, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_st_ref_get(x_3, x_24);
lean_dec(x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36, lean_object* x_37, lean_object* x_38, lean_object* x_39) {
_start:
{
lean_object* x_40; 
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_1, x_2, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_43 = l_Lean_MVarId_byContra_x3f(x_3, x_35, x_36, x_37, x_38, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_st_ref_take(x_31, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_push(x_47, x_1);
x_50 = lean_st_ref_set(x_31, x_49, x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
lean_dec(x_43);
x_58 = lean_ctor_get(x_44, 0);
lean_inc(x_58);
lean_dec(x_44);
x_59 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_5);
lean_ctor_set(x_59, 3, x_6);
lean_ctor_set(x_59, 4, x_7);
lean_ctor_set(x_59, 5, x_8);
lean_ctor_set(x_59, 6, x_9);
lean_ctor_set(x_59, 7, x_11);
lean_ctor_set(x_59, 8, x_12);
lean_ctor_set(x_59, 9, x_13);
lean_ctor_set(x_59, 10, x_14);
lean_ctor_set(x_59, 11, x_15);
lean_ctor_set(x_59, 12, x_16);
lean_ctor_set(x_59, 13, x_17);
lean_ctor_set(x_59, 14, x_18);
lean_ctor_set(x_59, 15, x_19);
lean_ctor_set(x_59, 16, x_20);
lean_ctor_set(x_59, 17, x_21);
lean_ctor_set(x_59, 18, x_22);
lean_ctor_set(x_59, 19, x_23);
lean_ctor_set(x_59, 20, x_24);
lean_ctor_set(x_59, 21, x_25);
lean_ctor_set(x_59, 22, x_26);
lean_ctor_set(x_59, 23, x_27);
lean_ctor_set(x_59, 24, x_28);
lean_ctor_set(x_59, 25, x_29);
lean_ctor_set_uint8(x_59, sizeof(void*)*26, x_10);
x_60 = l_Lean_Meta_Grind_intros_go(x_2, x_59, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_57);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_43);
if (x_61 == 0)
{
return x_43;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_43, 0);
x_63 = lean_ctor_get(x_43, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_43);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 1:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
lean_dec(x_1);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec(x_40);
x_66 = lean_ctor_get(x_41, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_41, 1);
lean_inc(x_67);
lean_dec(x_41);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_66);
lean_inc(x_67);
x_68 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_67, x_66, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_66);
lean_inc(x_67);
x_71 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(x_67, x_66, x_35, x_36, x_37, x_38, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
x_75 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_75, 0, x_67);
lean_inc(x_2);
x_76 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_intros_go___lambda__1), 11, 2);
lean_closure_set(x_76, 0, x_66);
lean_closure_set(x_76, 1, x_2);
x_77 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_77, 0, x_75);
lean_closure_set(x_77, 1, x_76);
x_78 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_79 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_79, 0, x_77);
lean_closure_set(x_79, 1, x_78);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_80 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_74, x_79, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_73);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Meta_Grind_intros_go(x_2, x_81, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_82);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_67);
lean_dec(x_66);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_dec(x_71);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
lean_dec(x_72);
x_90 = l_Lean_Meta_Grind_intros_go(x_2, x_89, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_88);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_71);
if (x_91 == 0)
{
return x_71;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_71, 0);
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_71);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_67);
lean_dec(x_66);
x_95 = lean_ctor_get(x_68, 1);
lean_inc(x_95);
lean_dec(x_68);
x_96 = lean_ctor_get(x_69, 0);
lean_inc(x_96);
lean_dec(x_69);
x_97 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(x_2, x_96, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_95);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_68);
if (x_98 == 0)
{
return x_68;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_68, 0);
x_100 = lean_ctor_get(x_68, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_68);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
case 2:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
lean_dec(x_1);
x_102 = lean_ctor_get(x_40, 1);
lean_inc(x_102);
lean_dec(x_40);
x_103 = lean_ctor_get(x_41, 0);
lean_inc(x_103);
lean_dec(x_41);
x_104 = l_Lean_Meta_Grind_intros_go(x_2, x_103, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_102);
return x_104;
}
default: 
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
lean_dec(x_1);
x_105 = lean_ctor_get(x_40, 1);
lean_inc(x_105);
lean_dec(x_40);
x_106 = lean_ctor_get(x_41, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_41, 1);
lean_inc(x_107);
lean_dec(x_41);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_107);
x_108 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_107, x_106, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Meta_Grind_intros_go(x_2, x_107, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_107);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
lean_dec(x_109);
x_114 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(x_2, x_113, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_112);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_107);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
return x_108;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_108, 0);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_108);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
x_119 = !lean_is_exclusive(x_40);
if (x_119 == 0)
{
return x_40;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_40, 0);
x_121 = lean_ctor_get(x_40, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_40);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 8);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 10);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 11);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 12);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 13);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 14);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 15);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 16);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 17);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 18);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 19);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 20);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 21);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 22);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 23);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 24);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 25);
lean_inc(x_38);
x_39 = lean_box(0);
x_40 = l_Lean_Meta_Grind_intros_go___lambda__2(x_2, x_1, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_12, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
lean_object* x_34 = _args[33];
lean_object* x_35 = _args[34];
lean_object* x_36 = _args[35];
lean_object* x_37 = _args[36];
lean_object* x_38 = _args[37];
lean_object* x_39 = _args[38];
_start:
{
uint8_t x_40; lean_object* x_41; 
x_40 = lean_unbox(x_10);
lean_dec(x_10);
x_41 = l_Lean_Meta_Grind_intros_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_31);
lean_dec(x_30);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_intros_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_intros___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_Grind_intros___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Grind_intros_go(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_13, x_16);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_to_list(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_array_to_list(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_Grind_preprocess(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Meta_Simp_Result_getProof(x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Meta_mkEqMP(x_18, x_2, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_4);
x_23 = l_Lean_Meta_Grind_add(x_16, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_4, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_st_ref_get(x_4, x_27);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set(x_25, 1, x_30);
lean_ctor_set(x_28, 0, x_25);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_25, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_st_ref_get(x_4, x_35);
lean_dec(x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
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
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
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
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_assertAt___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
lean_inc(x_4);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_4, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_15, 0, x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertAt___lambda__1), 12, 3);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_3);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_14, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*26);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_21);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = l_Lean_Meta_Grind_assertAt___closed__2;
x_42 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_41, x_10, x_11, x_12);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
x_48 = lean_ctor_get(x_4, 2);
x_49 = lean_ctor_get(x_4, 3);
x_50 = lean_ctor_get(x_4, 4);
x_51 = lean_ctor_get(x_4, 5);
x_52 = lean_ctor_get(x_4, 6);
x_53 = lean_ctor_get(x_4, 7);
x_54 = lean_ctor_get(x_4, 8);
x_55 = lean_ctor_get(x_4, 9);
x_56 = lean_ctor_get(x_4, 10);
x_57 = lean_ctor_get(x_4, 11);
x_58 = lean_ctor_get(x_4, 12);
x_59 = lean_ctor_get(x_4, 13);
x_60 = lean_ctor_get(x_4, 14);
x_61 = lean_ctor_get(x_4, 15);
x_62 = lean_ctor_get(x_4, 16);
x_63 = lean_ctor_get(x_4, 17);
x_64 = lean_ctor_get(x_4, 18);
x_65 = lean_ctor_get(x_4, 19);
x_66 = lean_ctor_get(x_4, 20);
x_67 = lean_ctor_get(x_4, 21);
x_68 = lean_ctor_get(x_4, 22);
x_69 = lean_ctor_get(x_4, 23);
x_70 = lean_ctor_get(x_4, 24);
x_71 = lean_ctor_get(x_4, 25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_72 = l_Lean_MVarId_assert(x_46, x_43, x_2, x_1, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_ctor_set(x_4, 0, x_73);
x_75 = l_Lean_Meta_Grind_intros(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
return x_75;
}
else
{
uint8_t x_76; 
lean_free_object(x_4);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_80 = lean_ctor_get(x_4, 0);
x_81 = lean_ctor_get(x_4, 1);
x_82 = lean_ctor_get(x_4, 2);
x_83 = lean_ctor_get(x_4, 3);
x_84 = lean_ctor_get(x_4, 4);
x_85 = lean_ctor_get(x_4, 5);
x_86 = lean_ctor_get(x_4, 6);
x_87 = lean_ctor_get_uint8(x_4, sizeof(void*)*26);
x_88 = lean_ctor_get(x_4, 7);
x_89 = lean_ctor_get(x_4, 8);
x_90 = lean_ctor_get(x_4, 9);
x_91 = lean_ctor_get(x_4, 10);
x_92 = lean_ctor_get(x_4, 11);
x_93 = lean_ctor_get(x_4, 12);
x_94 = lean_ctor_get(x_4, 13);
x_95 = lean_ctor_get(x_4, 14);
x_96 = lean_ctor_get(x_4, 15);
x_97 = lean_ctor_get(x_4, 16);
x_98 = lean_ctor_get(x_4, 17);
x_99 = lean_ctor_get(x_4, 18);
x_100 = lean_ctor_get(x_4, 19);
x_101 = lean_ctor_get(x_4, 20);
x_102 = lean_ctor_get(x_4, 21);
x_103 = lean_ctor_get(x_4, 22);
x_104 = lean_ctor_get(x_4, 23);
x_105 = lean_ctor_get(x_4, 24);
x_106 = lean_ctor_get(x_4, 25);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_107 = l_Lean_MVarId_assert(x_80, x_43, x_2, x_1, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_81);
lean_ctor_set(x_110, 2, x_82);
lean_ctor_set(x_110, 3, x_83);
lean_ctor_set(x_110, 4, x_84);
lean_ctor_set(x_110, 5, x_85);
lean_ctor_set(x_110, 6, x_86);
lean_ctor_set(x_110, 7, x_88);
lean_ctor_set(x_110, 8, x_89);
lean_ctor_set(x_110, 9, x_90);
lean_ctor_set(x_110, 10, x_91);
lean_ctor_set(x_110, 11, x_92);
lean_ctor_set(x_110, 12, x_93);
lean_ctor_set(x_110, 13, x_94);
lean_ctor_set(x_110, 14, x_95);
lean_ctor_set(x_110, 15, x_96);
lean_ctor_set(x_110, 16, x_97);
lean_ctor_set(x_110, 17, x_98);
lean_ctor_set(x_110, 18, x_99);
lean_ctor_set(x_110, 19, x_100);
lean_ctor_set(x_110, 20, x_101);
lean_ctor_set(x_110, 21, x_102);
lean_ctor_set(x_110, 22, x_103);
lean_ctor_set(x_110, 23, x_104);
lean_ctor_set(x_110, 24, x_105);
lean_ctor_set(x_110, 25, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*26, x_87);
x_111 = l_Lean_Meta_Grind_intros(x_3, x_110, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_ctor_get(x_1, 6);
x_18 = lean_ctor_get(x_1, 7);
x_19 = lean_ctor_get(x_1, 8);
x_20 = lean_ctor_get(x_1, 9);
x_21 = lean_ctor_get(x_1, 10);
x_22 = lean_ctor_get(x_1, 11);
x_23 = lean_ctor_get(x_1, 12);
x_24 = lean_ctor_get(x_1, 13);
x_25 = lean_ctor_get(x_1, 14);
x_26 = lean_ctor_get(x_1, 15);
x_27 = lean_ctor_get(x_1, 16);
x_28 = lean_ctor_get(x_1, 17);
x_29 = lean_ctor_get(x_1, 18);
x_30 = lean_ctor_get(x_1, 19);
x_31 = lean_ctor_get(x_1, 20);
x_32 = lean_ctor_get(x_1, 21);
x_33 = lean_ctor_get(x_1, 22);
x_34 = lean_ctor_get(x_1, 23);
x_35 = lean_ctor_get(x_1, 24);
x_36 = lean_ctor_get(x_1, 25);
x_37 = l_Std_Queue_dequeue_x3f___rarg(x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_1);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
lean_dec(x_42);
lean_ctor_set(x_1, 17, x_43);
x_47 = l_Lean_Meta_Grind_assertAt(x_44, x_45, x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_37, 0, x_49);
lean_ctor_set(x_47, 0, x_37);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_37, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_free_object(x_37);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
lean_dec(x_37);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
lean_dec(x_58);
lean_ctor_set(x_1, 17, x_59);
x_63 = l_Lean_Meta_Grind_assertAt(x_60, x_61, x_62, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_ctor_get(x_1, 1);
x_75 = lean_ctor_get(x_1, 2);
x_76 = lean_ctor_get(x_1, 3);
x_77 = lean_ctor_get(x_1, 4);
x_78 = lean_ctor_get(x_1, 5);
x_79 = lean_ctor_get(x_1, 6);
x_80 = lean_ctor_get_uint8(x_1, sizeof(void*)*26);
x_81 = lean_ctor_get(x_1, 7);
x_82 = lean_ctor_get(x_1, 8);
x_83 = lean_ctor_get(x_1, 9);
x_84 = lean_ctor_get(x_1, 10);
x_85 = lean_ctor_get(x_1, 11);
x_86 = lean_ctor_get(x_1, 12);
x_87 = lean_ctor_get(x_1, 13);
x_88 = lean_ctor_get(x_1, 14);
x_89 = lean_ctor_get(x_1, 15);
x_90 = lean_ctor_get(x_1, 16);
x_91 = lean_ctor_get(x_1, 17);
x_92 = lean_ctor_get(x_1, 18);
x_93 = lean_ctor_get(x_1, 19);
x_94 = lean_ctor_get(x_1, 20);
x_95 = lean_ctor_get(x_1, 21);
x_96 = lean_ctor_get(x_1, 22);
x_97 = lean_ctor_get(x_1, 23);
x_98 = lean_ctor_get(x_1, 24);
x_99 = lean_ctor_get(x_1, 25);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_1);
x_100 = l_Std_Queue_dequeue_x3f___rarg(x_91);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_9);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 2);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_110, 0, x_73);
lean_ctor_set(x_110, 1, x_74);
lean_ctor_set(x_110, 2, x_75);
lean_ctor_set(x_110, 3, x_76);
lean_ctor_set(x_110, 4, x_77);
lean_ctor_set(x_110, 5, x_78);
lean_ctor_set(x_110, 6, x_79);
lean_ctor_set(x_110, 7, x_81);
lean_ctor_set(x_110, 8, x_82);
lean_ctor_set(x_110, 9, x_83);
lean_ctor_set(x_110, 10, x_84);
lean_ctor_set(x_110, 11, x_85);
lean_ctor_set(x_110, 12, x_86);
lean_ctor_set(x_110, 13, x_87);
lean_ctor_set(x_110, 14, x_88);
lean_ctor_set(x_110, 15, x_89);
lean_ctor_set(x_110, 16, x_90);
lean_ctor_set(x_110, 17, x_106);
lean_ctor_set(x_110, 18, x_92);
lean_ctor_set(x_110, 19, x_93);
lean_ctor_set(x_110, 20, x_94);
lean_ctor_set(x_110, 21, x_95);
lean_ctor_set(x_110, 22, x_96);
lean_ctor_set(x_110, 23, x_97);
lean_ctor_set(x_110, 24, x_98);
lean_ctor_set(x_110, 25, x_99);
lean_ctor_set_uint8(x_110, sizeof(void*)*26, x_80);
x_111 = l_Lean_Meta_Grind_assertAt(x_107, x_108, x_109, x_110, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_104;
}
lean_ctor_set(x_115, 0, x_112);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_104);
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_119 = x_111;
} else {
 lean_dec_ref(x_111);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAll___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertNext), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Grind_assertAll___closed__1;
x_11 = l_Lean_Meta_Grind_GrindTactic_iterate(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Combinators(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Combinators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedIntroResult = _init_l_Lean_Meta_Grind_instInhabitedIntroResult();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__3);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4);
l_Lean_Meta_Grind_intros___closed__1 = _init_l_Lean_Meta_Grind_intros___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_intros___closed__1);
l_Lean_Meta_Grind_assertAt___closed__1 = _init_l_Lean_Meta_Grind_assertAt___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_assertAt___closed__1);
l_Lean_Meta_Grind_assertAt___closed__2 = _init_l_Lean_Meta_Grind_assertAt___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_assertAt___closed__2);
l_Lean_Meta_Grind_assertAll___closed__1 = _init_l_Lean_Meta_Grind_assertAll___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_assertAll___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
