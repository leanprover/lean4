// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.Combinators
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
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAll___closed__1;
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_intros___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___closed__1;
lean_object* l_Lean_Meta_Grind_isGrindCasesTarget(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GrindTactic_iterate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__1;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__2;
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed(lean_object**);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__3;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_10(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__4___rarg), 11, 0);
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
lean_inc(x_5);
x_16 = l_Lean_Meta_Grind_simp(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, uint8_t x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36, lean_object* x_37) {
_start:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_LocalDecl_type(x_29);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_38);
x_39 = l_Lean_Meta_isProp(x_38, x_33, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_38);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_ctor_get(x_39, 0);
lean_dec(x_44);
lean_inc(x_1);
x_45 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set(x_45, 2, x_3);
lean_ctor_set(x_45, 3, x_4);
lean_ctor_set(x_45, 4, x_5);
lean_ctor_set(x_45, 5, x_6);
lean_ctor_set(x_45, 6, x_7);
lean_ctor_set(x_45, 7, x_9);
lean_ctor_set(x_45, 8, x_10);
lean_ctor_set(x_45, 9, x_11);
lean_ctor_set(x_45, 10, x_12);
lean_ctor_set(x_45, 11, x_13);
lean_ctor_set(x_45, 12, x_14);
lean_ctor_set(x_45, 13, x_15);
lean_ctor_set(x_45, 14, x_16);
lean_ctor_set(x_45, 15, x_17);
lean_ctor_set(x_45, 16, x_18);
lean_ctor_set(x_45, 17, x_19);
lean_ctor_set(x_45, 18, x_20);
lean_ctor_set(x_45, 19, x_21);
lean_ctor_set(x_45, 20, x_22);
lean_ctor_set(x_45, 21, x_23);
lean_ctor_set(x_45, 22, x_24);
lean_ctor_set_uint8(x_45, sizeof(void*)*23, x_8);
if (x_25 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_isLetFun(x_26);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_1);
x_47 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_39);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_48, 0, x_45);
lean_inc(x_27);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_49, 0, x_27);
lean_closure_set(x_49, 1, x_28);
x_50 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_50, 0, x_48);
lean_closure_set(x_50, 1, x_49);
x_51 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
x_53 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_52, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_43);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_27);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_59, 0, x_27);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_27);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_39);
x_65 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_65, 0, x_45);
lean_inc(x_27);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_66, 0, x_27);
lean_closure_set(x_66, 1, x_28);
x_67 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_67, 0, x_65);
lean_closure_set(x_67, 1, x_66);
x_68 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_69 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
x_70 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_69, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_43);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_73, 0, x_27);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_27);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
return x_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 0);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_39, 1);
lean_inc(x_82);
lean_dec(x_39);
lean_inc(x_1);
x_83 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_2);
lean_ctor_set(x_83, 2, x_3);
lean_ctor_set(x_83, 3, x_4);
lean_ctor_set(x_83, 4, x_5);
lean_ctor_set(x_83, 5, x_6);
lean_ctor_set(x_83, 6, x_7);
lean_ctor_set(x_83, 7, x_9);
lean_ctor_set(x_83, 8, x_10);
lean_ctor_set(x_83, 9, x_11);
lean_ctor_set(x_83, 10, x_12);
lean_ctor_set(x_83, 11, x_13);
lean_ctor_set(x_83, 12, x_14);
lean_ctor_set(x_83, 13, x_15);
lean_ctor_set(x_83, 14, x_16);
lean_ctor_set(x_83, 15, x_17);
lean_ctor_set(x_83, 16, x_18);
lean_ctor_set(x_83, 17, x_19);
lean_ctor_set(x_83, 18, x_20);
lean_ctor_set(x_83, 19, x_21);
lean_ctor_set(x_83, 20, x_22);
lean_ctor_set(x_83, 21, x_23);
lean_ctor_set(x_83, 22, x_24);
lean_ctor_set_uint8(x_83, sizeof(void*)*23, x_8);
if (x_25 == 0)
{
uint8_t x_84; 
x_84 = l_Lean_Expr_isLetFun(x_26);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_1);
x_85 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_85, 0, x_27);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_87, 0, x_83);
lean_inc(x_27);
x_88 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_88, 0, x_27);
lean_closure_set(x_88, 1, x_28);
x_89 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_89, 0, x_87);
lean_closure_set(x_89, 1, x_88);
x_90 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_91 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_91, 0, x_89);
lean_closure_set(x_91, 1, x_90);
x_92 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_91, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_82);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_96, 0, x_27);
lean_ctor_set(x_96, 1, x_93);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_27);
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_100 = x_92;
} else {
 lean_dec_ref(x_92);
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
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_102, 0, x_83);
lean_inc(x_27);
x_103 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_103, 0, x_27);
lean_closure_set(x_103, 1, x_28);
x_104 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_104, 0, x_102);
lean_closure_set(x_104, 1, x_103);
x_105 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_106 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_106, 0, x_104);
lean_closure_set(x_106, 1, x_105);
x_107 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_106, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_82);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_111, 0, x_27);
lean_ctor_set(x_111, 1, x_108);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_27);
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_115 = x_107;
} else {
 lean_dec_ref(x_107);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
x_117 = lean_ctor_get(x_39, 1);
lean_inc(x_117);
lean_dec(x_39);
x_118 = l_Lean_LocalDecl_userName(x_29);
x_119 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_118, x_35, x_36, x_117);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Expr_fvar___override(x_27);
x_123 = l_Lean_MVarId_assert(x_1, x_120, x_38, x_122, x_33, x_34, x_35, x_36, x_121);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_2);
lean_ctor_set(x_126, 2, x_3);
lean_ctor_set(x_126, 3, x_4);
lean_ctor_set(x_126, 4, x_5);
lean_ctor_set(x_126, 5, x_6);
lean_ctor_set(x_126, 6, x_7);
lean_ctor_set(x_126, 7, x_9);
lean_ctor_set(x_126, 8, x_10);
lean_ctor_set(x_126, 9, x_11);
lean_ctor_set(x_126, 10, x_12);
lean_ctor_set(x_126, 11, x_13);
lean_ctor_set(x_126, 12, x_14);
lean_ctor_set(x_126, 13, x_15);
lean_ctor_set(x_126, 14, x_16);
lean_ctor_set(x_126, 15, x_17);
lean_ctor_set(x_126, 16, x_18);
lean_ctor_set(x_126, 17, x_19);
lean_ctor_set(x_126, 18, x_20);
lean_ctor_set(x_126, 19, x_21);
lean_ctor_set(x_126, 20, x_22);
lean_ctor_set(x_126, 21, x_23);
lean_ctor_set(x_126, 22, x_24);
lean_ctor_set_uint8(x_126, sizeof(void*)*23, x_8);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_123, 0, x_127);
return x_123;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_123, 0);
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_123);
x_130 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_2);
lean_ctor_set(x_130, 2, x_3);
lean_ctor_set(x_130, 3, x_4);
lean_ctor_set(x_130, 4, x_5);
lean_ctor_set(x_130, 5, x_6);
lean_ctor_set(x_130, 6, x_7);
lean_ctor_set(x_130, 7, x_9);
lean_ctor_set(x_130, 8, x_10);
lean_ctor_set(x_130, 9, x_11);
lean_ctor_set(x_130, 10, x_12);
lean_ctor_set(x_130, 11, x_13);
lean_ctor_set(x_130, 12, x_14);
lean_ctor_set(x_130, 13, x_15);
lean_ctor_set(x_130, 14, x_16);
lean_ctor_set(x_130, 15, x_17);
lean_ctor_set(x_130, 16, x_18);
lean_ctor_set(x_130, 17, x_19);
lean_ctor_set(x_130, 18, x_20);
lean_ctor_set(x_130, 19, x_21);
lean_ctor_set(x_130, 20, x_22);
lean_ctor_set(x_130, 21, x_23);
lean_ctor_set(x_130, 22, x_24);
lean_ctor_set_uint8(x_130, sizeof(void*)*23, x_8);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
}
else
{
uint8_t x_133; 
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
x_133 = !lean_is_exclusive(x_123);
if (x_133 == 0)
{
return x_123;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_123, 0);
x_135 = lean_ctor_get(x_123, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_123);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
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
x_137 = !lean_is_exclusive(x_39);
if (x_137 == 0)
{
return x_39;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_39, 0);
x_139 = lean_ctor_get(x_39, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_39);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_ctor_get(x_25, 3);
x_31 = lean_ctor_get(x_25, 4);
x_32 = lean_ctor_get(x_25, 5);
x_33 = lean_ctor_get(x_25, 6);
x_34 = lean_ctor_get_uint8(x_25, sizeof(void*)*23);
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
x_51 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_28);
lean_ctor_set(x_51, 2, x_29);
lean_ctor_set(x_51, 3, x_30);
lean_ctor_set(x_51, 4, x_31);
lean_ctor_set(x_51, 5, x_32);
lean_ctor_set(x_51, 6, x_33);
lean_ctor_set(x_51, 7, x_35);
lean_ctor_set(x_51, 8, x_36);
lean_ctor_set(x_51, 9, x_37);
lean_ctor_set(x_51, 10, x_38);
lean_ctor_set(x_51, 11, x_39);
lean_ctor_set(x_51, 12, x_40);
lean_ctor_set(x_51, 13, x_41);
lean_ctor_set(x_51, 14, x_42);
lean_ctor_set(x_51, 15, x_43);
lean_ctor_set(x_51, 16, x_44);
lean_ctor_set(x_51, 17, x_45);
lean_ctor_set(x_51, 18, x_46);
lean_ctor_set(x_51, 19, x_47);
lean_ctor_set(x_51, 20, x_48);
lean_ctor_set(x_51, 21, x_49);
lean_ctor_set(x_51, 22, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*23, x_34);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_51);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 6);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_52, sizeof(void*)*23);
x_61 = lean_ctor_get(x_52, 7);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 8);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 9);
lean_inc(x_63);
x_64 = lean_ctor_get(x_52, 10);
lean_inc(x_64);
x_65 = lean_ctor_get(x_52, 11);
lean_inc(x_65);
x_66 = lean_ctor_get(x_52, 12);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 13);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 14);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 15);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 16);
lean_inc(x_70);
x_71 = lean_ctor_get(x_52, 17);
lean_inc(x_71);
x_72 = lean_ctor_get(x_52, 18);
lean_inc(x_72);
x_73 = lean_ctor_get(x_52, 19);
lean_inc(x_73);
x_74 = lean_ctor_get(x_52, 20);
lean_inc(x_74);
x_75 = lean_ctor_get(x_52, 21);
lean_inc(x_75);
x_76 = lean_ctor_get(x_52, 22);
lean_inc(x_76);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 lean_ctor_release(x_52, 6);
 lean_ctor_release(x_52, 7);
 lean_ctor_release(x_52, 8);
 lean_ctor_release(x_52, 9);
 lean_ctor_release(x_52, 10);
 lean_ctor_release(x_52, 11);
 lean_ctor_release(x_52, 12);
 lean_ctor_release(x_52, 13);
 lean_ctor_release(x_52, 14);
 lean_ctor_release(x_52, 15);
 lean_ctor_release(x_52, 16);
 lean_ctor_release(x_52, 17);
 lean_ctor_release(x_52, 18);
 lean_ctor_release(x_52, 19);
 lean_ctor_release(x_52, 20);
 lean_ctor_release(x_52, 21);
 lean_ctor_release(x_52, 22);
 x_77 = x_52;
} else {
 lean_dec_ref(x_52);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 23, 1);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_54);
lean_ctor_set(x_78, 2, x_55);
lean_ctor_set(x_78, 3, x_56);
lean_ctor_set(x_78, 4, x_57);
lean_ctor_set(x_78, 5, x_58);
lean_ctor_set(x_78, 6, x_59);
lean_ctor_set(x_78, 7, x_61);
lean_ctor_set(x_78, 8, x_62);
lean_ctor_set(x_78, 9, x_63);
lean_ctor_set(x_78, 10, x_64);
lean_ctor_set(x_78, 11, x_65);
lean_ctor_set(x_78, 12, x_66);
lean_ctor_set(x_78, 13, x_67);
lean_ctor_set(x_78, 14, x_68);
lean_ctor_set(x_78, 15, x_69);
lean_ctor_set(x_78, 16, x_70);
lean_ctor_set(x_78, 17, x_71);
lean_ctor_set(x_78, 18, x_72);
lean_ctor_set(x_78, 19, x_73);
lean_ctor_set(x_78, 20, x_74);
lean_ctor_set(x_78, 21, x_75);
lean_ctor_set(x_78, 22, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*23, x_60);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_78);
lean_ctor_set(x_19, 0, x_4);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_19);
lean_ctor_set(x_79, 1, x_53);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_80 = lean_ctor_get(x_19, 1);
lean_inc(x_80);
lean_dec(x_19);
x_81 = lean_st_ref_get(x_10, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 5);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 6);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_82, sizeof(void*)*23);
x_92 = lean_ctor_get(x_82, 7);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 10);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 11);
lean_inc(x_96);
x_97 = lean_ctor_get(x_82, 12);
lean_inc(x_97);
x_98 = lean_ctor_get(x_82, 13);
lean_inc(x_98);
x_99 = lean_ctor_get(x_82, 14);
lean_inc(x_99);
x_100 = lean_ctor_get(x_82, 15);
lean_inc(x_100);
x_101 = lean_ctor_get(x_82, 16);
lean_inc(x_101);
x_102 = lean_ctor_get(x_82, 17);
lean_inc(x_102);
x_103 = lean_ctor_get(x_82, 18);
lean_inc(x_103);
x_104 = lean_ctor_get(x_82, 19);
lean_inc(x_104);
x_105 = lean_ctor_get(x_82, 20);
lean_inc(x_105);
x_106 = lean_ctor_get(x_82, 21);
lean_inc(x_106);
x_107 = lean_ctor_get(x_82, 22);
lean_inc(x_107);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 lean_ctor_release(x_82, 5);
 lean_ctor_release(x_82, 6);
 lean_ctor_release(x_82, 7);
 lean_ctor_release(x_82, 8);
 lean_ctor_release(x_82, 9);
 lean_ctor_release(x_82, 10);
 lean_ctor_release(x_82, 11);
 lean_ctor_release(x_82, 12);
 lean_ctor_release(x_82, 13);
 lean_ctor_release(x_82, 14);
 lean_ctor_release(x_82, 15);
 lean_ctor_release(x_82, 16);
 lean_ctor_release(x_82, 17);
 lean_ctor_release(x_82, 18);
 lean_ctor_release(x_82, 19);
 lean_ctor_release(x_82, 20);
 lean_ctor_release(x_82, 21);
 lean_ctor_release(x_82, 22);
 x_108 = x_82;
} else {
 lean_dec_ref(x_82);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 23, 1);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_3);
lean_ctor_set(x_109, 1, x_85);
lean_ctor_set(x_109, 2, x_86);
lean_ctor_set(x_109, 3, x_87);
lean_ctor_set(x_109, 4, x_88);
lean_ctor_set(x_109, 5, x_89);
lean_ctor_set(x_109, 6, x_90);
lean_ctor_set(x_109, 7, x_92);
lean_ctor_set(x_109, 8, x_93);
lean_ctor_set(x_109, 9, x_94);
lean_ctor_set(x_109, 10, x_95);
lean_ctor_set(x_109, 11, x_96);
lean_ctor_set(x_109, 12, x_97);
lean_ctor_set(x_109, 13, x_98);
lean_ctor_set(x_109, 14, x_99);
lean_ctor_set(x_109, 15, x_100);
lean_ctor_set(x_109, 16, x_101);
lean_ctor_set(x_109, 17, x_102);
lean_ctor_set(x_109, 18, x_103);
lean_ctor_set(x_109, 19, x_104);
lean_ctor_set(x_109, 20, x_105);
lean_ctor_set(x_109, 21, x_106);
lean_ctor_set(x_109, 22, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*23, x_91);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_109);
if (lean_is_scalar(x_84)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_84;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_83);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_112 = lean_ctor_get(x_1, 0);
x_113 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4;
lean_inc(x_5);
x_114 = l_Lean_Expr_const___override(x_113, x_5);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_9);
lean_ctor_set(x_115, 1, x_5);
lean_inc(x_112);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_6);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_7);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_8);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_array_mk(x_119);
x_121 = l_Lean_mkAppN(x_114, x_120);
lean_dec(x_120);
x_122 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_2, x_121, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_122, 1);
x_125 = lean_ctor_get(x_122, 0);
lean_dec(x_125);
x_126 = lean_st_ref_get(x_10, x_124);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
lean_dec(x_130);
lean_ctor_set(x_128, 0, x_3);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 1, x_128);
lean_ctor_set(x_122, 0, x_4);
lean_ctor_set(x_126, 0, x_122);
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_131 = lean_ctor_get(x_128, 1);
x_132 = lean_ctor_get(x_128, 2);
x_133 = lean_ctor_get(x_128, 3);
x_134 = lean_ctor_get(x_128, 4);
x_135 = lean_ctor_get(x_128, 5);
x_136 = lean_ctor_get(x_128, 6);
x_137 = lean_ctor_get_uint8(x_128, sizeof(void*)*23);
x_138 = lean_ctor_get(x_128, 7);
x_139 = lean_ctor_get(x_128, 8);
x_140 = lean_ctor_get(x_128, 9);
x_141 = lean_ctor_get(x_128, 10);
x_142 = lean_ctor_get(x_128, 11);
x_143 = lean_ctor_get(x_128, 12);
x_144 = lean_ctor_get(x_128, 13);
x_145 = lean_ctor_get(x_128, 14);
x_146 = lean_ctor_get(x_128, 15);
x_147 = lean_ctor_get(x_128, 16);
x_148 = lean_ctor_get(x_128, 17);
x_149 = lean_ctor_get(x_128, 18);
x_150 = lean_ctor_get(x_128, 19);
x_151 = lean_ctor_get(x_128, 20);
x_152 = lean_ctor_get(x_128, 21);
x_153 = lean_ctor_get(x_128, 22);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_128);
x_154 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_154, 0, x_3);
lean_ctor_set(x_154, 1, x_131);
lean_ctor_set(x_154, 2, x_132);
lean_ctor_set(x_154, 3, x_133);
lean_ctor_set(x_154, 4, x_134);
lean_ctor_set(x_154, 5, x_135);
lean_ctor_set(x_154, 6, x_136);
lean_ctor_set(x_154, 7, x_138);
lean_ctor_set(x_154, 8, x_139);
lean_ctor_set(x_154, 9, x_140);
lean_ctor_set(x_154, 10, x_141);
lean_ctor_set(x_154, 11, x_142);
lean_ctor_set(x_154, 12, x_143);
lean_ctor_set(x_154, 13, x_144);
lean_ctor_set(x_154, 14, x_145);
lean_ctor_set(x_154, 15, x_146);
lean_ctor_set(x_154, 16, x_147);
lean_ctor_set(x_154, 17, x_148);
lean_ctor_set(x_154, 18, x_149);
lean_ctor_set(x_154, 19, x_150);
lean_ctor_set(x_154, 20, x_151);
lean_ctor_set(x_154, 21, x_152);
lean_ctor_set(x_154, 22, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*23, x_137);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 1, x_154);
lean_ctor_set(x_122, 0, x_4);
lean_ctor_set(x_126, 0, x_122);
return x_126;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_155 = lean_ctor_get(x_126, 0);
x_156 = lean_ctor_get(x_126, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_126);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_155, 5);
lean_inc(x_161);
x_162 = lean_ctor_get(x_155, 6);
lean_inc(x_162);
x_163 = lean_ctor_get_uint8(x_155, sizeof(void*)*23);
x_164 = lean_ctor_get(x_155, 7);
lean_inc(x_164);
x_165 = lean_ctor_get(x_155, 8);
lean_inc(x_165);
x_166 = lean_ctor_get(x_155, 9);
lean_inc(x_166);
x_167 = lean_ctor_get(x_155, 10);
lean_inc(x_167);
x_168 = lean_ctor_get(x_155, 11);
lean_inc(x_168);
x_169 = lean_ctor_get(x_155, 12);
lean_inc(x_169);
x_170 = lean_ctor_get(x_155, 13);
lean_inc(x_170);
x_171 = lean_ctor_get(x_155, 14);
lean_inc(x_171);
x_172 = lean_ctor_get(x_155, 15);
lean_inc(x_172);
x_173 = lean_ctor_get(x_155, 16);
lean_inc(x_173);
x_174 = lean_ctor_get(x_155, 17);
lean_inc(x_174);
x_175 = lean_ctor_get(x_155, 18);
lean_inc(x_175);
x_176 = lean_ctor_get(x_155, 19);
lean_inc(x_176);
x_177 = lean_ctor_get(x_155, 20);
lean_inc(x_177);
x_178 = lean_ctor_get(x_155, 21);
lean_inc(x_178);
x_179 = lean_ctor_get(x_155, 22);
lean_inc(x_179);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 lean_ctor_release(x_155, 5);
 lean_ctor_release(x_155, 6);
 lean_ctor_release(x_155, 7);
 lean_ctor_release(x_155, 8);
 lean_ctor_release(x_155, 9);
 lean_ctor_release(x_155, 10);
 lean_ctor_release(x_155, 11);
 lean_ctor_release(x_155, 12);
 lean_ctor_release(x_155, 13);
 lean_ctor_release(x_155, 14);
 lean_ctor_release(x_155, 15);
 lean_ctor_release(x_155, 16);
 lean_ctor_release(x_155, 17);
 lean_ctor_release(x_155, 18);
 lean_ctor_release(x_155, 19);
 lean_ctor_release(x_155, 20);
 lean_ctor_release(x_155, 21);
 lean_ctor_release(x_155, 22);
 x_180 = x_155;
} else {
 lean_dec_ref(x_155);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 23, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_3);
lean_ctor_set(x_181, 1, x_157);
lean_ctor_set(x_181, 2, x_158);
lean_ctor_set(x_181, 3, x_159);
lean_ctor_set(x_181, 4, x_160);
lean_ctor_set(x_181, 5, x_161);
lean_ctor_set(x_181, 6, x_162);
lean_ctor_set(x_181, 7, x_164);
lean_ctor_set(x_181, 8, x_165);
lean_ctor_set(x_181, 9, x_166);
lean_ctor_set(x_181, 10, x_167);
lean_ctor_set(x_181, 11, x_168);
lean_ctor_set(x_181, 12, x_169);
lean_ctor_set(x_181, 13, x_170);
lean_ctor_set(x_181, 14, x_171);
lean_ctor_set(x_181, 15, x_172);
lean_ctor_set(x_181, 16, x_173);
lean_ctor_set(x_181, 17, x_174);
lean_ctor_set(x_181, 18, x_175);
lean_ctor_set(x_181, 19, x_176);
lean_ctor_set(x_181, 20, x_177);
lean_ctor_set(x_181, 21, x_178);
lean_ctor_set(x_181, 22, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*23, x_163);
lean_ctor_set_tag(x_122, 1);
lean_ctor_set(x_122, 1, x_181);
lean_ctor_set(x_122, 0, x_4);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_122);
lean_ctor_set(x_182, 1, x_156);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_183 = lean_ctor_get(x_122, 1);
lean_inc(x_183);
lean_dec(x_122);
x_184 = lean_st_ref_get(x_10, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_185, 4);
lean_inc(x_191);
x_192 = lean_ctor_get(x_185, 5);
lean_inc(x_192);
x_193 = lean_ctor_get(x_185, 6);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_185, sizeof(void*)*23);
x_195 = lean_ctor_get(x_185, 7);
lean_inc(x_195);
x_196 = lean_ctor_get(x_185, 8);
lean_inc(x_196);
x_197 = lean_ctor_get(x_185, 9);
lean_inc(x_197);
x_198 = lean_ctor_get(x_185, 10);
lean_inc(x_198);
x_199 = lean_ctor_get(x_185, 11);
lean_inc(x_199);
x_200 = lean_ctor_get(x_185, 12);
lean_inc(x_200);
x_201 = lean_ctor_get(x_185, 13);
lean_inc(x_201);
x_202 = lean_ctor_get(x_185, 14);
lean_inc(x_202);
x_203 = lean_ctor_get(x_185, 15);
lean_inc(x_203);
x_204 = lean_ctor_get(x_185, 16);
lean_inc(x_204);
x_205 = lean_ctor_get(x_185, 17);
lean_inc(x_205);
x_206 = lean_ctor_get(x_185, 18);
lean_inc(x_206);
x_207 = lean_ctor_get(x_185, 19);
lean_inc(x_207);
x_208 = lean_ctor_get(x_185, 20);
lean_inc(x_208);
x_209 = lean_ctor_get(x_185, 21);
lean_inc(x_209);
x_210 = lean_ctor_get(x_185, 22);
lean_inc(x_210);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 lean_ctor_release(x_185, 5);
 lean_ctor_release(x_185, 6);
 lean_ctor_release(x_185, 7);
 lean_ctor_release(x_185, 8);
 lean_ctor_release(x_185, 9);
 lean_ctor_release(x_185, 10);
 lean_ctor_release(x_185, 11);
 lean_ctor_release(x_185, 12);
 lean_ctor_release(x_185, 13);
 lean_ctor_release(x_185, 14);
 lean_ctor_release(x_185, 15);
 lean_ctor_release(x_185, 16);
 lean_ctor_release(x_185, 17);
 lean_ctor_release(x_185, 18);
 lean_ctor_release(x_185, 19);
 lean_ctor_release(x_185, 20);
 lean_ctor_release(x_185, 21);
 lean_ctor_release(x_185, 22);
 x_211 = x_185;
} else {
 lean_dec_ref(x_185);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 23, 1);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_3);
lean_ctor_set(x_212, 1, x_188);
lean_ctor_set(x_212, 2, x_189);
lean_ctor_set(x_212, 3, x_190);
lean_ctor_set(x_212, 4, x_191);
lean_ctor_set(x_212, 5, x_192);
lean_ctor_set(x_212, 6, x_193);
lean_ctor_set(x_212, 7, x_195);
lean_ctor_set(x_212, 8, x_196);
lean_ctor_set(x_212, 9, x_197);
lean_ctor_set(x_212, 10, x_198);
lean_ctor_set(x_212, 11, x_199);
lean_ctor_set(x_212, 12, x_200);
lean_ctor_set(x_212, 13, x_201);
lean_ctor_set(x_212, 14, x_202);
lean_ctor_set(x_212, 15, x_203);
lean_ctor_set(x_212, 16, x_204);
lean_ctor_set(x_212, 17, x_205);
lean_ctor_set(x_212, 18, x_206);
lean_ctor_set(x_212, 19, x_207);
lean_ctor_set(x_212, 20, x_208);
lean_ctor_set(x_212, 21, x_209);
lean_ctor_set(x_212, 22, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*23, x_194);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_4);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_187)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_187;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_186);
return x_214;
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_39, 2);
x_46 = lean_ctor_get(x_39, 3);
x_47 = lean_ctor_get(x_39, 4);
x_48 = lean_ctor_get(x_39, 5);
x_49 = lean_ctor_get(x_39, 6);
x_50 = lean_ctor_get_uint8(x_39, sizeof(void*)*23);
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
x_67 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_67, 0, x_36);
lean_ctor_set(x_67, 1, x_44);
lean_ctor_set(x_67, 2, x_45);
lean_ctor_set(x_67, 3, x_46);
lean_ctor_set(x_67, 4, x_47);
lean_ctor_set(x_67, 5, x_48);
lean_ctor_set(x_67, 6, x_49);
lean_ctor_set(x_67, 7, x_51);
lean_ctor_set(x_67, 8, x_52);
lean_ctor_set(x_67, 9, x_53);
lean_ctor_set(x_67, 10, x_54);
lean_ctor_set(x_67, 11, x_55);
lean_ctor_set(x_67, 12, x_56);
lean_ctor_set(x_67, 13, x_57);
lean_ctor_set(x_67, 14, x_58);
lean_ctor_set(x_67, 15, x_59);
lean_ctor_set(x_67, 16, x_60);
lean_ctor_set(x_67, 17, x_61);
lean_ctor_set(x_67, 18, x_62);
lean_ctor_set(x_67, 19, x_63);
lean_ctor_set(x_67, 20, x_64);
lean_ctor_set(x_67, 21, x_65);
lean_ctor_set(x_67, 22, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*23, x_50);
lean_ctor_set_tag(x_37, 3);
lean_ctor_set(x_37, 1, x_67);
lean_ctor_set(x_37, 0, x_35);
x_11 = x_37;
x_12 = x_43;
goto block_21;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_68 = lean_ctor_get(x_37, 0);
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_37);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 6);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_68, sizeof(void*)*23);
x_77 = lean_ctor_get(x_68, 7);
lean_inc(x_77);
x_78 = lean_ctor_get(x_68, 8);
lean_inc(x_78);
x_79 = lean_ctor_get(x_68, 9);
lean_inc(x_79);
x_80 = lean_ctor_get(x_68, 10);
lean_inc(x_80);
x_81 = lean_ctor_get(x_68, 11);
lean_inc(x_81);
x_82 = lean_ctor_get(x_68, 12);
lean_inc(x_82);
x_83 = lean_ctor_get(x_68, 13);
lean_inc(x_83);
x_84 = lean_ctor_get(x_68, 14);
lean_inc(x_84);
x_85 = lean_ctor_get(x_68, 15);
lean_inc(x_85);
x_86 = lean_ctor_get(x_68, 16);
lean_inc(x_86);
x_87 = lean_ctor_get(x_68, 17);
lean_inc(x_87);
x_88 = lean_ctor_get(x_68, 18);
lean_inc(x_88);
x_89 = lean_ctor_get(x_68, 19);
lean_inc(x_89);
x_90 = lean_ctor_get(x_68, 20);
lean_inc(x_90);
x_91 = lean_ctor_get(x_68, 21);
lean_inc(x_91);
x_92 = lean_ctor_get(x_68, 22);
lean_inc(x_92);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 lean_ctor_release(x_68, 5);
 lean_ctor_release(x_68, 6);
 lean_ctor_release(x_68, 7);
 lean_ctor_release(x_68, 8);
 lean_ctor_release(x_68, 9);
 lean_ctor_release(x_68, 10);
 lean_ctor_release(x_68, 11);
 lean_ctor_release(x_68, 12);
 lean_ctor_release(x_68, 13);
 lean_ctor_release(x_68, 14);
 lean_ctor_release(x_68, 15);
 lean_ctor_release(x_68, 16);
 lean_ctor_release(x_68, 17);
 lean_ctor_release(x_68, 18);
 lean_ctor_release(x_68, 19);
 lean_ctor_release(x_68, 20);
 lean_ctor_release(x_68, 21);
 lean_ctor_release(x_68, 22);
 x_93 = x_68;
} else {
 lean_dec_ref(x_68);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 23, 1);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_36);
lean_ctor_set(x_94, 1, x_70);
lean_ctor_set(x_94, 2, x_71);
lean_ctor_set(x_94, 3, x_72);
lean_ctor_set(x_94, 4, x_73);
lean_ctor_set(x_94, 5, x_74);
lean_ctor_set(x_94, 6, x_75);
lean_ctor_set(x_94, 7, x_77);
lean_ctor_set(x_94, 8, x_78);
lean_ctor_set(x_94, 9, x_79);
lean_ctor_set(x_94, 10, x_80);
lean_ctor_set(x_94, 11, x_81);
lean_ctor_set(x_94, 12, x_82);
lean_ctor_set(x_94, 13, x_83);
lean_ctor_set(x_94, 14, x_84);
lean_ctor_set(x_94, 15, x_85);
lean_ctor_set(x_94, 16, x_86);
lean_ctor_set(x_94, 17, x_87);
lean_ctor_set(x_94, 18, x_88);
lean_ctor_set(x_94, 19, x_89);
lean_ctor_set(x_94, 20, x_90);
lean_ctor_set(x_94, 21, x_91);
lean_ctor_set(x_94, 22, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*23, x_76);
x_95 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_95, 0, x_35);
lean_ctor_set(x_95, 1, x_94);
x_11 = x_95;
x_12 = x_69;
goto block_21;
}
}
else
{
uint8_t x_96; 
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_32);
if (x_96 == 0)
{
return x_32;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_32, 0);
x_98 = lean_ctor_get(x_32, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_32);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_27, 1);
lean_inc(x_100);
lean_dec(x_27);
lean_inc(x_25);
x_101 = l_Lean_MVarId_getTag(x_25, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Expr_bindingBody_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_26);
x_105 = l_Lean_Meta_Grind_simp(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_6, 2);
lean_inc(x_111);
x_112 = l_Lean_Expr_bindingName_x21(x_1);
x_113 = lean_ctor_get(x_106, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_dec(x_106);
x_115 = l_Lean_Expr_bindingInfo_x21(x_1);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
x_117 = 0;
lean_inc(x_113);
lean_inc(x_109);
x_118 = l_Lean_LocalContext_mkLocalDecl(x_111, x_109, x_112, x_113, x_116, x_117);
x_119 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_110);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = 2;
x_123 = lean_unsigned_to_nat(0u);
lean_inc(x_104);
x_124 = l_Lean_Meta_mkFreshExprMVarAt(x_118, x_120, x_104, x_122, x_102, x_123, x_6, x_7, x_8, x_9, x_121);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ctor_get(x_124, 1);
x_128 = l_Lean_Expr_mvarId_x21(x_126);
lean_inc(x_109);
x_129 = l_Lean_Expr_fvar___override(x_109);
x_130 = lean_box(0);
lean_ctor_set_tag(x_124, 1);
lean_ctor_set(x_124, 1, x_130);
lean_ctor_set(x_124, 0, x_129);
x_131 = lean_array_mk(x_124);
x_132 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_132, 0, x_131);
lean_closure_set(x_132, 1, x_126);
x_133 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_133, 0, x_132);
lean_inc(x_128);
x_134 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 18, 8);
lean_closure_set(x_134, 0, x_114);
lean_closure_set(x_134, 1, x_25);
lean_closure_set(x_134, 2, x_128);
lean_closure_set(x_134, 3, x_109);
lean_closure_set(x_134, 4, x_130);
lean_closure_set(x_134, 5, x_104);
lean_closure_set(x_134, 6, x_113);
lean_closure_set(x_134, 7, x_26);
x_135 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg), 11, 2);
lean_closure_set(x_135, 0, x_133);
lean_closure_set(x_135, 1, x_134);
lean_inc(x_2);
x_136 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__4___rarg(x_128, x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_127);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_11 = x_137;
x_12 = x_138;
goto block_21;
}
else
{
uint8_t x_139; 
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_136);
if (x_139 == 0)
{
return x_136;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_136, 0);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_136);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_143 = lean_ctor_get(x_124, 0);
x_144 = lean_ctor_get(x_124, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_124);
x_145 = l_Lean_Expr_mvarId_x21(x_143);
lean_inc(x_109);
x_146 = l_Lean_Expr_fvar___override(x_109);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_array_mk(x_148);
x_150 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_150, 0, x_149);
lean_closure_set(x_150, 1, x_143);
x_151 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_151, 0, x_150);
lean_inc(x_145);
x_152 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 18, 8);
lean_closure_set(x_152, 0, x_114);
lean_closure_set(x_152, 1, x_25);
lean_closure_set(x_152, 2, x_145);
lean_closure_set(x_152, 3, x_109);
lean_closure_set(x_152, 4, x_147);
lean_closure_set(x_152, 5, x_104);
lean_closure_set(x_152, 6, x_113);
lean_closure_set(x_152, 7, x_26);
x_153 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg), 11, 2);
lean_closure_set(x_153, 0, x_151);
lean_closure_set(x_153, 1, x_152);
lean_inc(x_2);
x_154 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__4___rarg(x_145, x_153, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_11 = x_155;
x_12 = x_156;
goto block_21;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_159 = x_154;
} else {
 lean_dec_ref(x_154);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_104);
lean_dec(x_102);
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
x_161 = !lean_is_exclusive(x_105);
if (x_161 == 0)
{
return x_105;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_105, 0);
x_163 = lean_ctor_get(x_105, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_105);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
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
x_165 = !lean_is_exclusive(x_101);
if (x_165 == 0)
{
return x_101;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_101, 0);
x_167 = lean_ctor_get(x_101, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_101);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
uint8_t x_169; 
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
x_169 = !lean_is_exclusive(x_27);
if (x_169 == 0)
{
return x_27;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_27, 0);
x_171 = lean_ctor_get(x_27, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_27);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*23);
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
lean_inc(x_11);
x_35 = l_Lean_MVarId_getType(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_Expr_isArrow(x_37);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = l_Lean_Expr_isLet(x_37);
if (x_40 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Expr_isForall(x_37);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_isLetFun(x_37);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_37);
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
x_61 = lean_box(0);
lean_ctor_set(x_35, 0, x_61);
return x_35;
}
else
{
lean_object* x_62; 
lean_free_object(x_35);
x_62 = lean_box(0);
x_41 = x_62;
goto block_58;
}
}
else
{
lean_object* x_63; 
lean_free_object(x_35);
x_63 = lean_box(0);
x_41 = x_63;
goto block_58;
}
}
else
{
lean_object* x_64; 
lean_free_object(x_35);
x_64 = lean_box(0);
x_41 = x_64;
goto block_58;
}
block_58:
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_41);
x_42 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Meta_intro1Core(x_11, x_42, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_46);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_48, 0, x_46);
x_49 = lean_box(x_18);
x_50 = lean_box(x_40);
lean_inc(x_47);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 37, 28);
lean_closure_set(x_51, 0, x_47);
lean_closure_set(x_51, 1, x_12);
lean_closure_set(x_51, 2, x_13);
lean_closure_set(x_51, 3, x_14);
lean_closure_set(x_51, 4, x_15);
lean_closure_set(x_51, 5, x_16);
lean_closure_set(x_51, 6, x_17);
lean_closure_set(x_51, 7, x_49);
lean_closure_set(x_51, 8, x_19);
lean_closure_set(x_51, 9, x_20);
lean_closure_set(x_51, 10, x_21);
lean_closure_set(x_51, 11, x_22);
lean_closure_set(x_51, 12, x_23);
lean_closure_set(x_51, 13, x_24);
lean_closure_set(x_51, 14, x_25);
lean_closure_set(x_51, 15, x_26);
lean_closure_set(x_51, 16, x_27);
lean_closure_set(x_51, 17, x_28);
lean_closure_set(x_51, 18, x_29);
lean_closure_set(x_51, 19, x_30);
lean_closure_set(x_51, 20, x_31);
lean_closure_set(x_51, 21, x_32);
lean_closure_set(x_51, 22, x_33);
lean_closure_set(x_51, 23, x_34);
lean_closure_set(x_51, 24, x_50);
lean_closure_set(x_51, 25, x_37);
lean_closure_set(x_51, 26, x_46);
lean_closure_set(x_51, 27, x_2);
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_52, 0, x_48);
lean_closure_set(x_52, 1, x_51);
x_53 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_47, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_37);
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
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_35);
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
x_65 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_65, 0, x_1);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 10, 1);
lean_closure_set(x_66, 0, x_37);
x_67 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_67, 0, x_65);
lean_closure_set(x_67, 1, x_66);
x_68 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
return x_68;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_68, 0);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_68);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_35, 0);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_35);
x_82 = l_Lean_Expr_isArrow(x_80);
if (x_82 == 0)
{
uint8_t x_83; lean_object* x_84; 
lean_dec(x_1);
x_83 = l_Lean_Expr_isLet(x_80);
if (x_83 == 0)
{
uint8_t x_102; 
x_102 = l_Lean_Expr_isForall(x_80);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = l_Lean_Expr_isLetFun(x_80);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_80);
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
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_81);
return x_105;
}
else
{
lean_object* x_106; 
x_106 = lean_box(0);
x_84 = x_106;
goto block_101;
}
}
else
{
lean_object* x_107; 
x_107 = lean_box(0);
x_84 = x_107;
goto block_101;
}
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_84 = x_108;
goto block_101;
}
block_101:
{
uint8_t x_85; lean_object* x_86; 
lean_dec(x_84);
x_85 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_86 = l_Lean_Meta_intro1Core(x_11, x_85, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_89);
x_91 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_91, 0, x_89);
x_92 = lean_box(x_18);
x_93 = lean_box(x_83);
lean_inc(x_90);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 37, 28);
lean_closure_set(x_94, 0, x_90);
lean_closure_set(x_94, 1, x_12);
lean_closure_set(x_94, 2, x_13);
lean_closure_set(x_94, 3, x_14);
lean_closure_set(x_94, 4, x_15);
lean_closure_set(x_94, 5, x_16);
lean_closure_set(x_94, 6, x_17);
lean_closure_set(x_94, 7, x_92);
lean_closure_set(x_94, 8, x_19);
lean_closure_set(x_94, 9, x_20);
lean_closure_set(x_94, 10, x_21);
lean_closure_set(x_94, 11, x_22);
lean_closure_set(x_94, 12, x_23);
lean_closure_set(x_94, 13, x_24);
lean_closure_set(x_94, 14, x_25);
lean_closure_set(x_94, 15, x_26);
lean_closure_set(x_94, 16, x_27);
lean_closure_set(x_94, 17, x_28);
lean_closure_set(x_94, 18, x_29);
lean_closure_set(x_94, 19, x_30);
lean_closure_set(x_94, 20, x_31);
lean_closure_set(x_94, 21, x_32);
lean_closure_set(x_94, 22, x_33);
lean_closure_set(x_94, 23, x_34);
lean_closure_set(x_94, 24, x_93);
lean_closure_set(x_94, 25, x_80);
lean_closure_set(x_94, 26, x_89);
lean_closure_set(x_94, 27, x_2);
x_95 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_95, 0, x_91);
lean_closure_set(x_95, 1, x_94);
x_96 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_90, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_88);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_80);
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
x_97 = lean_ctor_get(x_86, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_86, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_99 = x_86;
} else {
 lean_dec_ref(x_86);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
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
x_109 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_109, 0, x_1);
x_110 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 10, 1);
lean_closure_set(x_110, 0, x_80);
x_111 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
x_112 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
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
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
lean_dec(x_113);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
}
else
{
uint8_t x_122; 
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
x_122 = !lean_is_exclusive(x_35);
if (x_122 == 0)
{
return x_35;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_35, 0);
x_124 = lean_ctor_get(x_35, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_35);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
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
_start:
{
uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_unbox(x_8);
lean_dec(x_8);
x_39 = lean_unbox(x_25);
lean_dec(x_25);
x_40 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_38, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_39, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
lean_dec(x_29);
lean_dec(x_26);
return x_40;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_Grind_isGrindCasesTarget(x_8, x_4, x_5, x_6);
lean_dec(x_8);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*23);
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
x_31 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set(x_31, 2, x_9);
lean_ctor_set(x_31, 3, x_10);
lean_ctor_set(x_31, 4, x_11);
lean_ctor_set(x_31, 5, x_12);
lean_ctor_set(x_31, 6, x_13);
lean_ctor_set(x_31, 7, x_15);
lean_ctor_set(x_31, 8, x_16);
lean_ctor_set(x_31, 9, x_17);
lean_ctor_set(x_31, 10, x_18);
lean_ctor_set(x_31, 11, x_19);
lean_ctor_set(x_31, 12, x_20);
lean_ctor_set(x_31, 13, x_21);
lean_ctor_set(x_31, 14, x_22);
lean_ctor_set(x_31, 15, x_23);
lean_ctor_set(x_31, 16, x_24);
lean_ctor_set(x_31, 17, x_25);
lean_ctor_set(x_31, 18, x_26);
lean_ctor_set(x_31, 19, x_27);
lean_ctor_set(x_31, 20, x_28);
lean_ctor_set(x_31, 21, x_29);
lean_ctor_set(x_31, 22, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*23, x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_31);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_ctor_get(x_1, 4);
x_39 = lean_ctor_get(x_1, 5);
x_40 = lean_ctor_get(x_1, 6);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*23);
x_42 = lean_ctor_get(x_1, 7);
x_43 = lean_ctor_get(x_1, 8);
x_44 = lean_ctor_get(x_1, 9);
x_45 = lean_ctor_get(x_1, 10);
x_46 = lean_ctor_get(x_1, 11);
x_47 = lean_ctor_get(x_1, 12);
x_48 = lean_ctor_get(x_1, 13);
x_49 = lean_ctor_get(x_1, 14);
x_50 = lean_ctor_get(x_1, 15);
x_51 = lean_ctor_get(x_1, 16);
x_52 = lean_ctor_get(x_1, 17);
x_53 = lean_ctor_get(x_1, 18);
x_54 = lean_ctor_get(x_1, 19);
x_55 = lean_ctor_get(x_1, 20);
x_56 = lean_ctor_get(x_1, 21);
x_57 = lean_ctor_get(x_1, 22);
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
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_58 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_58, 0, x_33);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set(x_58, 4, x_38);
lean_ctor_set(x_58, 5, x_39);
lean_ctor_set(x_58, 6, x_40);
lean_ctor_set(x_58, 7, x_42);
lean_ctor_set(x_58, 8, x_43);
lean_ctor_set(x_58, 9, x_44);
lean_ctor_set(x_58, 10, x_45);
lean_ctor_set(x_58, 11, x_46);
lean_ctor_set(x_58, 12, x_47);
lean_ctor_set(x_58, 13, x_48);
lean_ctor_set(x_58, 14, x_49);
lean_ctor_set(x_58, 15, x_50);
lean_ctor_set(x_58, 16, x_51);
lean_ctor_set(x_58, 17, x_52);
lean_ctor_set(x_58, 18, x_53);
lean_ctor_set(x_58, 19, x_54);
lean_ctor_set(x_58, 20, x_55);
lean_ctor_set(x_58, 21, x_56);
lean_ctor_set(x_58, 22, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*23, x_41);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
x_2 = x_34;
x_3 = x_59;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_FVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate(x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_Expr_fvar___override(x_1);
x_23 = l_Lean_Meta_Grind_cases(x_2, x_22, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_3, x_25, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_box(0);
x_32 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_3, x_29, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_32 = l_Lean_Meta_Grind_injection_x3f(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_free_object(x_1);
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
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set(x_33, 0, x_1);
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
lean_ctor_set(x_1, 0, x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_32, 0, x_45);
return x_32;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_dec(x_32);
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_48 = x_33;
} else {
 lean_dec_ref(x_33);
 x_48 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_47);
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_1);
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
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
return x_32;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_32, 0);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_32);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
x_57 = lean_ctor_get(x_1, 2);
x_58 = lean_ctor_get(x_1, 3);
x_59 = lean_ctor_get(x_1, 4);
x_60 = lean_ctor_get(x_1, 5);
x_61 = lean_ctor_get(x_1, 6);
x_62 = lean_ctor_get_uint8(x_1, sizeof(void*)*23);
x_63 = lean_ctor_get(x_1, 7);
x_64 = lean_ctor_get(x_1, 8);
x_65 = lean_ctor_get(x_1, 9);
x_66 = lean_ctor_get(x_1, 10);
x_67 = lean_ctor_get(x_1, 11);
x_68 = lean_ctor_get(x_1, 12);
x_69 = lean_ctor_get(x_1, 13);
x_70 = lean_ctor_get(x_1, 14);
x_71 = lean_ctor_get(x_1, 15);
x_72 = lean_ctor_get(x_1, 16);
x_73 = lean_ctor_get(x_1, 17);
x_74 = lean_ctor_get(x_1, 18);
x_75 = lean_ctor_get(x_1, 19);
x_76 = lean_ctor_get(x_1, 20);
x_77 = lean_ctor_get(x_1, 21);
x_78 = lean_ctor_get(x_1, 22);
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
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_1);
x_79 = l_Lean_Meta_Grind_injection_x3f(x_55, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
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
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_56);
lean_ctor_set(x_89, 2, x_57);
lean_ctor_set(x_89, 3, x_58);
lean_ctor_set(x_89, 4, x_59);
lean_ctor_set(x_89, 5, x_60);
lean_ctor_set(x_89, 6, x_61);
lean_ctor_set(x_89, 7, x_63);
lean_ctor_set(x_89, 8, x_64);
lean_ctor_set(x_89, 9, x_65);
lean_ctor_set(x_89, 10, x_66);
lean_ctor_set(x_89, 11, x_67);
lean_ctor_set(x_89, 12, x_68);
lean_ctor_set(x_89, 13, x_69);
lean_ctor_set(x_89, 14, x_70);
lean_ctor_set(x_89, 15, x_71);
lean_ctor_set(x_89, 16, x_72);
lean_ctor_set(x_89, 17, x_73);
lean_ctor_set(x_89, 18, x_74);
lean_ctor_set(x_89, 19, x_75);
lean_ctor_set(x_89, 20, x_76);
lean_ctor_set(x_89, 21, x_77);
lean_ctor_set(x_89, 22, x_78);
lean_ctor_set_uint8(x_89, sizeof(void*)*23, x_62);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
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
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_92 = lean_ctor_get(x_79, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_94 = x_79;
} else {
 lean_dec_ref(x_79);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36) {
_start:
{
lean_object* x_37; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_1, x_2, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
switch (lean_obj_tag(x_38)) {
case 0:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_40 = l_Lean_MVarId_byContra_x3f(x_3, x_32, x_33, x_34, x_35, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
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
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_take(x_28, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_array_push(x_44, x_1);
x_47 = lean_st_ref_set(x_28, x_46, x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
lean_dec(x_41);
x_56 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
lean_ctor_set(x_56, 2, x_5);
lean_ctor_set(x_56, 3, x_6);
lean_ctor_set(x_56, 4, x_7);
lean_ctor_set(x_56, 5, x_8);
lean_ctor_set(x_56, 6, x_9);
lean_ctor_set(x_56, 7, x_11);
lean_ctor_set(x_56, 8, x_12);
lean_ctor_set(x_56, 9, x_13);
lean_ctor_set(x_56, 10, x_14);
lean_ctor_set(x_56, 11, x_15);
lean_ctor_set(x_56, 12, x_16);
lean_ctor_set(x_56, 13, x_17);
lean_ctor_set(x_56, 14, x_18);
lean_ctor_set(x_56, 15, x_19);
lean_ctor_set(x_56, 16, x_20);
lean_ctor_set(x_56, 17, x_21);
lean_ctor_set(x_56, 18, x_22);
lean_ctor_set(x_56, 19, x_23);
lean_ctor_set(x_56, 20, x_24);
lean_ctor_set(x_56, 21, x_25);
lean_ctor_set(x_56, 22, x_26);
lean_ctor_set_uint8(x_56, sizeof(void*)*23, x_10);
x_57 = l_Lean_Meta_Grind_intros_go(x_2, x_56, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_54);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
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
x_58 = !lean_is_exclusive(x_40);
if (x_58 == 0)
{
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
lean_dec(x_37);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_63);
lean_inc(x_64);
x_65 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_64, x_63, x_32, x_33, x_34, x_35, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_63);
lean_inc(x_64);
x_68 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(x_64, x_63, x_32, x_33, x_34, x_35, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_72, 0, x_64);
lean_inc(x_2);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_intros_go___lambda__1), 11, 2);
lean_closure_set(x_73, 0, x_63);
lean_closure_set(x_73, 1, x_2);
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_74, 0, x_72);
lean_closure_set(x_74, 1, x_73);
x_75 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_76 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_76, 0, x_74);
lean_closure_set(x_76, 1, x_75);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_77 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_71, x_76, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_Grind_intros_go(x_2, x_78, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_77);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_64);
lean_dec(x_63);
x_85 = lean_ctor_get(x_68, 1);
lean_inc(x_85);
lean_dec(x_68);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
lean_dec(x_69);
x_87 = l_Lean_Meta_Grind_intros_go(x_2, x_86, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_85);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_68);
if (x_88 == 0)
{
return x_68;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_68, 0);
x_90 = lean_ctor_get(x_68, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_68);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_64);
lean_dec(x_63);
x_92 = lean_ctor_get(x_65, 1);
lean_inc(x_92);
lean_dec(x_65);
x_93 = lean_ctor_get(x_66, 0);
lean_inc(x_93);
lean_dec(x_66);
x_94 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(x_2, x_93, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_92);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_65);
if (x_95 == 0)
{
return x_65;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_65, 0);
x_97 = lean_ctor_get(x_65, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_65);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
case 2:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
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
x_99 = lean_ctor_get(x_37, 1);
lean_inc(x_99);
lean_dec(x_37);
x_100 = lean_ctor_get(x_38, 0);
lean_inc(x_100);
lean_dec(x_38);
x_101 = l_Lean_Meta_Grind_intros_go(x_2, x_100, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_99);
return x_101;
}
default: 
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
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
x_102 = lean_ctor_get(x_37, 1);
lean_inc(x_102);
lean_dec(x_37);
x_103 = lean_ctor_get(x_38, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_38, 1);
lean_inc(x_104);
lean_dec(x_38);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_104);
x_105 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_104, x_103, x_32, x_33, x_34, x_35, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_Grind_intros_go(x_2, x_104, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
lean_dec(x_106);
x_111 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(x_2, x_110, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_109);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_dec(x_104);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_105);
if (x_112 == 0)
{
return x_105;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_105, 0);
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_105);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
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
x_116 = !lean_is_exclusive(x_37);
if (x_116 == 0)
{
return x_37;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_37, 0);
x_118 = lean_ctor_get(x_37, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_37);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*23);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_36 = lean_box(0);
x_37 = l_Lean_Meta_Grind_intros_go___lambda__2(x_2, x_1, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_12, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_11);
return x_39;
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
_start:
{
uint8_t x_37; lean_object* x_38; 
x_37 = lean_unbox(x_10);
lean_dec(x_10);
x_38 = l_Lean_Meta_Grind_intros_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_28);
lean_dec(x_27);
return x_38;
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
lean_inc(x_6);
x_13 = l_Lean_Meta_Grind_simp(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate(x_2, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_20, 0, x_4);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertAt___lambda__1), 12, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_3);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_19, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*23);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_30);
lean_ctor_set(x_13, 0, x_26);
lean_ctor_set(x_25, 0, x_13);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_13, 0, x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_26);
lean_free_object(x_13);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_13);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_46, 0, x_4);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertAt___lambda__1), 12, 3);
lean_closure_set(x_47, 0, x_2);
lean_closure_set(x_47, 1, x_1);
lean_closure_set(x_47, 2, x_3);
x_48 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_48, 0, x_46);
lean_closure_set(x_48, 1, x_47);
x_49 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_50 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_50, 0, x_48);
lean_closure_set(x_50, 1, x_49);
x_51 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_45, x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*23);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_51, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_65 = x_51;
} else {
 lean_dec_ref(x_51);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_dec(x_13);
x_68 = l_Lean_Meta_Grind_assertAt___closed__2;
x_69 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_68, x_10, x_11, x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_4);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_73 = lean_ctor_get(x_4, 0);
x_74 = lean_ctor_get(x_4, 1);
x_75 = lean_ctor_get(x_4, 2);
x_76 = lean_ctor_get(x_4, 3);
x_77 = lean_ctor_get(x_4, 4);
x_78 = lean_ctor_get(x_4, 5);
x_79 = lean_ctor_get(x_4, 6);
x_80 = lean_ctor_get(x_4, 7);
x_81 = lean_ctor_get(x_4, 8);
x_82 = lean_ctor_get(x_4, 9);
x_83 = lean_ctor_get(x_4, 10);
x_84 = lean_ctor_get(x_4, 11);
x_85 = lean_ctor_get(x_4, 12);
x_86 = lean_ctor_get(x_4, 13);
x_87 = lean_ctor_get(x_4, 14);
x_88 = lean_ctor_get(x_4, 15);
x_89 = lean_ctor_get(x_4, 16);
x_90 = lean_ctor_get(x_4, 17);
x_91 = lean_ctor_get(x_4, 18);
x_92 = lean_ctor_get(x_4, 19);
x_93 = lean_ctor_get(x_4, 20);
x_94 = lean_ctor_get(x_4, 21);
x_95 = lean_ctor_get(x_4, 22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_96 = l_Lean_MVarId_assert(x_73, x_70, x_2, x_1, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_ctor_set(x_4, 0, x_97);
x_99 = l_Lean_Meta_Grind_intros(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_98);
return x_99;
}
else
{
uint8_t x_100; 
lean_free_object(x_4);
lean_dec(x_95);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_104 = lean_ctor_get(x_4, 0);
x_105 = lean_ctor_get(x_4, 1);
x_106 = lean_ctor_get(x_4, 2);
x_107 = lean_ctor_get(x_4, 3);
x_108 = lean_ctor_get(x_4, 4);
x_109 = lean_ctor_get(x_4, 5);
x_110 = lean_ctor_get(x_4, 6);
x_111 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_112 = lean_ctor_get(x_4, 7);
x_113 = lean_ctor_get(x_4, 8);
x_114 = lean_ctor_get(x_4, 9);
x_115 = lean_ctor_get(x_4, 10);
x_116 = lean_ctor_get(x_4, 11);
x_117 = lean_ctor_get(x_4, 12);
x_118 = lean_ctor_get(x_4, 13);
x_119 = lean_ctor_get(x_4, 14);
x_120 = lean_ctor_get(x_4, 15);
x_121 = lean_ctor_get(x_4, 16);
x_122 = lean_ctor_get(x_4, 17);
x_123 = lean_ctor_get(x_4, 18);
x_124 = lean_ctor_get(x_4, 19);
x_125 = lean_ctor_get(x_4, 20);
x_126 = lean_ctor_get(x_4, 21);
x_127 = lean_ctor_get(x_4, 22);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_128 = l_Lean_MVarId_assert(x_104, x_70, x_2, x_1, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_105);
lean_ctor_set(x_131, 2, x_106);
lean_ctor_set(x_131, 3, x_107);
lean_ctor_set(x_131, 4, x_108);
lean_ctor_set(x_131, 5, x_109);
lean_ctor_set(x_131, 6, x_110);
lean_ctor_set(x_131, 7, x_112);
lean_ctor_set(x_131, 8, x_113);
lean_ctor_set(x_131, 9, x_114);
lean_ctor_set(x_131, 10, x_115);
lean_ctor_set(x_131, 11, x_116);
lean_ctor_set(x_131, 12, x_117);
lean_ctor_set(x_131, 13, x_118);
lean_ctor_set(x_131, 14, x_119);
lean_ctor_set(x_131, 15, x_120);
lean_ctor_set(x_131, 16, x_121);
lean_ctor_set(x_131, 17, x_122);
lean_ctor_set(x_131, 18, x_123);
lean_ctor_set(x_131, 19, x_124);
lean_ctor_set(x_131, 20, x_125);
lean_ctor_set(x_131, 21, x_126);
lean_ctor_set(x_131, 22, x_127);
lean_ctor_set_uint8(x_131, sizeof(void*)*23, x_111);
x_132 = l_Lean_Meta_Grind_intros(x_3, x_131, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_130);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_135 = x_128;
} else {
 lean_dec_ref(x_128);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
x_34 = l_Std_Queue_dequeue_x3f___rarg(x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_1);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
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
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
lean_dec(x_39);
lean_ctor_set(x_1, 16, x_40);
x_44 = l_Lean_Meta_Grind_assertAt(x_41, x_42, x_43, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set(x_34, 0, x_46);
lean_ctor_set(x_44, 0, x_34);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_34, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_free_object(x_34);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_34, 0);
lean_inc(x_54);
lean_dec(x_34);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 2);
lean_inc(x_59);
lean_dec(x_55);
lean_ctor_set(x_1, 16, x_56);
x_60 = l_Lean_Meta_Grind_assertAt(x_57, x_58, x_59, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_61);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
x_72 = lean_ctor_get(x_1, 2);
x_73 = lean_ctor_get(x_1, 3);
x_74 = lean_ctor_get(x_1, 4);
x_75 = lean_ctor_get(x_1, 5);
x_76 = lean_ctor_get(x_1, 6);
x_77 = lean_ctor_get_uint8(x_1, sizeof(void*)*23);
x_78 = lean_ctor_get(x_1, 7);
x_79 = lean_ctor_get(x_1, 8);
x_80 = lean_ctor_get(x_1, 9);
x_81 = lean_ctor_get(x_1, 10);
x_82 = lean_ctor_get(x_1, 11);
x_83 = lean_ctor_get(x_1, 12);
x_84 = lean_ctor_get(x_1, 13);
x_85 = lean_ctor_get(x_1, 14);
x_86 = lean_ctor_get(x_1, 15);
x_87 = lean_ctor_get(x_1, 16);
x_88 = lean_ctor_get(x_1, 17);
x_89 = lean_ctor_get(x_1, 18);
x_90 = lean_ctor_get(x_1, 19);
x_91 = lean_ctor_get(x_1, 20);
x_92 = lean_ctor_get(x_1, 21);
x_93 = lean_ctor_get(x_1, 22);
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
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_1);
x_94 = l_Std_Queue_dequeue_x3f___rarg(x_87);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
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
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_9);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 2);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_alloc_ctor(0, 23, 1);
lean_ctor_set(x_104, 0, x_70);
lean_ctor_set(x_104, 1, x_71);
lean_ctor_set(x_104, 2, x_72);
lean_ctor_set(x_104, 3, x_73);
lean_ctor_set(x_104, 4, x_74);
lean_ctor_set(x_104, 5, x_75);
lean_ctor_set(x_104, 6, x_76);
lean_ctor_set(x_104, 7, x_78);
lean_ctor_set(x_104, 8, x_79);
lean_ctor_set(x_104, 9, x_80);
lean_ctor_set(x_104, 10, x_81);
lean_ctor_set(x_104, 11, x_82);
lean_ctor_set(x_104, 12, x_83);
lean_ctor_set(x_104, 13, x_84);
lean_ctor_set(x_104, 14, x_85);
lean_ctor_set(x_104, 15, x_86);
lean_ctor_set(x_104, 16, x_100);
lean_ctor_set(x_104, 17, x_88);
lean_ctor_set(x_104, 18, x_89);
lean_ctor_set(x_104, 19, x_90);
lean_ctor_set(x_104, 20, x_91);
lean_ctor_set(x_104, 21, x_92);
lean_ctor_set(x_104, 22, x_93);
lean_ctor_set_uint8(x_104, sizeof(void*)*23, x_77);
x_105 = l_Lean_Meta_Grind_assertAt(x_101, x_102, x_103, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_98;
}
lean_ctor_set(x_109, 0, x_106);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_98);
x_111 = lean_ctor_get(x_105, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_113 = x_105;
} else {
 lean_dec_ref(x_105);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
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
