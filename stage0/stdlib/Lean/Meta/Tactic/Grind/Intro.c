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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isEagerCasesCandidate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed(lean_object**);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, uint8_t x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36, lean_object* x_37, lean_object* x_38, lean_object* x_39) {
_start:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_LocalDecl_type(x_31);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_40);
x_41 = l_Lean_Meta_isProp(x_40, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_40);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
lean_inc(x_1);
x_47 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_2);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_4);
lean_ctor_set(x_47, 4, x_5);
lean_ctor_set(x_47, 5, x_6);
lean_ctor_set(x_47, 6, x_7);
lean_ctor_set(x_47, 7, x_9);
lean_ctor_set(x_47, 8, x_10);
lean_ctor_set(x_47, 9, x_11);
lean_ctor_set(x_47, 10, x_12);
lean_ctor_set(x_47, 11, x_13);
lean_ctor_set(x_47, 12, x_14);
lean_ctor_set(x_47, 13, x_15);
lean_ctor_set(x_47, 14, x_16);
lean_ctor_set(x_47, 15, x_17);
lean_ctor_set(x_47, 16, x_18);
lean_ctor_set(x_47, 17, x_19);
lean_ctor_set(x_47, 18, x_20);
lean_ctor_set(x_47, 19, x_21);
lean_ctor_set(x_47, 20, x_22);
lean_ctor_set(x_47, 21, x_23);
lean_ctor_set(x_47, 22, x_24);
lean_ctor_set(x_47, 23, x_25);
lean_ctor_set(x_47, 24, x_26);
lean_ctor_set_uint8(x_47, sizeof(void*)*25, x_8);
if (x_27 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_isLetFun(x_28);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_1);
x_49 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_49, 0, x_29);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_41);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_50, 0, x_47);
lean_inc(x_29);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_51, 0, x_29);
lean_closure_set(x_51, 1, x_30);
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
x_53 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_54 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_54, 0, x_52);
lean_closure_set(x_54, 1, x_53);
x_55 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_54, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_45);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_58, 0, x_29);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_61, 0, x_29);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_29);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
return x_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_41);
x_67 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_67, 0, x_47);
lean_inc(x_29);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_68, 0, x_29);
lean_closure_set(x_68, 1, x_30);
x_69 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
x_70 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_71 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_71, 0, x_69);
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_71, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_45);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_75, 0, x_29);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_78, 0, x_29);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_29);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
return x_72;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_72);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_41, 1);
lean_inc(x_84);
lean_dec(x_41);
lean_inc(x_1);
x_85 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_2);
lean_ctor_set(x_85, 2, x_3);
lean_ctor_set(x_85, 3, x_4);
lean_ctor_set(x_85, 4, x_5);
lean_ctor_set(x_85, 5, x_6);
lean_ctor_set(x_85, 6, x_7);
lean_ctor_set(x_85, 7, x_9);
lean_ctor_set(x_85, 8, x_10);
lean_ctor_set(x_85, 9, x_11);
lean_ctor_set(x_85, 10, x_12);
lean_ctor_set(x_85, 11, x_13);
lean_ctor_set(x_85, 12, x_14);
lean_ctor_set(x_85, 13, x_15);
lean_ctor_set(x_85, 14, x_16);
lean_ctor_set(x_85, 15, x_17);
lean_ctor_set(x_85, 16, x_18);
lean_ctor_set(x_85, 17, x_19);
lean_ctor_set(x_85, 18, x_20);
lean_ctor_set(x_85, 19, x_21);
lean_ctor_set(x_85, 20, x_22);
lean_ctor_set(x_85, 21, x_23);
lean_ctor_set(x_85, 22, x_24);
lean_ctor_set(x_85, 23, x_25);
lean_ctor_set(x_85, 24, x_26);
lean_ctor_set_uint8(x_85, sizeof(void*)*25, x_8);
if (x_27 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Expr_isLetFun(x_28);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_1);
x_87 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_87, 0, x_29);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_89, 0, x_85);
lean_inc(x_29);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_90, 0, x_29);
lean_closure_set(x_90, 1, x_30);
x_91 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_91, 0, x_89);
lean_closure_set(x_91, 1, x_90);
x_92 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_93 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_93, 0, x_91);
lean_closure_set(x_93, 1, x_92);
x_94 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_93, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_84);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_98, 0, x_29);
lean_ctor_set(x_98, 1, x_95);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_29);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
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
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_104, 0, x_85);
lean_inc(x_29);
x_105 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 11, 2);
lean_closure_set(x_105, 0, x_29);
lean_closure_set(x_105, 1, x_30);
x_106 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_106, 0, x_104);
lean_closure_set(x_106, 1, x_105);
x_107 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_108 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_108, 0, x_106);
lean_closure_set(x_108, 1, x_107);
x_109 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_108, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_84);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_113, 0, x_29);
lean_ctor_set(x_113, 1, x_110);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_29);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
x_119 = lean_ctor_get(x_41, 1);
lean_inc(x_119);
lean_dec(x_41);
x_120 = l_Lean_LocalDecl_userName(x_31);
x_121 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_120, x_37, x_38, x_119);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_Expr_fvar___override(x_29);
x_125 = l_Lean_MVarId_assert(x_1, x_122, x_40, x_124, x_35, x_36, x_37, x_38, x_123);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_2);
lean_ctor_set(x_128, 2, x_3);
lean_ctor_set(x_128, 3, x_4);
lean_ctor_set(x_128, 4, x_5);
lean_ctor_set(x_128, 5, x_6);
lean_ctor_set(x_128, 6, x_7);
lean_ctor_set(x_128, 7, x_9);
lean_ctor_set(x_128, 8, x_10);
lean_ctor_set(x_128, 9, x_11);
lean_ctor_set(x_128, 10, x_12);
lean_ctor_set(x_128, 11, x_13);
lean_ctor_set(x_128, 12, x_14);
lean_ctor_set(x_128, 13, x_15);
lean_ctor_set(x_128, 14, x_16);
lean_ctor_set(x_128, 15, x_17);
lean_ctor_set(x_128, 16, x_18);
lean_ctor_set(x_128, 17, x_19);
lean_ctor_set(x_128, 18, x_20);
lean_ctor_set(x_128, 19, x_21);
lean_ctor_set(x_128, 20, x_22);
lean_ctor_set(x_128, 21, x_23);
lean_ctor_set(x_128, 22, x_24);
lean_ctor_set(x_128, 23, x_25);
lean_ctor_set(x_128, 24, x_26);
lean_ctor_set_uint8(x_128, sizeof(void*)*25, x_8);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_125, 0, x_129);
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_125);
x_132 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_2);
lean_ctor_set(x_132, 2, x_3);
lean_ctor_set(x_132, 3, x_4);
lean_ctor_set(x_132, 4, x_5);
lean_ctor_set(x_132, 5, x_6);
lean_ctor_set(x_132, 6, x_7);
lean_ctor_set(x_132, 7, x_9);
lean_ctor_set(x_132, 8, x_10);
lean_ctor_set(x_132, 9, x_11);
lean_ctor_set(x_132, 10, x_12);
lean_ctor_set(x_132, 11, x_13);
lean_ctor_set(x_132, 12, x_14);
lean_ctor_set(x_132, 13, x_15);
lean_ctor_set(x_132, 14, x_16);
lean_ctor_set(x_132, 15, x_17);
lean_ctor_set(x_132, 16, x_18);
lean_ctor_set(x_132, 17, x_19);
lean_ctor_set(x_132, 18, x_20);
lean_ctor_set(x_132, 19, x_21);
lean_ctor_set(x_132, 20, x_22);
lean_ctor_set(x_132, 21, x_23);
lean_ctor_set(x_132, 22, x_24);
lean_ctor_set(x_132, 23, x_25);
lean_ctor_set(x_132, 24, x_26);
lean_ctor_set_uint8(x_132, sizeof(void*)*25, x_8);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
else
{
uint8_t x_135; 
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
x_135 = !lean_is_exclusive(x_125);
if (x_135 == 0)
{
return x_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_125, 0);
x_137 = lean_ctor_get(x_125, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_125);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_41);
if (x_139 == 0)
{
return x_41;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_41, 0);
x_141 = lean_ctor_get(x_41, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_41);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_ctor_get(x_25, 3);
x_31 = lean_ctor_get(x_25, 4);
x_32 = lean_ctor_get(x_25, 5);
x_33 = lean_ctor_get(x_25, 6);
x_34 = lean_ctor_get_uint8(x_25, sizeof(void*)*25);
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
x_53 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_28);
lean_ctor_set(x_53, 2, x_29);
lean_ctor_set(x_53, 3, x_30);
lean_ctor_set(x_53, 4, x_31);
lean_ctor_set(x_53, 5, x_32);
lean_ctor_set(x_53, 6, x_33);
lean_ctor_set(x_53, 7, x_35);
lean_ctor_set(x_53, 8, x_36);
lean_ctor_set(x_53, 9, x_37);
lean_ctor_set(x_53, 10, x_38);
lean_ctor_set(x_53, 11, x_39);
lean_ctor_set(x_53, 12, x_40);
lean_ctor_set(x_53, 13, x_41);
lean_ctor_set(x_53, 14, x_42);
lean_ctor_set(x_53, 15, x_43);
lean_ctor_set(x_53, 16, x_44);
lean_ctor_set(x_53, 17, x_45);
lean_ctor_set(x_53, 18, x_46);
lean_ctor_set(x_53, 19, x_47);
lean_ctor_set(x_53, 20, x_48);
lean_ctor_set(x_53, 21, x_49);
lean_ctor_set(x_53, 22, x_50);
lean_ctor_set(x_53, 23, x_51);
lean_ctor_set(x_53, 24, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*25, x_34);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_53);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 5);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 6);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_54, sizeof(void*)*25);
x_63 = lean_ctor_get(x_54, 7);
lean_inc(x_63);
x_64 = lean_ctor_get(x_54, 8);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 9);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 10);
lean_inc(x_66);
x_67 = lean_ctor_get(x_54, 11);
lean_inc(x_67);
x_68 = lean_ctor_get(x_54, 12);
lean_inc(x_68);
x_69 = lean_ctor_get(x_54, 13);
lean_inc(x_69);
x_70 = lean_ctor_get(x_54, 14);
lean_inc(x_70);
x_71 = lean_ctor_get(x_54, 15);
lean_inc(x_71);
x_72 = lean_ctor_get(x_54, 16);
lean_inc(x_72);
x_73 = lean_ctor_get(x_54, 17);
lean_inc(x_73);
x_74 = lean_ctor_get(x_54, 18);
lean_inc(x_74);
x_75 = lean_ctor_get(x_54, 19);
lean_inc(x_75);
x_76 = lean_ctor_get(x_54, 20);
lean_inc(x_76);
x_77 = lean_ctor_get(x_54, 21);
lean_inc(x_77);
x_78 = lean_ctor_get(x_54, 22);
lean_inc(x_78);
x_79 = lean_ctor_get(x_54, 23);
lean_inc(x_79);
x_80 = lean_ctor_get(x_54, 24);
lean_inc(x_80);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 lean_ctor_release(x_54, 6);
 lean_ctor_release(x_54, 7);
 lean_ctor_release(x_54, 8);
 lean_ctor_release(x_54, 9);
 lean_ctor_release(x_54, 10);
 lean_ctor_release(x_54, 11);
 lean_ctor_release(x_54, 12);
 lean_ctor_release(x_54, 13);
 lean_ctor_release(x_54, 14);
 lean_ctor_release(x_54, 15);
 lean_ctor_release(x_54, 16);
 lean_ctor_release(x_54, 17);
 lean_ctor_release(x_54, 18);
 lean_ctor_release(x_54, 19);
 lean_ctor_release(x_54, 20);
 lean_ctor_release(x_54, 21);
 lean_ctor_release(x_54, 22);
 lean_ctor_release(x_54, 23);
 lean_ctor_release(x_54, 24);
 x_81 = x_54;
} else {
 lean_dec_ref(x_54);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 25, 1);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_56);
lean_ctor_set(x_82, 2, x_57);
lean_ctor_set(x_82, 3, x_58);
lean_ctor_set(x_82, 4, x_59);
lean_ctor_set(x_82, 5, x_60);
lean_ctor_set(x_82, 6, x_61);
lean_ctor_set(x_82, 7, x_63);
lean_ctor_set(x_82, 8, x_64);
lean_ctor_set(x_82, 9, x_65);
lean_ctor_set(x_82, 10, x_66);
lean_ctor_set(x_82, 11, x_67);
lean_ctor_set(x_82, 12, x_68);
lean_ctor_set(x_82, 13, x_69);
lean_ctor_set(x_82, 14, x_70);
lean_ctor_set(x_82, 15, x_71);
lean_ctor_set(x_82, 16, x_72);
lean_ctor_set(x_82, 17, x_73);
lean_ctor_set(x_82, 18, x_74);
lean_ctor_set(x_82, 19, x_75);
lean_ctor_set(x_82, 20, x_76);
lean_ctor_set(x_82, 21, x_77);
lean_ctor_set(x_82, 22, x_78);
lean_ctor_set(x_82, 23, x_79);
lean_ctor_set(x_82, 24, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*25, x_62);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_82);
lean_ctor_set(x_19, 0, x_4);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_19);
lean_ctor_set(x_83, 1, x_55);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_84 = lean_ctor_get(x_19, 1);
lean_inc(x_84);
lean_dec(x_19);
x_85 = lean_st_ref_get(x_10, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
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
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_86, 6);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_86, sizeof(void*)*25);
x_96 = lean_ctor_get(x_86, 7);
lean_inc(x_96);
x_97 = lean_ctor_get(x_86, 8);
lean_inc(x_97);
x_98 = lean_ctor_get(x_86, 9);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 10);
lean_inc(x_99);
x_100 = lean_ctor_get(x_86, 11);
lean_inc(x_100);
x_101 = lean_ctor_get(x_86, 12);
lean_inc(x_101);
x_102 = lean_ctor_get(x_86, 13);
lean_inc(x_102);
x_103 = lean_ctor_get(x_86, 14);
lean_inc(x_103);
x_104 = lean_ctor_get(x_86, 15);
lean_inc(x_104);
x_105 = lean_ctor_get(x_86, 16);
lean_inc(x_105);
x_106 = lean_ctor_get(x_86, 17);
lean_inc(x_106);
x_107 = lean_ctor_get(x_86, 18);
lean_inc(x_107);
x_108 = lean_ctor_get(x_86, 19);
lean_inc(x_108);
x_109 = lean_ctor_get(x_86, 20);
lean_inc(x_109);
x_110 = lean_ctor_get(x_86, 21);
lean_inc(x_110);
x_111 = lean_ctor_get(x_86, 22);
lean_inc(x_111);
x_112 = lean_ctor_get(x_86, 23);
lean_inc(x_112);
x_113 = lean_ctor_get(x_86, 24);
lean_inc(x_113);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 lean_ctor_release(x_86, 6);
 lean_ctor_release(x_86, 7);
 lean_ctor_release(x_86, 8);
 lean_ctor_release(x_86, 9);
 lean_ctor_release(x_86, 10);
 lean_ctor_release(x_86, 11);
 lean_ctor_release(x_86, 12);
 lean_ctor_release(x_86, 13);
 lean_ctor_release(x_86, 14);
 lean_ctor_release(x_86, 15);
 lean_ctor_release(x_86, 16);
 lean_ctor_release(x_86, 17);
 lean_ctor_release(x_86, 18);
 lean_ctor_release(x_86, 19);
 lean_ctor_release(x_86, 20);
 lean_ctor_release(x_86, 21);
 lean_ctor_release(x_86, 22);
 lean_ctor_release(x_86, 23);
 lean_ctor_release(x_86, 24);
 x_114 = x_86;
} else {
 lean_dec_ref(x_86);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 25, 1);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_3);
lean_ctor_set(x_115, 1, x_89);
lean_ctor_set(x_115, 2, x_90);
lean_ctor_set(x_115, 3, x_91);
lean_ctor_set(x_115, 4, x_92);
lean_ctor_set(x_115, 5, x_93);
lean_ctor_set(x_115, 6, x_94);
lean_ctor_set(x_115, 7, x_96);
lean_ctor_set(x_115, 8, x_97);
lean_ctor_set(x_115, 9, x_98);
lean_ctor_set(x_115, 10, x_99);
lean_ctor_set(x_115, 11, x_100);
lean_ctor_set(x_115, 12, x_101);
lean_ctor_set(x_115, 13, x_102);
lean_ctor_set(x_115, 14, x_103);
lean_ctor_set(x_115, 15, x_104);
lean_ctor_set(x_115, 16, x_105);
lean_ctor_set(x_115, 17, x_106);
lean_ctor_set(x_115, 18, x_107);
lean_ctor_set(x_115, 19, x_108);
lean_ctor_set(x_115, 20, x_109);
lean_ctor_set(x_115, 21, x_110);
lean_ctor_set(x_115, 22, x_111);
lean_ctor_set(x_115, 23, x_112);
lean_ctor_set(x_115, 24, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*25, x_95);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_4);
lean_ctor_set(x_116, 1, x_115);
if (lean_is_scalar(x_88)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_88;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_87);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_118 = lean_ctor_get(x_1, 0);
x_119 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___closed__4;
lean_inc(x_5);
x_120 = l_Lean_Expr_const___override(x_119, x_5);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_9);
lean_ctor_set(x_121, 1, x_5);
lean_inc(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_6);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_7);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_8);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_mk(x_125);
x_127 = l_Lean_mkAppN(x_120, x_126);
lean_dec(x_126);
x_128 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_2, x_127, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_128, 1);
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
x_132 = lean_st_ref_get(x_10, x_130);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_134, 0);
lean_dec(x_136);
lean_ctor_set(x_134, 0, x_3);
lean_ctor_set_tag(x_128, 1);
lean_ctor_set(x_128, 1, x_134);
lean_ctor_set(x_128, 0, x_4);
lean_ctor_set(x_132, 0, x_128);
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_ctor_get(x_134, 2);
x_139 = lean_ctor_get(x_134, 3);
x_140 = lean_ctor_get(x_134, 4);
x_141 = lean_ctor_get(x_134, 5);
x_142 = lean_ctor_get(x_134, 6);
x_143 = lean_ctor_get_uint8(x_134, sizeof(void*)*25);
x_144 = lean_ctor_get(x_134, 7);
x_145 = lean_ctor_get(x_134, 8);
x_146 = lean_ctor_get(x_134, 9);
x_147 = lean_ctor_get(x_134, 10);
x_148 = lean_ctor_get(x_134, 11);
x_149 = lean_ctor_get(x_134, 12);
x_150 = lean_ctor_get(x_134, 13);
x_151 = lean_ctor_get(x_134, 14);
x_152 = lean_ctor_get(x_134, 15);
x_153 = lean_ctor_get(x_134, 16);
x_154 = lean_ctor_get(x_134, 17);
x_155 = lean_ctor_get(x_134, 18);
x_156 = lean_ctor_get(x_134, 19);
x_157 = lean_ctor_get(x_134, 20);
x_158 = lean_ctor_get(x_134, 21);
x_159 = lean_ctor_get(x_134, 22);
x_160 = lean_ctor_get(x_134, 23);
x_161 = lean_ctor_get(x_134, 24);
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
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_134);
x_162 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_162, 0, x_3);
lean_ctor_set(x_162, 1, x_137);
lean_ctor_set(x_162, 2, x_138);
lean_ctor_set(x_162, 3, x_139);
lean_ctor_set(x_162, 4, x_140);
lean_ctor_set(x_162, 5, x_141);
lean_ctor_set(x_162, 6, x_142);
lean_ctor_set(x_162, 7, x_144);
lean_ctor_set(x_162, 8, x_145);
lean_ctor_set(x_162, 9, x_146);
lean_ctor_set(x_162, 10, x_147);
lean_ctor_set(x_162, 11, x_148);
lean_ctor_set(x_162, 12, x_149);
lean_ctor_set(x_162, 13, x_150);
lean_ctor_set(x_162, 14, x_151);
lean_ctor_set(x_162, 15, x_152);
lean_ctor_set(x_162, 16, x_153);
lean_ctor_set(x_162, 17, x_154);
lean_ctor_set(x_162, 18, x_155);
lean_ctor_set(x_162, 19, x_156);
lean_ctor_set(x_162, 20, x_157);
lean_ctor_set(x_162, 21, x_158);
lean_ctor_set(x_162, 22, x_159);
lean_ctor_set(x_162, 23, x_160);
lean_ctor_set(x_162, 24, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*25, x_143);
lean_ctor_set_tag(x_128, 1);
lean_ctor_set(x_128, 1, x_162);
lean_ctor_set(x_128, 0, x_4);
lean_ctor_set(x_132, 0, x_128);
return x_132;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_163 = lean_ctor_get(x_132, 0);
x_164 = lean_ctor_get(x_132, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_132);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_163, 6);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_163, sizeof(void*)*25);
x_172 = lean_ctor_get(x_163, 7);
lean_inc(x_172);
x_173 = lean_ctor_get(x_163, 8);
lean_inc(x_173);
x_174 = lean_ctor_get(x_163, 9);
lean_inc(x_174);
x_175 = lean_ctor_get(x_163, 10);
lean_inc(x_175);
x_176 = lean_ctor_get(x_163, 11);
lean_inc(x_176);
x_177 = lean_ctor_get(x_163, 12);
lean_inc(x_177);
x_178 = lean_ctor_get(x_163, 13);
lean_inc(x_178);
x_179 = lean_ctor_get(x_163, 14);
lean_inc(x_179);
x_180 = lean_ctor_get(x_163, 15);
lean_inc(x_180);
x_181 = lean_ctor_get(x_163, 16);
lean_inc(x_181);
x_182 = lean_ctor_get(x_163, 17);
lean_inc(x_182);
x_183 = lean_ctor_get(x_163, 18);
lean_inc(x_183);
x_184 = lean_ctor_get(x_163, 19);
lean_inc(x_184);
x_185 = lean_ctor_get(x_163, 20);
lean_inc(x_185);
x_186 = lean_ctor_get(x_163, 21);
lean_inc(x_186);
x_187 = lean_ctor_get(x_163, 22);
lean_inc(x_187);
x_188 = lean_ctor_get(x_163, 23);
lean_inc(x_188);
x_189 = lean_ctor_get(x_163, 24);
lean_inc(x_189);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 lean_ctor_release(x_163, 5);
 lean_ctor_release(x_163, 6);
 lean_ctor_release(x_163, 7);
 lean_ctor_release(x_163, 8);
 lean_ctor_release(x_163, 9);
 lean_ctor_release(x_163, 10);
 lean_ctor_release(x_163, 11);
 lean_ctor_release(x_163, 12);
 lean_ctor_release(x_163, 13);
 lean_ctor_release(x_163, 14);
 lean_ctor_release(x_163, 15);
 lean_ctor_release(x_163, 16);
 lean_ctor_release(x_163, 17);
 lean_ctor_release(x_163, 18);
 lean_ctor_release(x_163, 19);
 lean_ctor_release(x_163, 20);
 lean_ctor_release(x_163, 21);
 lean_ctor_release(x_163, 22);
 lean_ctor_release(x_163, 23);
 lean_ctor_release(x_163, 24);
 x_190 = x_163;
} else {
 lean_dec_ref(x_163);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 25, 1);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_3);
lean_ctor_set(x_191, 1, x_165);
lean_ctor_set(x_191, 2, x_166);
lean_ctor_set(x_191, 3, x_167);
lean_ctor_set(x_191, 4, x_168);
lean_ctor_set(x_191, 5, x_169);
lean_ctor_set(x_191, 6, x_170);
lean_ctor_set(x_191, 7, x_172);
lean_ctor_set(x_191, 8, x_173);
lean_ctor_set(x_191, 9, x_174);
lean_ctor_set(x_191, 10, x_175);
lean_ctor_set(x_191, 11, x_176);
lean_ctor_set(x_191, 12, x_177);
lean_ctor_set(x_191, 13, x_178);
lean_ctor_set(x_191, 14, x_179);
lean_ctor_set(x_191, 15, x_180);
lean_ctor_set(x_191, 16, x_181);
lean_ctor_set(x_191, 17, x_182);
lean_ctor_set(x_191, 18, x_183);
lean_ctor_set(x_191, 19, x_184);
lean_ctor_set(x_191, 20, x_185);
lean_ctor_set(x_191, 21, x_186);
lean_ctor_set(x_191, 22, x_187);
lean_ctor_set(x_191, 23, x_188);
lean_ctor_set(x_191, 24, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*25, x_171);
lean_ctor_set_tag(x_128, 1);
lean_ctor_set(x_128, 1, x_191);
lean_ctor_set(x_128, 0, x_4);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_128);
lean_ctor_set(x_192, 1, x_164);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_193 = lean_ctor_get(x_128, 1);
lean_inc(x_193);
lean_dec(x_128);
x_194 = lean_st_ref_get(x_10, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_195, 5);
lean_inc(x_202);
x_203 = lean_ctor_get(x_195, 6);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_195, sizeof(void*)*25);
x_205 = lean_ctor_get(x_195, 7);
lean_inc(x_205);
x_206 = lean_ctor_get(x_195, 8);
lean_inc(x_206);
x_207 = lean_ctor_get(x_195, 9);
lean_inc(x_207);
x_208 = lean_ctor_get(x_195, 10);
lean_inc(x_208);
x_209 = lean_ctor_get(x_195, 11);
lean_inc(x_209);
x_210 = lean_ctor_get(x_195, 12);
lean_inc(x_210);
x_211 = lean_ctor_get(x_195, 13);
lean_inc(x_211);
x_212 = lean_ctor_get(x_195, 14);
lean_inc(x_212);
x_213 = lean_ctor_get(x_195, 15);
lean_inc(x_213);
x_214 = lean_ctor_get(x_195, 16);
lean_inc(x_214);
x_215 = lean_ctor_get(x_195, 17);
lean_inc(x_215);
x_216 = lean_ctor_get(x_195, 18);
lean_inc(x_216);
x_217 = lean_ctor_get(x_195, 19);
lean_inc(x_217);
x_218 = lean_ctor_get(x_195, 20);
lean_inc(x_218);
x_219 = lean_ctor_get(x_195, 21);
lean_inc(x_219);
x_220 = lean_ctor_get(x_195, 22);
lean_inc(x_220);
x_221 = lean_ctor_get(x_195, 23);
lean_inc(x_221);
x_222 = lean_ctor_get(x_195, 24);
lean_inc(x_222);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 lean_ctor_release(x_195, 5);
 lean_ctor_release(x_195, 6);
 lean_ctor_release(x_195, 7);
 lean_ctor_release(x_195, 8);
 lean_ctor_release(x_195, 9);
 lean_ctor_release(x_195, 10);
 lean_ctor_release(x_195, 11);
 lean_ctor_release(x_195, 12);
 lean_ctor_release(x_195, 13);
 lean_ctor_release(x_195, 14);
 lean_ctor_release(x_195, 15);
 lean_ctor_release(x_195, 16);
 lean_ctor_release(x_195, 17);
 lean_ctor_release(x_195, 18);
 lean_ctor_release(x_195, 19);
 lean_ctor_release(x_195, 20);
 lean_ctor_release(x_195, 21);
 lean_ctor_release(x_195, 22);
 lean_ctor_release(x_195, 23);
 lean_ctor_release(x_195, 24);
 x_223 = x_195;
} else {
 lean_dec_ref(x_195);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 25, 1);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_3);
lean_ctor_set(x_224, 1, x_198);
lean_ctor_set(x_224, 2, x_199);
lean_ctor_set(x_224, 3, x_200);
lean_ctor_set(x_224, 4, x_201);
lean_ctor_set(x_224, 5, x_202);
lean_ctor_set(x_224, 6, x_203);
lean_ctor_set(x_224, 7, x_205);
lean_ctor_set(x_224, 8, x_206);
lean_ctor_set(x_224, 9, x_207);
lean_ctor_set(x_224, 10, x_208);
lean_ctor_set(x_224, 11, x_209);
lean_ctor_set(x_224, 12, x_210);
lean_ctor_set(x_224, 13, x_211);
lean_ctor_set(x_224, 14, x_212);
lean_ctor_set(x_224, 15, x_213);
lean_ctor_set(x_224, 16, x_214);
lean_ctor_set(x_224, 17, x_215);
lean_ctor_set(x_224, 18, x_216);
lean_ctor_set(x_224, 19, x_217);
lean_ctor_set(x_224, 20, x_218);
lean_ctor_set(x_224, 21, x_219);
lean_ctor_set(x_224, 22, x_220);
lean_ctor_set(x_224, 23, x_221);
lean_ctor_set(x_224, 24, x_222);
lean_ctor_set_uint8(x_224, sizeof(void*)*25, x_204);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_4);
lean_ctor_set(x_225, 1, x_224);
if (lean_is_scalar(x_197)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_197;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_196);
return x_226;
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_39, 2);
x_46 = lean_ctor_get(x_39, 3);
x_47 = lean_ctor_get(x_39, 4);
x_48 = lean_ctor_get(x_39, 5);
x_49 = lean_ctor_get(x_39, 6);
x_50 = lean_ctor_get_uint8(x_39, sizeof(void*)*25);
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
x_69 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_69, 0, x_36);
lean_ctor_set(x_69, 1, x_44);
lean_ctor_set(x_69, 2, x_45);
lean_ctor_set(x_69, 3, x_46);
lean_ctor_set(x_69, 4, x_47);
lean_ctor_set(x_69, 5, x_48);
lean_ctor_set(x_69, 6, x_49);
lean_ctor_set(x_69, 7, x_51);
lean_ctor_set(x_69, 8, x_52);
lean_ctor_set(x_69, 9, x_53);
lean_ctor_set(x_69, 10, x_54);
lean_ctor_set(x_69, 11, x_55);
lean_ctor_set(x_69, 12, x_56);
lean_ctor_set(x_69, 13, x_57);
lean_ctor_set(x_69, 14, x_58);
lean_ctor_set(x_69, 15, x_59);
lean_ctor_set(x_69, 16, x_60);
lean_ctor_set(x_69, 17, x_61);
lean_ctor_set(x_69, 18, x_62);
lean_ctor_set(x_69, 19, x_63);
lean_ctor_set(x_69, 20, x_64);
lean_ctor_set(x_69, 21, x_65);
lean_ctor_set(x_69, 22, x_66);
lean_ctor_set(x_69, 23, x_67);
lean_ctor_set(x_69, 24, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*25, x_50);
lean_ctor_set_tag(x_37, 3);
lean_ctor_set(x_37, 1, x_69);
lean_ctor_set(x_37, 0, x_35);
x_11 = x_37;
x_12 = x_43;
goto block_21;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_70 = lean_ctor_get(x_37, 0);
x_71 = lean_ctor_get(x_37, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_37);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 6);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_70, sizeof(void*)*25);
x_79 = lean_ctor_get(x_70, 7);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 9);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 10);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 11);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 12);
lean_inc(x_84);
x_85 = lean_ctor_get(x_70, 13);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 14);
lean_inc(x_86);
x_87 = lean_ctor_get(x_70, 15);
lean_inc(x_87);
x_88 = lean_ctor_get(x_70, 16);
lean_inc(x_88);
x_89 = lean_ctor_get(x_70, 17);
lean_inc(x_89);
x_90 = lean_ctor_get(x_70, 18);
lean_inc(x_90);
x_91 = lean_ctor_get(x_70, 19);
lean_inc(x_91);
x_92 = lean_ctor_get(x_70, 20);
lean_inc(x_92);
x_93 = lean_ctor_get(x_70, 21);
lean_inc(x_93);
x_94 = lean_ctor_get(x_70, 22);
lean_inc(x_94);
x_95 = lean_ctor_get(x_70, 23);
lean_inc(x_95);
x_96 = lean_ctor_get(x_70, 24);
lean_inc(x_96);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 lean_ctor_release(x_70, 6);
 lean_ctor_release(x_70, 7);
 lean_ctor_release(x_70, 8);
 lean_ctor_release(x_70, 9);
 lean_ctor_release(x_70, 10);
 lean_ctor_release(x_70, 11);
 lean_ctor_release(x_70, 12);
 lean_ctor_release(x_70, 13);
 lean_ctor_release(x_70, 14);
 lean_ctor_release(x_70, 15);
 lean_ctor_release(x_70, 16);
 lean_ctor_release(x_70, 17);
 lean_ctor_release(x_70, 18);
 lean_ctor_release(x_70, 19);
 lean_ctor_release(x_70, 20);
 lean_ctor_release(x_70, 21);
 lean_ctor_release(x_70, 22);
 lean_ctor_release(x_70, 23);
 lean_ctor_release(x_70, 24);
 x_97 = x_70;
} else {
 lean_dec_ref(x_70);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 25, 1);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_36);
lean_ctor_set(x_98, 1, x_72);
lean_ctor_set(x_98, 2, x_73);
lean_ctor_set(x_98, 3, x_74);
lean_ctor_set(x_98, 4, x_75);
lean_ctor_set(x_98, 5, x_76);
lean_ctor_set(x_98, 6, x_77);
lean_ctor_set(x_98, 7, x_79);
lean_ctor_set(x_98, 8, x_80);
lean_ctor_set(x_98, 9, x_81);
lean_ctor_set(x_98, 10, x_82);
lean_ctor_set(x_98, 11, x_83);
lean_ctor_set(x_98, 12, x_84);
lean_ctor_set(x_98, 13, x_85);
lean_ctor_set(x_98, 14, x_86);
lean_ctor_set(x_98, 15, x_87);
lean_ctor_set(x_98, 16, x_88);
lean_ctor_set(x_98, 17, x_89);
lean_ctor_set(x_98, 18, x_90);
lean_ctor_set(x_98, 19, x_91);
lean_ctor_set(x_98, 20, x_92);
lean_ctor_set(x_98, 21, x_93);
lean_ctor_set(x_98, 22, x_94);
lean_ctor_set(x_98, 23, x_95);
lean_ctor_set(x_98, 24, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*25, x_78);
x_99 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_99, 0, x_35);
lean_ctor_set(x_99, 1, x_98);
x_11 = x_99;
x_12 = x_71;
goto block_21;
}
}
else
{
uint8_t x_100; 
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_32);
if (x_100 == 0)
{
return x_32;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_32, 0);
x_102 = lean_ctor_get(x_32, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_32);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_27, 1);
lean_inc(x_104);
lean_dec(x_27);
lean_inc(x_25);
x_105 = l_Lean_MVarId_getTag(x_25, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Expr_bindingBody_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_26);
x_109 = l_Lean_Meta_Grind_simp(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_6, 2);
lean_inc(x_115);
x_116 = l_Lean_Expr_bindingName_x21(x_1);
x_117 = lean_ctor_get(x_110, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
lean_dec(x_110);
x_119 = l_Lean_Expr_bindingInfo_x21(x_1);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
x_121 = 0;
lean_inc(x_117);
lean_inc(x_113);
x_122 = l_Lean_LocalContext_mkLocalDecl(x_115, x_113, x_116, x_117, x_120, x_121);
x_123 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_114);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = 2;
x_127 = lean_unsigned_to_nat(0u);
lean_inc(x_108);
x_128 = l_Lean_Meta_mkFreshExprMVarAt(x_122, x_124, x_108, x_126, x_106, x_127, x_6, x_7, x_8, x_9, x_125);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
x_132 = l_Lean_Expr_mvarId_x21(x_130);
lean_inc(x_113);
x_133 = l_Lean_Expr_fvar___override(x_113);
x_134 = lean_box(0);
lean_ctor_set_tag(x_128, 1);
lean_ctor_set(x_128, 1, x_134);
lean_ctor_set(x_128, 0, x_133);
x_135 = lean_array_mk(x_128);
x_136 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_136, 0, x_135);
lean_closure_set(x_136, 1, x_130);
x_137 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_137, 0, x_136);
lean_inc(x_132);
x_138 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 18, 8);
lean_closure_set(x_138, 0, x_118);
lean_closure_set(x_138, 1, x_25);
lean_closure_set(x_138, 2, x_132);
lean_closure_set(x_138, 3, x_113);
lean_closure_set(x_138, 4, x_134);
lean_closure_set(x_138, 5, x_108);
lean_closure_set(x_138, 6, x_117);
lean_closure_set(x_138, 7, x_26);
x_139 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_139, 0, x_137);
lean_closure_set(x_139, 1, x_138);
lean_inc(x_2);
x_140 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(x_132, x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_131);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_11 = x_141;
x_12 = x_142;
goto block_21;
}
else
{
uint8_t x_143; 
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_140);
if (x_143 == 0)
{
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_140, 0);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_140);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_147 = lean_ctor_get(x_128, 0);
x_148 = lean_ctor_get(x_128, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_128);
x_149 = l_Lean_Expr_mvarId_x21(x_147);
lean_inc(x_113);
x_150 = l_Lean_Expr_fvar___override(x_113);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_array_mk(x_152);
x_154 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_154, 0, x_153);
lean_closure_set(x_154, 1, x_147);
x_155 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_155, 0, x_154);
lean_inc(x_149);
x_156 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 18, 8);
lean_closure_set(x_156, 0, x_118);
lean_closure_set(x_156, 1, x_25);
lean_closure_set(x_156, 2, x_149);
lean_closure_set(x_156, 3, x_113);
lean_closure_set(x_156, 4, x_151);
lean_closure_set(x_156, 5, x_108);
lean_closure_set(x_156, 6, x_117);
lean_closure_set(x_156, 7, x_26);
x_157 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_157, 0, x_155);
lean_closure_set(x_157, 1, x_156);
lean_inc(x_2);
x_158 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(x_149, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_148);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_11 = x_159;
x_12 = x_160;
goto block_21;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_163 = x_158;
} else {
 lean_dec_ref(x_158);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_108);
lean_dec(x_106);
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
x_165 = !lean_is_exclusive(x_109);
if (x_165 == 0)
{
return x_109;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_109, 0);
x_167 = lean_ctor_get(x_109, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_109);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
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
x_169 = !lean_is_exclusive(x_105);
if (x_169 == 0)
{
return x_105;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_105, 0);
x_171 = lean_ctor_get(x_105, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_105);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
uint8_t x_173; 
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
x_173 = !lean_is_exclusive(x_27);
if (x_173 == 0)
{
return x_27;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_27, 0);
x_175 = lean_ctor_get(x_27, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_27);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*25);
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
lean_inc(x_11);
x_37 = l_Lean_MVarId_getType(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = l_Lean_Expr_isArrow(x_39);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_1);
x_42 = l_Lean_Expr_isLet(x_39);
if (x_42 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Expr_isForall(x_39);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Expr_isLetFun(x_39);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_39);
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
x_63 = lean_box(0);
lean_ctor_set(x_37, 0, x_63);
return x_37;
}
else
{
lean_object* x_64; 
lean_free_object(x_37);
x_64 = lean_box(0);
x_43 = x_64;
goto block_60;
}
}
else
{
lean_object* x_65; 
lean_free_object(x_37);
x_65 = lean_box(0);
x_43 = x_65;
goto block_60;
}
}
else
{
lean_object* x_66; 
lean_free_object(x_37);
x_66 = lean_box(0);
x_43 = x_66;
goto block_60;
}
block_60:
{
uint8_t x_44; lean_object* x_45; 
lean_dec(x_43);
x_44 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Meta_intro1Core(x_11, x_44, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_48);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_50, 0, x_48);
x_51 = lean_box(x_18);
x_52 = lean_box(x_42);
lean_inc(x_49);
x_53 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 39, 30);
lean_closure_set(x_53, 0, x_49);
lean_closure_set(x_53, 1, x_12);
lean_closure_set(x_53, 2, x_13);
lean_closure_set(x_53, 3, x_14);
lean_closure_set(x_53, 4, x_15);
lean_closure_set(x_53, 5, x_16);
lean_closure_set(x_53, 6, x_17);
lean_closure_set(x_53, 7, x_51);
lean_closure_set(x_53, 8, x_19);
lean_closure_set(x_53, 9, x_20);
lean_closure_set(x_53, 10, x_21);
lean_closure_set(x_53, 11, x_22);
lean_closure_set(x_53, 12, x_23);
lean_closure_set(x_53, 13, x_24);
lean_closure_set(x_53, 14, x_25);
lean_closure_set(x_53, 15, x_26);
lean_closure_set(x_53, 16, x_27);
lean_closure_set(x_53, 17, x_28);
lean_closure_set(x_53, 18, x_29);
lean_closure_set(x_53, 19, x_30);
lean_closure_set(x_53, 20, x_31);
lean_closure_set(x_53, 21, x_32);
lean_closure_set(x_53, 22, x_33);
lean_closure_set(x_53, 23, x_34);
lean_closure_set(x_53, 24, x_35);
lean_closure_set(x_53, 25, x_36);
lean_closure_set(x_53, 26, x_52);
lean_closure_set(x_53, 27, x_39);
lean_closure_set(x_53, 28, x_48);
lean_closure_set(x_53, 29, x_2);
x_54 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_54, 0, x_50);
lean_closure_set(x_54, 1, x_53);
x_55 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_49, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_39);
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
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_37);
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
x_67 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_67, 0, x_1);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 10, 1);
lean_closure_set(x_68, 0, x_39);
x_69 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
x_70 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
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
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
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
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_37, 0);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_37);
x_84 = l_Lean_Expr_isArrow(x_82);
if (x_84 == 0)
{
uint8_t x_85; lean_object* x_86; 
lean_dec(x_1);
x_85 = l_Lean_Expr_isLet(x_82);
if (x_85 == 0)
{
uint8_t x_104; 
x_104 = l_Lean_Expr_isForall(x_82);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Expr_isLetFun(x_82);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_82);
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
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_83);
return x_107;
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_86 = x_108;
goto block_103;
}
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_86 = x_109;
goto block_103;
}
}
else
{
lean_object* x_110; 
x_110 = lean_box(0);
x_86 = x_110;
goto block_103;
}
block_103:
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_86);
x_87 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_88 = l_Lean_Meta_intro1Core(x_11, x_87, x_6, x_7, x_8, x_9, x_83);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
lean_inc(x_91);
x_93 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_93, 0, x_91);
x_94 = lean_box(x_18);
x_95 = lean_box(x_85);
lean_inc(x_92);
x_96 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 39, 30);
lean_closure_set(x_96, 0, x_92);
lean_closure_set(x_96, 1, x_12);
lean_closure_set(x_96, 2, x_13);
lean_closure_set(x_96, 3, x_14);
lean_closure_set(x_96, 4, x_15);
lean_closure_set(x_96, 5, x_16);
lean_closure_set(x_96, 6, x_17);
lean_closure_set(x_96, 7, x_94);
lean_closure_set(x_96, 8, x_19);
lean_closure_set(x_96, 9, x_20);
lean_closure_set(x_96, 10, x_21);
lean_closure_set(x_96, 11, x_22);
lean_closure_set(x_96, 12, x_23);
lean_closure_set(x_96, 13, x_24);
lean_closure_set(x_96, 14, x_25);
lean_closure_set(x_96, 15, x_26);
lean_closure_set(x_96, 16, x_27);
lean_closure_set(x_96, 17, x_28);
lean_closure_set(x_96, 18, x_29);
lean_closure_set(x_96, 19, x_30);
lean_closure_set(x_96, 20, x_31);
lean_closure_set(x_96, 21, x_32);
lean_closure_set(x_96, 22, x_33);
lean_closure_set(x_96, 23, x_34);
lean_closure_set(x_96, 24, x_35);
lean_closure_set(x_96, 25, x_36);
lean_closure_set(x_96, 26, x_95);
lean_closure_set(x_96, 27, x_82);
lean_closure_set(x_96, 28, x_91);
lean_closure_set(x_96, 29, x_2);
x_97 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_97, 0, x_93);
lean_closure_set(x_97, 1, x_96);
x_98 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_92, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
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
x_99 = lean_ctor_get(x_88, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_101 = x_88;
} else {
 lean_dec_ref(x_88);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
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
x_111 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_111, 0, x_1);
x_112 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 10, 1);
lean_closure_set(x_112, 0, x_82);
x_113 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_113, 0, x_111);
lean_closure_set(x_113, 1, x_112);
x_114 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_83);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
lean_dec(x_115);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_114, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_122 = x_114;
} else {
 lean_dec_ref(x_114);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
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
x_124 = !lean_is_exclusive(x_37);
if (x_124 == 0)
{
return x_37;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_37, 0);
x_126 = lean_ctor_get(x_37, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_37);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
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
_start:
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_unbox(x_8);
lean_dec(x_8);
x_41 = lean_unbox(x_27);
lean_dec(x_27);
x_42 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_40, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_41, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_31);
lean_dec(x_28);
return x_42;
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isEagerCasesCandidate(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*25);
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
x_33 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set(x_33, 2, x_9);
lean_ctor_set(x_33, 3, x_10);
lean_ctor_set(x_33, 4, x_11);
lean_ctor_set(x_33, 5, x_12);
lean_ctor_set(x_33, 6, x_13);
lean_ctor_set(x_33, 7, x_15);
lean_ctor_set(x_33, 8, x_16);
lean_ctor_set(x_33, 9, x_17);
lean_ctor_set(x_33, 10, x_18);
lean_ctor_set(x_33, 11, x_19);
lean_ctor_set(x_33, 12, x_20);
lean_ctor_set(x_33, 13, x_21);
lean_ctor_set(x_33, 14, x_22);
lean_ctor_set(x_33, 15, x_23);
lean_ctor_set(x_33, 16, x_24);
lean_ctor_set(x_33, 17, x_25);
lean_ctor_set(x_33, 18, x_26);
lean_ctor_set(x_33, 19, x_27);
lean_ctor_set(x_33, 20, x_28);
lean_ctor_set(x_33, 21, x_29);
lean_ctor_set(x_33, 22, x_30);
lean_ctor_set(x_33, 23, x_31);
lean_ctor_set(x_33, 24, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*25, x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_33);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 2);
x_39 = lean_ctor_get(x_1, 3);
x_40 = lean_ctor_get(x_1, 4);
x_41 = lean_ctor_get(x_1, 5);
x_42 = lean_ctor_get(x_1, 6);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*25);
x_44 = lean_ctor_get(x_1, 7);
x_45 = lean_ctor_get(x_1, 8);
x_46 = lean_ctor_get(x_1, 9);
x_47 = lean_ctor_get(x_1, 10);
x_48 = lean_ctor_get(x_1, 11);
x_49 = lean_ctor_get(x_1, 12);
x_50 = lean_ctor_get(x_1, 13);
x_51 = lean_ctor_get(x_1, 14);
x_52 = lean_ctor_get(x_1, 15);
x_53 = lean_ctor_get(x_1, 16);
x_54 = lean_ctor_get(x_1, 17);
x_55 = lean_ctor_get(x_1, 18);
x_56 = lean_ctor_get(x_1, 19);
x_57 = lean_ctor_get(x_1, 20);
x_58 = lean_ctor_get(x_1, 21);
x_59 = lean_ctor_get(x_1, 22);
x_60 = lean_ctor_get(x_1, 23);
x_61 = lean_ctor_get(x_1, 24);
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
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_62 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_62, 0, x_35);
lean_ctor_set(x_62, 1, x_37);
lean_ctor_set(x_62, 2, x_38);
lean_ctor_set(x_62, 3, x_39);
lean_ctor_set(x_62, 4, x_40);
lean_ctor_set(x_62, 5, x_41);
lean_ctor_set(x_62, 6, x_42);
lean_ctor_set(x_62, 7, x_44);
lean_ctor_set(x_62, 8, x_45);
lean_ctor_set(x_62, 9, x_46);
lean_ctor_set(x_62, 10, x_47);
lean_ctor_set(x_62, 11, x_48);
lean_ctor_set(x_62, 12, x_49);
lean_ctor_set(x_62, 13, x_50);
lean_ctor_set(x_62, 14, x_51);
lean_ctor_set(x_62, 15, x_52);
lean_ctor_set(x_62, 16, x_53);
lean_ctor_set(x_62, 17, x_54);
lean_ctor_set(x_62, 18, x_55);
lean_ctor_set(x_62, 19, x_56);
lean_ctor_set(x_62, 20, x_57);
lean_ctor_set(x_62, 21, x_58);
lean_ctor_set(x_62, 22, x_59);
lean_ctor_set(x_62, 23, x_60);
lean_ctor_set(x_62, 24, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*25, x_43);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_3);
x_2 = x_36;
x_3 = x_63;
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_13 = l_Lean_Meta_Grind_isEagerCasesCandidate(x_2, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_15 = l_Lean_Expr_fvar___override(x_1);
x_16 = l_Lean_Meta_Grind_cases(x_3, x_15, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_2, x_18, x_19);
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_2, x_22, x_24);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
lean_inc(x_2);
x_34 = l_Lean_Meta_Grind_isEagerCasesCandidate(x_2, x_32);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_fvar___override(x_1);
x_38 = l_Lean_Meta_Grind_cases(x_3, x_37, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
x_43 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_2, x_39, x_42);
lean_dec(x_2);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
return x_9;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_9, 0);
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_9);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
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
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
x_34 = l_Lean_Meta_Grind_injection_x3f(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_free_object(x_1);
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
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_34, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set(x_35, 0, x_1);
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
lean_dec(x_35);
lean_ctor_set(x_1, 0, x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_34, 0, x_47);
return x_34;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_ctor_get(x_35, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_50 = x_35;
} else {
 lean_dec_ref(x_35);
 x_50 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_49);
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_1);
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
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_57 = lean_ctor_get(x_1, 0);
x_58 = lean_ctor_get(x_1, 1);
x_59 = lean_ctor_get(x_1, 2);
x_60 = lean_ctor_get(x_1, 3);
x_61 = lean_ctor_get(x_1, 4);
x_62 = lean_ctor_get(x_1, 5);
x_63 = lean_ctor_get(x_1, 6);
x_64 = lean_ctor_get_uint8(x_1, sizeof(void*)*25);
x_65 = lean_ctor_get(x_1, 7);
x_66 = lean_ctor_get(x_1, 8);
x_67 = lean_ctor_get(x_1, 9);
x_68 = lean_ctor_get(x_1, 10);
x_69 = lean_ctor_get(x_1, 11);
x_70 = lean_ctor_get(x_1, 12);
x_71 = lean_ctor_get(x_1, 13);
x_72 = lean_ctor_get(x_1, 14);
x_73 = lean_ctor_get(x_1, 15);
x_74 = lean_ctor_get(x_1, 16);
x_75 = lean_ctor_get(x_1, 17);
x_76 = lean_ctor_get(x_1, 18);
x_77 = lean_ctor_get(x_1, 19);
x_78 = lean_ctor_get(x_1, 20);
x_79 = lean_ctor_get(x_1, 21);
x_80 = lean_ctor_get(x_1, 22);
x_81 = lean_ctor_get(x_1, 23);
x_82 = lean_ctor_get(x_1, 24);
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
lean_inc(x_65);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_1);
x_83 = l_Lean_Meta_Grind_injection_x3f(x_57, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_58);
lean_ctor_set(x_93, 2, x_59);
lean_ctor_set(x_93, 3, x_60);
lean_ctor_set(x_93, 4, x_61);
lean_ctor_set(x_93, 5, x_62);
lean_ctor_set(x_93, 6, x_63);
lean_ctor_set(x_93, 7, x_65);
lean_ctor_set(x_93, 8, x_66);
lean_ctor_set(x_93, 9, x_67);
lean_ctor_set(x_93, 10, x_68);
lean_ctor_set(x_93, 11, x_69);
lean_ctor_set(x_93, 12, x_70);
lean_ctor_set(x_93, 13, x_71);
lean_ctor_set(x_93, 14, x_72);
lean_ctor_set(x_93, 15, x_73);
lean_ctor_set(x_93, 16, x_74);
lean_ctor_set(x_93, 17, x_75);
lean_ctor_set(x_93, 18, x_76);
lean_ctor_set(x_93, 19, x_77);
lean_ctor_set(x_93, 20, x_78);
lean_ctor_set(x_93, 21, x_79);
lean_ctor_set(x_93, 22, x_80);
lean_ctor_set(x_93, 23, x_81);
lean_ctor_set(x_93, 24, x_82);
lean_ctor_set_uint8(x_93, sizeof(void*)*25, x_64);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_89);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
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
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
x_96 = lean_ctor_get(x_83, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_83, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_98 = x_83;
} else {
 lean_dec_ref(x_83);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36, lean_object* x_37, lean_object* x_38) {
_start:
{
lean_object* x_39; 
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_1, x_2, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
switch (lean_obj_tag(x_40)) {
case 0:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_42 = l_Lean_MVarId_byContra_x3f(x_3, x_34, x_35, x_36, x_37, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
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
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_take(x_30, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_push(x_46, x_1);
x_49 = lean_st_ref_set(x_30, x_48, x_47);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_dec(x_42);
x_57 = lean_ctor_get(x_43, 0);
lean_inc(x_57);
lean_dec(x_43);
x_58 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
lean_ctor_set(x_58, 2, x_5);
lean_ctor_set(x_58, 3, x_6);
lean_ctor_set(x_58, 4, x_7);
lean_ctor_set(x_58, 5, x_8);
lean_ctor_set(x_58, 6, x_9);
lean_ctor_set(x_58, 7, x_11);
lean_ctor_set(x_58, 8, x_12);
lean_ctor_set(x_58, 9, x_13);
lean_ctor_set(x_58, 10, x_14);
lean_ctor_set(x_58, 11, x_15);
lean_ctor_set(x_58, 12, x_16);
lean_ctor_set(x_58, 13, x_17);
lean_ctor_set(x_58, 14, x_18);
lean_ctor_set(x_58, 15, x_19);
lean_ctor_set(x_58, 16, x_20);
lean_ctor_set(x_58, 17, x_21);
lean_ctor_set(x_58, 18, x_22);
lean_ctor_set(x_58, 19, x_23);
lean_ctor_set(x_58, 20, x_24);
lean_ctor_set(x_58, 21, x_25);
lean_ctor_set(x_58, 22, x_26);
lean_ctor_set(x_58, 23, x_27);
lean_ctor_set(x_58, 24, x_28);
lean_ctor_set_uint8(x_58, sizeof(void*)*25, x_10);
x_59 = l_Lean_Meta_Grind_intros_go(x_2, x_58, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_56);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
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
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 1:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
x_64 = lean_ctor_get(x_39, 1);
lean_inc(x_64);
lean_dec(x_39);
x_65 = lean_ctor_get(x_40, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_40, 1);
lean_inc(x_66);
lean_dec(x_40);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_65);
lean_inc(x_66);
x_67 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_66, x_65, x_34, x_35, x_36, x_37, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_65);
lean_inc(x_66);
x_70 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(x_66, x_65, x_34, x_35, x_36, x_37, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
x_74 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_74, 0, x_66);
lean_inc(x_2);
x_75 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_intros_go___lambda__1), 11, 2);
lean_closure_set(x_75, 0, x_65);
lean_closure_set(x_75, 1, x_2);
x_76 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_76, 0, x_74);
lean_closure_set(x_76, 1, x_75);
x_77 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_78 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_78, 0, x_76);
lean_closure_set(x_78, 1, x_77);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_79 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_73, x_78, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_72);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Meta_Grind_intros_go(x_2, x_80, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_81);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 0);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_79);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_dec(x_65);
x_87 = lean_ctor_get(x_70, 1);
lean_inc(x_87);
lean_dec(x_70);
x_88 = lean_ctor_get(x_71, 0);
lean_inc(x_88);
lean_dec(x_71);
x_89 = l_Lean_Meta_Grind_intros_go(x_2, x_88, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_87);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_70);
if (x_90 == 0)
{
return x_70;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_70, 0);
x_92 = lean_ctor_get(x_70, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_70);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_66);
lean_dec(x_65);
x_94 = lean_ctor_get(x_67, 1);
lean_inc(x_94);
lean_dec(x_67);
x_95 = lean_ctor_get(x_68, 0);
lean_inc(x_95);
lean_dec(x_68);
x_96 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(x_2, x_95, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_67);
if (x_97 == 0)
{
return x_67;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_67, 0);
x_99 = lean_ctor_get(x_67, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_67);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
case 2:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
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
x_101 = lean_ctor_get(x_39, 1);
lean_inc(x_101);
lean_dec(x_39);
x_102 = lean_ctor_get(x_40, 0);
lean_inc(x_102);
lean_dec(x_40);
x_103 = l_Lean_Meta_Grind_intros_go(x_2, x_102, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_101);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
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
x_104 = lean_ctor_get(x_39, 1);
lean_inc(x_104);
lean_dec(x_39);
x_105 = lean_ctor_get(x_40, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 1);
lean_inc(x_106);
lean_dec(x_40);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_106);
x_107 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_106, x_105, x_34, x_35, x_36, x_37, x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_Grind_intros_go(x_2, x_106, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_106);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
lean_dec(x_108);
x_113 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(x_2, x_112, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_106);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_107);
if (x_114 == 0)
{
return x_107;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_107);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
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
x_118 = !lean_is_exclusive(x_39);
if (x_118 == 0)
{
return x_39;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_39, 0);
x_120 = lean_ctor_get(x_39, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_39);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*25);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_38 = lean_box(0);
x_39 = l_Lean_Meta_Grind_intros_go___lambda__2(x_2, x_1, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_12, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_11);
return x_41;
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
_start:
{
uint8_t x_39; lean_object* x_40; 
x_39 = lean_unbox(x_10);
lean_dec(x_10);
x_40 = l_Lean_Meta_Grind_intros_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
lean_dec(x_30);
lean_dec(x_29);
return x_40;
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
uint8_t x_13; 
lean_inc(x_4);
x_13 = l_Lean_Meta_Grind_isEagerCasesCandidate(x_4, x_2);
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
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*25);
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_71 = l_Lean_MVarId_assert(x_46, x_43, x_2, x_1, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_ctor_set(x_4, 0, x_72);
x_74 = l_Lean_Meta_Grind_intros(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_73);
return x_74;
}
else
{
uint8_t x_75; 
lean_free_object(x_4);
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
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_71);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_79 = lean_ctor_get(x_4, 0);
x_80 = lean_ctor_get(x_4, 1);
x_81 = lean_ctor_get(x_4, 2);
x_82 = lean_ctor_get(x_4, 3);
x_83 = lean_ctor_get(x_4, 4);
x_84 = lean_ctor_get(x_4, 5);
x_85 = lean_ctor_get(x_4, 6);
x_86 = lean_ctor_get_uint8(x_4, sizeof(void*)*25);
x_87 = lean_ctor_get(x_4, 7);
x_88 = lean_ctor_get(x_4, 8);
x_89 = lean_ctor_get(x_4, 9);
x_90 = lean_ctor_get(x_4, 10);
x_91 = lean_ctor_get(x_4, 11);
x_92 = lean_ctor_get(x_4, 12);
x_93 = lean_ctor_get(x_4, 13);
x_94 = lean_ctor_get(x_4, 14);
x_95 = lean_ctor_get(x_4, 15);
x_96 = lean_ctor_get(x_4, 16);
x_97 = lean_ctor_get(x_4, 17);
x_98 = lean_ctor_get(x_4, 18);
x_99 = lean_ctor_get(x_4, 19);
x_100 = lean_ctor_get(x_4, 20);
x_101 = lean_ctor_get(x_4, 21);
x_102 = lean_ctor_get(x_4, 22);
x_103 = lean_ctor_get(x_4, 23);
x_104 = lean_ctor_get(x_4, 24);
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
lean_inc(x_87);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_105 = l_Lean_MVarId_assert(x_79, x_43, x_2, x_1, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_80);
lean_ctor_set(x_108, 2, x_81);
lean_ctor_set(x_108, 3, x_82);
lean_ctor_set(x_108, 4, x_83);
lean_ctor_set(x_108, 5, x_84);
lean_ctor_set(x_108, 6, x_85);
lean_ctor_set(x_108, 7, x_87);
lean_ctor_set(x_108, 8, x_88);
lean_ctor_set(x_108, 9, x_89);
lean_ctor_set(x_108, 10, x_90);
lean_ctor_set(x_108, 11, x_91);
lean_ctor_set(x_108, 12, x_92);
lean_ctor_set(x_108, 13, x_93);
lean_ctor_set(x_108, 14, x_94);
lean_ctor_set(x_108, 15, x_95);
lean_ctor_set(x_108, 16, x_96);
lean_ctor_set(x_108, 17, x_97);
lean_ctor_set(x_108, 18, x_98);
lean_ctor_set(x_108, 19, x_99);
lean_ctor_set(x_108, 20, x_100);
lean_ctor_set(x_108, 21, x_101);
lean_ctor_set(x_108, 22, x_102);
lean_ctor_set(x_108, 23, x_103);
lean_ctor_set(x_108, 24, x_104);
lean_ctor_set_uint8(x_108, sizeof(void*)*25, x_86);
x_109 = l_Lean_Meta_Grind_intros(x_3, x_108, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
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
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
x_36 = l_Std_Queue_dequeue_x3f___rarg(x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_free_object(x_1);
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
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
lean_dec(x_41);
lean_ctor_set(x_1, 17, x_42);
x_46 = l_Lean_Meta_Grind_assertAt(x_43, x_44, x_45, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_36, 0, x_48);
lean_ctor_set(x_46, 0, x_36);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_36, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_free_object(x_36);
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_36, 0);
lean_inc(x_56);
lean_dec(x_36);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
lean_dec(x_57);
lean_ctor_set(x_1, 17, x_58);
x_62 = l_Lean_Meta_Grind_assertAt(x_59, x_60, x_61, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 1);
x_74 = lean_ctor_get(x_1, 2);
x_75 = lean_ctor_get(x_1, 3);
x_76 = lean_ctor_get(x_1, 4);
x_77 = lean_ctor_get(x_1, 5);
x_78 = lean_ctor_get(x_1, 6);
x_79 = lean_ctor_get_uint8(x_1, sizeof(void*)*25);
x_80 = lean_ctor_get(x_1, 7);
x_81 = lean_ctor_get(x_1, 8);
x_82 = lean_ctor_get(x_1, 9);
x_83 = lean_ctor_get(x_1, 10);
x_84 = lean_ctor_get(x_1, 11);
x_85 = lean_ctor_get(x_1, 12);
x_86 = lean_ctor_get(x_1, 13);
x_87 = lean_ctor_get(x_1, 14);
x_88 = lean_ctor_get(x_1, 15);
x_89 = lean_ctor_get(x_1, 16);
x_90 = lean_ctor_get(x_1, 17);
x_91 = lean_ctor_get(x_1, 18);
x_92 = lean_ctor_get(x_1, 19);
x_93 = lean_ctor_get(x_1, 20);
x_94 = lean_ctor_get(x_1, 21);
x_95 = lean_ctor_get(x_1, 22);
x_96 = lean_ctor_get(x_1, 23);
x_97 = lean_ctor_get(x_1, 24);
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
lean_inc(x_80);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_1);
x_98 = l_Std_Queue_dequeue_x3f___rarg(x_90);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
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
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_9);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 2);
lean_inc(x_107);
lean_dec(x_103);
x_108 = lean_alloc_ctor(0, 25, 1);
lean_ctor_set(x_108, 0, x_72);
lean_ctor_set(x_108, 1, x_73);
lean_ctor_set(x_108, 2, x_74);
lean_ctor_set(x_108, 3, x_75);
lean_ctor_set(x_108, 4, x_76);
lean_ctor_set(x_108, 5, x_77);
lean_ctor_set(x_108, 6, x_78);
lean_ctor_set(x_108, 7, x_80);
lean_ctor_set(x_108, 8, x_81);
lean_ctor_set(x_108, 9, x_82);
lean_ctor_set(x_108, 10, x_83);
lean_ctor_set(x_108, 11, x_84);
lean_ctor_set(x_108, 12, x_85);
lean_ctor_set(x_108, 13, x_86);
lean_ctor_set(x_108, 14, x_87);
lean_ctor_set(x_108, 15, x_88);
lean_ctor_set(x_108, 16, x_89);
lean_ctor_set(x_108, 17, x_104);
lean_ctor_set(x_108, 18, x_91);
lean_ctor_set(x_108, 19, x_92);
lean_ctor_set(x_108, 20, x_93);
lean_ctor_set(x_108, 21, x_94);
lean_ctor_set(x_108, 22, x_95);
lean_ctor_set(x_108, 23, x_96);
lean_ctor_set(x_108, 24, x_97);
lean_ctor_set_uint8(x_108, sizeof(void*)*25, x_79);
x_109 = l_Lean_Meta_Grind_assertAt(x_105, x_106, x_107, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_102;
}
lean_ctor_set(x_113, 0, x_110);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_102);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
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
