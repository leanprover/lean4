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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAll___closed__1;
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_intros___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___closed__1;
lean_object* l_Lean_Meta_Grind_isGrindCasesTarget(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed(lean_object**);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_Grind_GrindTactic_iterate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___closed__2;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCasesCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed(lean_object**);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed(lean_object**);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg___boxed), 2, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___rarg(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_st_ref_take(x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_13, 7);
x_19 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_18, x_1, x_2);
lean_ctor_set(x_13, 7, x_19);
x_20 = lean_st_ref_set(x_7, x_12, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
x_29 = lean_ctor_get(x_13, 2);
x_30 = lean_ctor_get(x_13, 3);
x_31 = lean_ctor_get(x_13, 4);
x_32 = lean_ctor_get(x_13, 5);
x_33 = lean_ctor_get(x_13, 6);
x_34 = lean_ctor_get(x_13, 7);
x_35 = lean_ctor_get(x_13, 8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_36 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_34, x_1, x_2);
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set(x_37, 3, x_30);
lean_ctor_set(x_37, 4, x_31);
lean_ctor_set(x_37, 5, x_32);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_36);
lean_ctor_set(x_37, 8, x_35);
lean_ctor_set(x_12, 0, x_37);
x_38 = lean_st_ref_set(x_7, x_12, x_14);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_12, 1);
x_44 = lean_ctor_get(x_12, 2);
x_45 = lean_ctor_get(x_12, 3);
x_46 = lean_ctor_get(x_12, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_13, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_13, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_13, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_13, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_13, 6);
lean_inc(x_53);
x_54 = lean_ctor_get(x_13, 7);
lean_inc(x_54);
x_55 = lean_ctor_get(x_13, 8);
lean_inc(x_55);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_56 = x_13;
} else {
 lean_dec_ref(x_13);
 x_56 = lean_box(0);
}
x_57 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_54, x_1, x_2);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 9, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_49);
lean_ctor_set(x_58, 3, x_50);
lean_ctor_set(x_58, 4, x_51);
lean_ctor_set(x_58, 5, x_52);
lean_ctor_set(x_58, 6, x_53);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_55);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_59, 2, x_44);
lean_ctor_set(x_59, 3, x_45);
lean_ctor_set(x_59, 4, x_46);
x_60 = lean_st_ref_set(x_7, x_59, x_14);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_5);
x_14 = l_Lean_Meta_Grind_addNewEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_st_ref_get(x_5, x_18);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_16, 1, x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_st_ref_get(x_5, x_26);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, uint8_t x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34) {
_start:
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_LocalDecl_type(x_26);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_35);
x_36 = l_Lean_Meta_isProp(x_35, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
lean_inc(x_1);
x_42 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_3);
lean_ctor_set(x_42, 3, x_4);
lean_ctor_set(x_42, 4, x_5);
lean_ctor_set(x_42, 5, x_6);
lean_ctor_set(x_42, 6, x_8);
lean_ctor_set(x_42, 7, x_9);
lean_ctor_set(x_42, 8, x_10);
lean_ctor_set(x_42, 9, x_11);
lean_ctor_set(x_42, 10, x_12);
lean_ctor_set(x_42, 11, x_13);
lean_ctor_set(x_42, 12, x_14);
lean_ctor_set(x_42, 13, x_15);
lean_ctor_set(x_42, 14, x_16);
lean_ctor_set(x_42, 15, x_17);
lean_ctor_set(x_42, 16, x_18);
lean_ctor_set(x_42, 17, x_19);
lean_ctor_set(x_42, 18, x_20);
lean_ctor_set(x_42, 19, x_21);
lean_ctor_set_uint8(x_42, sizeof(void*)*20, x_7);
if (x_24 == 0)
{
uint8_t x_113; 
x_113 = l_Lean_Expr_isLetFun(x_25);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_1);
x_114 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_114, 0, x_22);
lean_ctor_set(x_114, 1, x_42);
lean_ctor_set(x_36, 0, x_114);
return x_36;
}
else
{
lean_object* x_115; 
lean_free_object(x_36);
x_115 = lean_box(0);
x_43 = x_115;
goto block_112;
}
}
else
{
lean_object* x_116; 
lean_free_object(x_36);
x_116 = lean_box(0);
x_43 = x_116;
goto block_112;
}
block_112:
{
lean_object* x_44; 
lean_dec(x_43);
lean_inc(x_30);
lean_inc(x_22);
x_44 = l_Lean_FVarId_getDecl(x_22, x_30, x_31, x_32, x_33, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_LocalDecl_value(x_45);
lean_dec(x_45);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
x_48 = l_Lean_Meta_Grind_simp(x_47, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_22);
x_51 = l_Lean_Expr_fvar___override(x_22);
x_52 = l_Lean_Meta_Grind_shareCommon(x_51, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_50);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_49);
x_56 = l_Lean_Meta_Simp_Result_getProof(x_49, x_30, x_31, x_32, x_33, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_60, 0, x_42);
x_61 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 13, 4);
lean_closure_set(x_61, 0, x_54);
lean_closure_set(x_61, 1, x_59);
lean_closure_set(x_61, 2, x_57);
lean_closure_set(x_61, 3, x_23);
x_62 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_62, 0, x_60);
lean_closure_set(x_62, 1, x_61);
x_63 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_64 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_64, 0, x_62);
lean_closure_set(x_64, 1, x_63);
x_65 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_64, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_58);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 1, x_67);
lean_ctor_set(x_52, 0, x_22);
lean_ctor_set(x_65, 0, x_52);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 1, x_68);
lean_ctor_set(x_52, 0, x_22);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_52);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_free_object(x_52);
lean_dec(x_22);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_free_object(x_52);
lean_dec(x_54);
lean_dec(x_49);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_56);
if (x_75 == 0)
{
return x_56;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_56, 0);
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_56);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_52, 0);
x_80 = lean_ctor_get(x_52, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_52);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_49);
x_81 = l_Lean_Meta_Simp_Result_getProof(x_49, x_30, x_31, x_32, x_33, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_49, 0);
lean_inc(x_84);
lean_dec(x_49);
x_85 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_85, 0, x_42);
x_86 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 13, 4);
lean_closure_set(x_86, 0, x_79);
lean_closure_set(x_86, 1, x_84);
lean_closure_set(x_86, 2, x_82);
lean_closure_set(x_86, 3, x_23);
x_87 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_87, 0, x_85);
lean_closure_set(x_87, 1, x_86);
x_88 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_89 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_89, 0, x_87);
lean_closure_set(x_89, 1, x_88);
x_90 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_89, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_94, 0, x_22);
lean_ctor_set(x_94, 1, x_91);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_22);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
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
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_79);
lean_dec(x_49);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_100 = lean_ctor_get(x_81, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_81, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_102 = x_81;
} else {
 lean_dec_ref(x_81);
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
uint8_t x_104; 
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_48);
if (x_104 == 0)
{
return x_48;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_48, 0);
x_106 = lean_ctor_get(x_48, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_48);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_44);
if (x_108 == 0)
{
return x_44;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_44, 0);
x_110 = lean_ctor_get(x_44, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_44);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_36, 1);
lean_inc(x_117);
lean_dec(x_36);
lean_inc(x_1);
x_118 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_2);
lean_ctor_set(x_118, 2, x_3);
lean_ctor_set(x_118, 3, x_4);
lean_ctor_set(x_118, 4, x_5);
lean_ctor_set(x_118, 5, x_6);
lean_ctor_set(x_118, 6, x_8);
lean_ctor_set(x_118, 7, x_9);
lean_ctor_set(x_118, 8, x_10);
lean_ctor_set(x_118, 9, x_11);
lean_ctor_set(x_118, 10, x_12);
lean_ctor_set(x_118, 11, x_13);
lean_ctor_set(x_118, 12, x_14);
lean_ctor_set(x_118, 13, x_15);
lean_ctor_set(x_118, 14, x_16);
lean_ctor_set(x_118, 15, x_17);
lean_ctor_set(x_118, 16, x_18);
lean_ctor_set(x_118, 17, x_19);
lean_ctor_set(x_118, 18, x_20);
lean_ctor_set(x_118, 19, x_21);
lean_ctor_set_uint8(x_118, sizeof(void*)*20, x_7);
if (x_24 == 0)
{
uint8_t x_164; 
x_164 = l_Lean_Expr_isLetFun(x_25);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_1);
x_165 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_165, 0, x_22);
lean_ctor_set(x_165, 1, x_118);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_117);
return x_166;
}
else
{
lean_object* x_167; 
x_167 = lean_box(0);
x_119 = x_167;
goto block_163;
}
}
else
{
lean_object* x_168; 
x_168 = lean_box(0);
x_119 = x_168;
goto block_163;
}
block_163:
{
lean_object* x_120; 
lean_dec(x_119);
lean_inc(x_30);
lean_inc(x_22);
x_120 = l_Lean_FVarId_getDecl(x_22, x_30, x_31, x_32, x_33, x_117);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_LocalDecl_value(x_121);
lean_dec(x_121);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
x_124 = l_Lean_Meta_Grind_simp(x_123, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_22);
x_127 = l_Lean_Expr_fvar___override(x_22);
x_128 = l_Lean_Meta_Grind_shareCommon(x_127, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_126);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_125);
x_132 = l_Lean_Meta_Simp_Result_getProof(x_125, x_30, x_31, x_32, x_33, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_125, 0);
lean_inc(x_135);
lean_dec(x_125);
x_136 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_136, 0, x_118);
x_137 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3), 13, 4);
lean_closure_set(x_137, 0, x_129);
lean_closure_set(x_137, 1, x_135);
lean_closure_set(x_137, 2, x_133);
lean_closure_set(x_137, 3, x_23);
x_138 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_138, 0, x_136);
lean_closure_set(x_138, 1, x_137);
x_139 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_140 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_140, 0, x_138);
lean_closure_set(x_140, 1, x_139);
x_141 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_140, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_134);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_145 = lean_alloc_ctor(3, 2, 0);
} else {
 x_145 = x_131;
 lean_ctor_set_tag(x_145, 3);
}
lean_ctor_set(x_145, 0, x_22);
lean_ctor_set(x_145, 1, x_142);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_131);
lean_dec(x_22);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_125);
lean_dec(x_118);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_151 = lean_ctor_get(x_132, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_132, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_153 = x_132;
} else {
 lean_dec_ref(x_132);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_118);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_155 = lean_ctor_get(x_124, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_124, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_157 = x_124;
} else {
 lean_dec_ref(x_124);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_118);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_159 = lean_ctor_get(x_120, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_120, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_161 = x_120;
} else {
 lean_dec_ref(x_120);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
x_169 = lean_ctor_get(x_36, 1);
lean_inc(x_169);
lean_dec(x_36);
x_170 = l_Lean_LocalDecl_userName(x_26);
x_171 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_170, x_32, x_33, x_169);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Expr_fvar___override(x_22);
x_175 = l_Lean_MVarId_assert(x_1, x_172, x_35, x_174, x_30, x_31, x_32, x_33, x_173);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_2);
lean_ctor_set(x_178, 2, x_3);
lean_ctor_set(x_178, 3, x_4);
lean_ctor_set(x_178, 4, x_5);
lean_ctor_set(x_178, 5, x_6);
lean_ctor_set(x_178, 6, x_8);
lean_ctor_set(x_178, 7, x_9);
lean_ctor_set(x_178, 8, x_10);
lean_ctor_set(x_178, 9, x_11);
lean_ctor_set(x_178, 10, x_12);
lean_ctor_set(x_178, 11, x_13);
lean_ctor_set(x_178, 12, x_14);
lean_ctor_set(x_178, 13, x_15);
lean_ctor_set(x_178, 14, x_16);
lean_ctor_set(x_178, 15, x_17);
lean_ctor_set(x_178, 16, x_18);
lean_ctor_set(x_178, 17, x_19);
lean_ctor_set(x_178, 18, x_20);
lean_ctor_set(x_178, 19, x_21);
lean_ctor_set_uint8(x_178, sizeof(void*)*20, x_7);
x_179 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_175, 0, x_179);
return x_175;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_175, 0);
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_175);
x_182 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_2);
lean_ctor_set(x_182, 2, x_3);
lean_ctor_set(x_182, 3, x_4);
lean_ctor_set(x_182, 4, x_5);
lean_ctor_set(x_182, 5, x_6);
lean_ctor_set(x_182, 6, x_8);
lean_ctor_set(x_182, 7, x_9);
lean_ctor_set(x_182, 8, x_10);
lean_ctor_set(x_182, 9, x_11);
lean_ctor_set(x_182, 10, x_12);
lean_ctor_set(x_182, 11, x_13);
lean_ctor_set(x_182, 12, x_14);
lean_ctor_set(x_182, 13, x_15);
lean_ctor_set(x_182, 14, x_16);
lean_ctor_set(x_182, 15, x_17);
lean_ctor_set(x_182, 16, x_18);
lean_ctor_set(x_182, 17, x_19);
lean_ctor_set(x_182, 18, x_20);
lean_ctor_set(x_182, 19, x_21);
lean_ctor_set_uint8(x_182, sizeof(void*)*20, x_7);
x_183 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
}
else
{
uint8_t x_185; 
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_175);
if (x_185 == 0)
{
return x_175;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_175, 0);
x_187 = lean_ctor_get(x_175, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_175);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_36);
if (x_189 == 0)
{
return x_36;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_36, 0);
x_191 = lean_ctor_get(x_36, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_36);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isProp(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro_with_eq", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34, lean_object* x_35, lean_object* x_36, lean_object* x_37) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_38 = l_Lean_MVarId_assign___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(x_2, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_41, 2, x_5);
lean_ctor_set(x_41, 3, x_6);
lean_ctor_set(x_41, 4, x_7);
lean_ctor_set(x_41, 5, x_8);
lean_ctor_set(x_41, 6, x_10);
lean_ctor_set(x_41, 7, x_11);
lean_ctor_set(x_41, 8, x_12);
lean_ctor_set(x_41, 9, x_13);
lean_ctor_set(x_41, 10, x_14);
lean_ctor_set(x_41, 11, x_15);
lean_ctor_set(x_41, 12, x_16);
lean_ctor_set(x_41, 13, x_17);
lean_ctor_set(x_41, 14, x_18);
lean_ctor_set(x_41, 15, x_19);
lean_ctor_set(x_41, 16, x_20);
lean_ctor_set(x_41, 17, x_21);
lean_ctor_set(x_41, 18, x_22);
lean_ctor_set(x_41, 19, x_23);
lean_ctor_set_uint8(x_41, sizeof(void*)*20, x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set(x_44, 3, x_6);
lean_ctor_set(x_44, 4, x_7);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set(x_44, 6, x_10);
lean_ctor_set(x_44, 7, x_11);
lean_ctor_set(x_44, 8, x_12);
lean_ctor_set(x_44, 9, x_13);
lean_ctor_set(x_44, 10, x_14);
lean_ctor_set(x_44, 11, x_15);
lean_ctor_set(x_44, 12, x_16);
lean_ctor_set(x_44, 13, x_17);
lean_ctor_set(x_44, 14, x_18);
lean_ctor_set(x_44, 15, x_19);
lean_ctor_set(x_44, 16, x_20);
lean_ctor_set(x_44, 17, x_21);
lean_ctor_set(x_44, 18, x_22);
lean_ctor_set(x_44, 19, x_23);
lean_ctor_set_uint8(x_44, sizeof(void*)*20, x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__4;
lean_inc(x_25);
x_49 = l_Lean_Expr_const___override(x_48, x_25);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_25);
lean_inc(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_26);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_28);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_mk(x_54);
x_56 = l_Lean_mkAppN(x_49, x_55);
lean_dec(x_55);
x_57 = l_Lean_MVarId_assign___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(x_2, x_56, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_4);
lean_ctor_set(x_60, 2, x_5);
lean_ctor_set(x_60, 3, x_6);
lean_ctor_set(x_60, 4, x_7);
lean_ctor_set(x_60, 5, x_8);
lean_ctor_set(x_60, 6, x_10);
lean_ctor_set(x_60, 7, x_11);
lean_ctor_set(x_60, 8, x_12);
lean_ctor_set(x_60, 9, x_13);
lean_ctor_set(x_60, 10, x_14);
lean_ctor_set(x_60, 11, x_15);
lean_ctor_set(x_60, 12, x_16);
lean_ctor_set(x_60, 13, x_17);
lean_ctor_set(x_60, 14, x_18);
lean_ctor_set(x_60, 15, x_19);
lean_ctor_set(x_60, 16, x_20);
lean_ctor_set(x_60, 17, x_21);
lean_ctor_set(x_60, 18, x_22);
lean_ctor_set(x_60, 19, x_23);
lean_ctor_set_uint8(x_60, sizeof(void*)*20, x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_24);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_4);
lean_ctor_set(x_63, 2, x_5);
lean_ctor_set(x_63, 3, x_6);
lean_ctor_set(x_63, 4, x_7);
lean_ctor_set(x_63, 5, x_8);
lean_ctor_set(x_63, 6, x_10);
lean_ctor_set(x_63, 7, x_11);
lean_ctor_set(x_63, 8, x_12);
lean_ctor_set(x_63, 9, x_13);
lean_ctor_set(x_63, 10, x_14);
lean_ctor_set(x_63, 11, x_15);
lean_ctor_set(x_63, 12, x_16);
lean_ctor_set(x_63, 13, x_17);
lean_ctor_set(x_63, 14, x_18);
lean_ctor_set(x_63, 15, x_19);
lean_ctor_set(x_63, 16, x_20);
lean_ctor_set(x_63, 17, x_21);
lean_ctor_set(x_63, 18, x_22);
lean_ctor_set(x_63, 19, x_23);
lean_ctor_set_uint8(x_63, sizeof(void*)*20, x_9);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, uint8_t x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
if (x_24 == 0)
{
uint8_t x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
x_33 = 1;
x_34 = l_Lean_Meta_intro1Core(x_1, x_33, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_3);
lean_ctor_set(x_39, 3, x_4);
lean_ctor_set(x_39, 4, x_5);
lean_ctor_set(x_39, 5, x_6);
lean_ctor_set(x_39, 6, x_8);
lean_ctor_set(x_39, 7, x_9);
lean_ctor_set(x_39, 8, x_10);
lean_ctor_set(x_39, 9, x_11);
lean_ctor_set(x_39, 10, x_12);
lean_ctor_set(x_39, 11, x_13);
lean_ctor_set(x_39, 12, x_14);
lean_ctor_set(x_39, 13, x_15);
lean_ctor_set(x_39, 14, x_16);
lean_ctor_set(x_39, 15, x_17);
lean_ctor_set(x_39, 16, x_18);
lean_ctor_set(x_39, 17, x_19);
lean_ctor_set(x_39, 18, x_20);
lean_ctor_set(x_39, 19, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*20, x_7);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 1, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_3);
lean_ctor_set(x_42, 3, x_4);
lean_ctor_set(x_42, 4, x_5);
lean_ctor_set(x_42, 5, x_6);
lean_ctor_set(x_42, 6, x_8);
lean_ctor_set(x_42, 7, x_9);
lean_ctor_set(x_42, 8, x_10);
lean_ctor_set(x_42, 9, x_11);
lean_ctor_set(x_42, 10, x_12);
lean_ctor_set(x_42, 11, x_13);
lean_ctor_set(x_42, 12, x_14);
lean_ctor_set(x_42, 13, x_15);
lean_ctor_set(x_42, 14, x_16);
lean_ctor_set(x_42, 15, x_17);
lean_ctor_set(x_42, 16, x_18);
lean_ctor_set(x_42, 17, x_19);
lean_ctor_set(x_42, 18, x_20);
lean_ctor_set(x_42, 19, x_21);
lean_ctor_set_uint8(x_42, sizeof(void*)*20, x_7);
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_3);
lean_ctor_set(x_49, 3, x_4);
lean_ctor_set(x_49, 4, x_5);
lean_ctor_set(x_49, 5, x_6);
lean_ctor_set(x_49, 6, x_8);
lean_ctor_set(x_49, 7, x_9);
lean_ctor_set(x_49, 8, x_10);
lean_ctor_set(x_49, 9, x_11);
lean_ctor_set(x_49, 10, x_12);
lean_ctor_set(x_49, 11, x_13);
lean_ctor_set(x_49, 12, x_14);
lean_ctor_set(x_49, 13, x_15);
lean_ctor_set(x_49, 14, x_16);
lean_ctor_set(x_49, 15, x_17);
lean_ctor_set(x_49, 16, x_18);
lean_ctor_set(x_49, 17, x_19);
lean_ctor_set(x_49, 18, x_20);
lean_ctor_set(x_49, 19, x_21);
lean_ctor_set_uint8(x_49, sizeof(void*)*20, x_7);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(3, 2, 0);
} else {
 x_50 = x_48;
 lean_ctor_set_tag(x_50, 3);
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
else
{
uint8_t x_52; 
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_inc(x_1);
x_56 = l_Lean_MVarId_getTag(x_1, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Expr_bindingBody_x21(x_22);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_23);
x_60 = l_Lean_Meta_Grind_simp(x_23, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_28, 2);
lean_inc(x_66);
x_67 = l_Lean_Expr_bindingName_x21(x_22);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
lean_dec(x_61);
x_70 = l_Lean_Expr_bindingInfo_x21(x_22);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
x_72 = 0;
lean_inc(x_68);
lean_inc(x_64);
x_73 = l_Lean_LocalContext_mkLocalDecl(x_66, x_64, x_67, x_68, x_71, x_72);
x_74 = l_Lean_Meta_getLocalInstances(x_28, x_29, x_30, x_31, x_65);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = 2;
x_78 = lean_unsigned_to_nat(0u);
lean_inc(x_59);
x_79 = l_Lean_Meta_mkFreshExprMVarAt(x_73, x_75, x_59, x_77, x_57, x_78, x_28, x_29, x_30, x_31, x_76);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
x_83 = l_Lean_Expr_mvarId_x21(x_81);
lean_inc(x_64);
x_84 = l_Lean_Expr_fvar___override(x_64);
x_85 = lean_box(0);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 1, x_85);
lean_ctor_set(x_79, 0, x_84);
x_86 = lean_array_mk(x_79);
x_87 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 10, 2);
lean_closure_set(x_87, 0, x_86);
lean_closure_set(x_87, 1, x_81);
x_88 = lean_box(x_7);
lean_inc(x_83);
x_89 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 37, 28);
lean_closure_set(x_89, 0, x_69);
lean_closure_set(x_89, 1, x_1);
lean_closure_set(x_89, 2, x_83);
lean_closure_set(x_89, 3, x_2);
lean_closure_set(x_89, 4, x_3);
lean_closure_set(x_89, 5, x_4);
lean_closure_set(x_89, 6, x_5);
lean_closure_set(x_89, 7, x_6);
lean_closure_set(x_89, 8, x_88);
lean_closure_set(x_89, 9, x_8);
lean_closure_set(x_89, 10, x_9);
lean_closure_set(x_89, 11, x_10);
lean_closure_set(x_89, 12, x_11);
lean_closure_set(x_89, 13, x_12);
lean_closure_set(x_89, 14, x_13);
lean_closure_set(x_89, 15, x_14);
lean_closure_set(x_89, 16, x_15);
lean_closure_set(x_89, 17, x_16);
lean_closure_set(x_89, 18, x_17);
lean_closure_set(x_89, 19, x_18);
lean_closure_set(x_89, 20, x_19);
lean_closure_set(x_89, 21, x_20);
lean_closure_set(x_89, 22, x_21);
lean_closure_set(x_89, 23, x_64);
lean_closure_set(x_89, 24, x_85);
lean_closure_set(x_89, 25, x_59);
lean_closure_set(x_89, 26, x_68);
lean_closure_set(x_89, 27, x_23);
x_90 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_90, 0, x_87);
lean_closure_set(x_90, 1, x_89);
x_91 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_83, x_90, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_82);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_79, 0);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_79);
x_94 = l_Lean_Expr_mvarId_x21(x_92);
lean_inc(x_64);
x_95 = l_Lean_Expr_fvar___override(x_64);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_mk(x_97);
x_99 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 10, 2);
lean_closure_set(x_99, 0, x_98);
lean_closure_set(x_99, 1, x_92);
x_100 = lean_box(x_7);
lean_inc(x_94);
x_101 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 37, 28);
lean_closure_set(x_101, 0, x_69);
lean_closure_set(x_101, 1, x_1);
lean_closure_set(x_101, 2, x_94);
lean_closure_set(x_101, 3, x_2);
lean_closure_set(x_101, 4, x_3);
lean_closure_set(x_101, 5, x_4);
lean_closure_set(x_101, 6, x_5);
lean_closure_set(x_101, 7, x_6);
lean_closure_set(x_101, 8, x_100);
lean_closure_set(x_101, 9, x_8);
lean_closure_set(x_101, 10, x_9);
lean_closure_set(x_101, 11, x_10);
lean_closure_set(x_101, 12, x_11);
lean_closure_set(x_101, 13, x_12);
lean_closure_set(x_101, 14, x_13);
lean_closure_set(x_101, 15, x_14);
lean_closure_set(x_101, 16, x_15);
lean_closure_set(x_101, 17, x_16);
lean_closure_set(x_101, 18, x_17);
lean_closure_set(x_101, 19, x_18);
lean_closure_set(x_101, 20, x_19);
lean_closure_set(x_101, 21, x_20);
lean_closure_set(x_101, 22, x_21);
lean_closure_set(x_101, 23, x_64);
lean_closure_set(x_101, 24, x_96);
lean_closure_set(x_101, 25, x_59);
lean_closure_set(x_101, 26, x_68);
lean_closure_set(x_101, 27, x_23);
x_102 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_102, 0, x_99);
lean_closure_set(x_102, 1, x_101);
x_103 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_94, x_102, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_93);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_60);
if (x_104 == 0)
{
return x_60;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_60, 0);
x_106 = lean_ctor_get(x_60, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_60);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_56);
if (x_108 == 0)
{
return x_56;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_56, 0);
x_110 = lean_ctor_get(x_56, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_56);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*20);
x_18 = lean_ctor_get(x_1, 6);
lean_inc(x_18);
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
lean_dec(x_1);
lean_inc(x_11);
x_32 = l_Lean_MVarId_getType(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = l_Lean_Expr_isArrow(x_34);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_isLet(x_34);
if (x_37 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_isForall(x_34);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Expr_isLetFun(x_34);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_34);
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
x_58 = lean_box(0);
lean_ctor_set(x_32, 0, x_58);
return x_32;
}
else
{
lean_object* x_59; 
lean_free_object(x_32);
x_59 = lean_box(0);
x_38 = x_59;
goto block_55;
}
}
else
{
lean_object* x_60; 
lean_free_object(x_32);
x_60 = lean_box(0);
x_38 = x_60;
goto block_55;
}
}
else
{
lean_object* x_61; 
lean_free_object(x_32);
x_61 = lean_box(0);
x_38 = x_61;
goto block_55;
}
block_55:
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_38);
x_39 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Lean_Meta_intro1Core(x_11, x_39, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_43);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_45, 0, x_43);
x_46 = lean_box(x_17);
x_47 = lean_box(x_37);
lean_inc(x_44);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 34, 25);
lean_closure_set(x_48, 0, x_44);
lean_closure_set(x_48, 1, x_12);
lean_closure_set(x_48, 2, x_13);
lean_closure_set(x_48, 3, x_14);
lean_closure_set(x_48, 4, x_15);
lean_closure_set(x_48, 5, x_16);
lean_closure_set(x_48, 6, x_46);
lean_closure_set(x_48, 7, x_18);
lean_closure_set(x_48, 8, x_19);
lean_closure_set(x_48, 9, x_20);
lean_closure_set(x_48, 10, x_21);
lean_closure_set(x_48, 11, x_22);
lean_closure_set(x_48, 12, x_23);
lean_closure_set(x_48, 13, x_24);
lean_closure_set(x_48, 14, x_25);
lean_closure_set(x_48, 15, x_26);
lean_closure_set(x_48, 16, x_27);
lean_closure_set(x_48, 17, x_28);
lean_closure_set(x_48, 18, x_29);
lean_closure_set(x_48, 19, x_30);
lean_closure_set(x_48, 20, x_31);
lean_closure_set(x_48, 21, x_43);
lean_closure_set(x_48, 22, x_2);
lean_closure_set(x_48, 23, x_47);
lean_closure_set(x_48, 24, x_34);
x_49 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_49, 0, x_45);
lean_closure_set(x_49, 1, x_48);
x_50 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_44, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_34);
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
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_32);
lean_dec(x_2);
x_62 = l_Lean_Expr_bindingDomain_x21(x_34);
lean_inc(x_62);
x_63 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 9, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = lean_box(x_17);
lean_inc(x_11);
x_65 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed), 32, 23);
lean_closure_set(x_65, 0, x_11);
lean_closure_set(x_65, 1, x_12);
lean_closure_set(x_65, 2, x_13);
lean_closure_set(x_65, 3, x_14);
lean_closure_set(x_65, 4, x_15);
lean_closure_set(x_65, 5, x_16);
lean_closure_set(x_65, 6, x_64);
lean_closure_set(x_65, 7, x_18);
lean_closure_set(x_65, 8, x_19);
lean_closure_set(x_65, 9, x_20);
lean_closure_set(x_65, 10, x_21);
lean_closure_set(x_65, 11, x_22);
lean_closure_set(x_65, 12, x_23);
lean_closure_set(x_65, 13, x_24);
lean_closure_set(x_65, 14, x_25);
lean_closure_set(x_65, 15, x_26);
lean_closure_set(x_65, 16, x_27);
lean_closure_set(x_65, 17, x_28);
lean_closure_set(x_65, 18, x_29);
lean_closure_set(x_65, 19, x_30);
lean_closure_set(x_65, 20, x_31);
lean_closure_set(x_65, 21, x_34);
lean_closure_set(x_65, 22, x_62);
x_66 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_66, 0, x_63);
lean_closure_set(x_66, 1, x_65);
x_67 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_32, 0);
x_69 = lean_ctor_get(x_32, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_32);
x_70 = l_Lean_Expr_isArrow(x_68);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; 
x_71 = l_Lean_Expr_isLet(x_68);
if (x_71 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Expr_isForall(x_68);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Expr_isLetFun(x_68);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_68);
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
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_69);
return x_93;
}
else
{
lean_object* x_94; 
x_94 = lean_box(0);
x_72 = x_94;
goto block_89;
}
}
else
{
lean_object* x_95; 
x_95 = lean_box(0);
x_72 = x_95;
goto block_89;
}
}
else
{
lean_object* x_96; 
x_96 = lean_box(0);
x_72 = x_96;
goto block_89;
}
block_89:
{
uint8_t x_73; lean_object* x_74; 
lean_dec(x_72);
x_73 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_74 = l_Lean_Meta_intro1Core(x_11, x_73, x_6, x_7, x_8, x_9, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_inc(x_77);
x_79 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_79, 0, x_77);
x_80 = lean_box(x_17);
x_81 = lean_box(x_71);
lean_inc(x_78);
x_82 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 34, 25);
lean_closure_set(x_82, 0, x_78);
lean_closure_set(x_82, 1, x_12);
lean_closure_set(x_82, 2, x_13);
lean_closure_set(x_82, 3, x_14);
lean_closure_set(x_82, 4, x_15);
lean_closure_set(x_82, 5, x_16);
lean_closure_set(x_82, 6, x_80);
lean_closure_set(x_82, 7, x_18);
lean_closure_set(x_82, 8, x_19);
lean_closure_set(x_82, 9, x_20);
lean_closure_set(x_82, 10, x_21);
lean_closure_set(x_82, 11, x_22);
lean_closure_set(x_82, 12, x_23);
lean_closure_set(x_82, 13, x_24);
lean_closure_set(x_82, 14, x_25);
lean_closure_set(x_82, 15, x_26);
lean_closure_set(x_82, 16, x_27);
lean_closure_set(x_82, 17, x_28);
lean_closure_set(x_82, 18, x_29);
lean_closure_set(x_82, 19, x_30);
lean_closure_set(x_82, 20, x_31);
lean_closure_set(x_82, 21, x_77);
lean_closure_set(x_82, 22, x_2);
lean_closure_set(x_82, 23, x_81);
lean_closure_set(x_82, 24, x_68);
x_83 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_83, 0, x_79);
lean_closure_set(x_83, 1, x_82);
x_84 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_78, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_68);
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
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_87 = x_74;
} else {
 lean_dec_ref(x_74);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_2);
x_97 = l_Lean_Expr_bindingDomain_x21(x_68);
lean_inc(x_97);
x_98 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 9, 1);
lean_closure_set(x_98, 0, x_97);
x_99 = lean_box(x_17);
lean_inc(x_11);
x_100 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed), 32, 23);
lean_closure_set(x_100, 0, x_11);
lean_closure_set(x_100, 1, x_12);
lean_closure_set(x_100, 2, x_13);
lean_closure_set(x_100, 3, x_14);
lean_closure_set(x_100, 4, x_15);
lean_closure_set(x_100, 5, x_16);
lean_closure_set(x_100, 6, x_99);
lean_closure_set(x_100, 7, x_18);
lean_closure_set(x_100, 8, x_19);
lean_closure_set(x_100, 9, x_20);
lean_closure_set(x_100, 10, x_21);
lean_closure_set(x_100, 11, x_22);
lean_closure_set(x_100, 12, x_23);
lean_closure_set(x_100, 13, x_24);
lean_closure_set(x_100, 14, x_25);
lean_closure_set(x_100, 15, x_26);
lean_closure_set(x_100, 16, x_27);
lean_closure_set(x_100, 17, x_28);
lean_closure_set(x_100, 18, x_29);
lean_closure_set(x_100, 19, x_30);
lean_closure_set(x_100, 20, x_31);
lean_closure_set(x_100, 21, x_68);
lean_closure_set(x_100, 22, x_97);
x_101 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_101, 0, x_98);
lean_closure_set(x_101, 1, x_100);
x_102 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_101, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
return x_102;
}
}
}
else
{
uint8_t x_103; 
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
x_103 = !lean_is_exclusive(x_32);
if (x_103 == 0)
{
return x_32;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_32, 0);
x_105 = lean_ctor_get(x_32, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_32);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_assign___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
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
_start:
{
uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_unbox(x_7);
lean_dec(x_7);
x_36 = lean_unbox(x_24);
lean_dec(x_24);
x_37 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_36, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
lean_dec(x_26);
lean_dec(x_25);
return x_37;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed(lean_object** _args) {
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
uint8_t x_38; lean_object* x_39; 
x_38 = lean_unbox(x_9);
lean_dec(x_9);
x_39 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
return x_39;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_unbox(x_7);
lean_dec(x_7);
x_34 = lean_unbox(x_24);
lean_dec(x_24);
x_35 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_34, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
lean_dec(x_22);
return x_35;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*20);
x_14 = lean_ctor_get(x_1, 6);
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
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_8);
lean_ctor_set(x_28, 2, x_9);
lean_ctor_set(x_28, 3, x_10);
lean_ctor_set(x_28, 4, x_11);
lean_ctor_set(x_28, 5, x_12);
lean_ctor_set(x_28, 6, x_14);
lean_ctor_set(x_28, 7, x_15);
lean_ctor_set(x_28, 8, x_16);
lean_ctor_set(x_28, 9, x_17);
lean_ctor_set(x_28, 10, x_18);
lean_ctor_set(x_28, 11, x_19);
lean_ctor_set(x_28, 12, x_20);
lean_ctor_set(x_28, 13, x_21);
lean_ctor_set(x_28, 14, x_22);
lean_ctor_set(x_28, 15, x_23);
lean_ctor_set(x_28, 16, x_24);
lean_ctor_set(x_28, 17, x_25);
lean_ctor_set(x_28, 18, x_26);
lean_ctor_set(x_28, 19, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*20, x_13);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_28);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_ctor_get(x_1, 3);
x_35 = lean_ctor_get(x_1, 4);
x_36 = lean_ctor_get(x_1, 5);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*20);
x_38 = lean_ctor_get(x_1, 6);
x_39 = lean_ctor_get(x_1, 7);
x_40 = lean_ctor_get(x_1, 8);
x_41 = lean_ctor_get(x_1, 9);
x_42 = lean_ctor_get(x_1, 10);
x_43 = lean_ctor_get(x_1, 11);
x_44 = lean_ctor_get(x_1, 12);
x_45 = lean_ctor_get(x_1, 13);
x_46 = lean_ctor_get(x_1, 14);
x_47 = lean_ctor_get(x_1, 15);
x_48 = lean_ctor_get(x_1, 16);
x_49 = lean_ctor_get(x_1, 17);
x_50 = lean_ctor_get(x_1, 18);
x_51 = lean_ctor_get(x_1, 19);
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
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_52 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_52, 0, x_30);
lean_ctor_set(x_52, 1, x_32);
lean_ctor_set(x_52, 2, x_33);
lean_ctor_set(x_52, 3, x_34);
lean_ctor_set(x_52, 4, x_35);
lean_ctor_set(x_52, 5, x_36);
lean_ctor_set(x_52, 6, x_38);
lean_ctor_set(x_52, 7, x_39);
lean_ctor_set(x_52, 8, x_40);
lean_ctor_set(x_52, 9, x_41);
lean_ctor_set(x_52, 10, x_42);
lean_ctor_set(x_52, 11, x_43);
lean_ctor_set(x_52, 12, x_44);
lean_ctor_set(x_52, 13, x_45);
lean_ctor_set(x_52, 14, x_46);
lean_ctor_set(x_52, 15, x_47);
lean_ctor_set(x_52, 16, x_48);
lean_ctor_set(x_52, 17, x_49);
lean_ctor_set(x_52, 18, x_50);
lean_ctor_set(x_52, 19, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*20, x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
x_2 = x_31;
x_3 = x_53;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_29 = l_Lean_Meta_Grind_injection_x3f(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_free_object(x_1);
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
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set(x_30, 0, x_1);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
lean_ctor_set(x_1, 0, x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_29, 0, x_42);
return x_29;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_44);
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_1);
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
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_54 = lean_ctor_get(x_1, 2);
x_55 = lean_ctor_get(x_1, 3);
x_56 = lean_ctor_get(x_1, 4);
x_57 = lean_ctor_get(x_1, 5);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*20);
x_59 = lean_ctor_get(x_1, 6);
x_60 = lean_ctor_get(x_1, 7);
x_61 = lean_ctor_get(x_1, 8);
x_62 = lean_ctor_get(x_1, 9);
x_63 = lean_ctor_get(x_1, 10);
x_64 = lean_ctor_get(x_1, 11);
x_65 = lean_ctor_get(x_1, 12);
x_66 = lean_ctor_get(x_1, 13);
x_67 = lean_ctor_get(x_1, 14);
x_68 = lean_ctor_get(x_1, 15);
x_69 = lean_ctor_get(x_1, 16);
x_70 = lean_ctor_get(x_1, 17);
x_71 = lean_ctor_get(x_1, 18);
x_72 = lean_ctor_get(x_1, 19);
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
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_73 = l_Lean_Meta_Grind_injection_x3f(x_52, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
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
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_82 = x_74;
} else {
 lean_dec_ref(x_74);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_53);
lean_ctor_set(x_83, 2, x_54);
lean_ctor_set(x_83, 3, x_55);
lean_ctor_set(x_83, 4, x_56);
lean_ctor_set(x_83, 5, x_57);
lean_ctor_set(x_83, 6, x_59);
lean_ctor_set(x_83, 7, x_60);
lean_ctor_set(x_83, 8, x_61);
lean_ctor_set(x_83, 9, x_62);
lean_ctor_set(x_83, 10, x_63);
lean_ctor_set(x_83, 11, x_64);
lean_ctor_set(x_83, 12, x_65);
lean_ctor_set(x_83, 13, x_66);
lean_ctor_set(x_83, 14, x_67);
lean_ctor_set(x_83, 15, x_68);
lean_ctor_set(x_83, 16, x_69);
lean_ctor_set(x_83, 17, x_70);
lean_ctor_set(x_83, 18, x_71);
lean_ctor_set(x_83, 19, x_72);
lean_ctor_set_uint8(x_83, sizeof(void*)*20, x_58);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
x_86 = lean_ctor_get(x_73, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_73, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_88 = x_73;
} else {
 lean_dec_ref(x_73);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
lean_object* x_34; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_1, x_2, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_37 = l_Lean_MVarId_byContra_x3f(x_3, x_29, x_30, x_31, x_32, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_st_ref_take(x_25, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_array_push(x_41, x_1);
x_44 = lean_st_ref_set(x_25, x_43, x_42);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_dec(x_37);
x_52 = lean_ctor_get(x_38, 0);
lean_inc(x_52);
lean_dec(x_38);
x_53 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
lean_ctor_set(x_53, 2, x_5);
lean_ctor_set(x_53, 3, x_6);
lean_ctor_set(x_53, 4, x_7);
lean_ctor_set(x_53, 5, x_8);
lean_ctor_set(x_53, 6, x_10);
lean_ctor_set(x_53, 7, x_11);
lean_ctor_set(x_53, 8, x_12);
lean_ctor_set(x_53, 9, x_13);
lean_ctor_set(x_53, 10, x_14);
lean_ctor_set(x_53, 11, x_15);
lean_ctor_set(x_53, 12, x_16);
lean_ctor_set(x_53, 13, x_17);
lean_ctor_set(x_53, 14, x_18);
lean_ctor_set(x_53, 15, x_19);
lean_ctor_set(x_53, 16, x_20);
lean_ctor_set(x_53, 17, x_21);
lean_ctor_set(x_53, 18, x_22);
lean_ctor_set(x_53, 19, x_23);
lean_ctor_set_uint8(x_53, sizeof(void*)*20, x_9);
x_54 = l_Lean_Meta_Grind_intros_go(x_2, x_53, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_37);
if (x_55 == 0)
{
return x_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_37, 0);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_37);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 1:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = lean_ctor_get(x_35, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_35, 1);
lean_inc(x_61);
lean_dec(x_35);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_60);
lean_inc(x_61);
x_62 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_61, x_60, x_29, x_30, x_31, x_32, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_60);
lean_inc(x_61);
x_65 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(x_61, x_60, x_29, x_30, x_31, x_32, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_69, 0, x_61);
lean_inc(x_2);
x_70 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_intros_go___lambda__1), 11, 2);
lean_closure_set(x_70, 0, x_60);
lean_closure_set(x_70, 1, x_2);
x_71 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_71, 0, x_69);
lean_closure_set(x_71, 1, x_70);
x_72 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___closed__1;
x_73 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_73, 0, x_71);
lean_closure_set(x_73, 1, x_72);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_74 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_68, x_73, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_67);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_Grind_intros_go(x_2, x_75, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_76);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 0);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_74);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_61);
lean_dec(x_60);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_dec(x_65);
x_83 = lean_ctor_get(x_66, 0);
lean_inc(x_83);
lean_dec(x_66);
x_84 = l_Lean_Meta_Grind_intros_go(x_2, x_83, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_65);
if (x_85 == 0)
{
return x_65;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_65, 0);
x_87 = lean_ctor_get(x_65, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_65);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_61);
lean_dec(x_60);
x_89 = lean_ctor_get(x_62, 1);
lean_inc(x_89);
lean_dec(x_62);
x_90 = lean_ctor_get(x_63, 0);
lean_inc(x_90);
lean_dec(x_63);
x_91 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(x_2, x_90, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_62);
if (x_92 == 0)
{
return x_62;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_62, 0);
x_94 = lean_ctor_get(x_62, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_62);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 2:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_ctor_get(x_34, 1);
lean_inc(x_96);
lean_dec(x_34);
x_97 = lean_ctor_get(x_35, 0);
lean_inc(x_97);
lean_dec(x_35);
x_98 = l_Lean_Meta_Grind_intros_go(x_2, x_97, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_96);
return x_98;
}
default: 
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_34, 1);
lean_inc(x_99);
lean_dec(x_34);
x_100 = lean_ctor_get(x_35, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_35, 1);
lean_inc(x_101);
lean_dec(x_35);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_101);
x_102 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_101, x_100, x_29, x_30, x_31, x_32, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Meta_Grind_intros_go(x_2, x_101, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_101);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
lean_dec(x_103);
x_108 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(x_2, x_107, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_106);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_101);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_102);
if (x_109 == 0)
{
return x_102;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_102, 0);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_102);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_34);
if (x_113 == 0)
{
return x_34;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_34, 0);
x_115 = lean_ctor_get(x_34, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_34);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*20);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Grind_intros_go___lambda__2(x_2, x_1, x_13, x_14, x_15, x_16, x_17, x_18, x_12, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
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
_start:
{
uint8_t x_34; lean_object* x_35; 
x_34 = lean_unbox(x_9);
lean_dec(x_9);
x_35 = l_Lean_Meta_Grind_intros_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_25);
lean_dec(x_24);
return x_35;
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
x_13 = l_Lean_Meta_Grind_simp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*20);
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
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*20);
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_93 = l_Lean_MVarId_assert(x_73, x_70, x_2, x_1, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_ctor_set(x_4, 0, x_94);
x_96 = l_Lean_Meta_Grind_intros(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_95);
return x_96;
}
else
{
uint8_t x_97; 
lean_free_object(x_4);
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
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 0);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_93);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_101 = lean_ctor_get(x_4, 0);
x_102 = lean_ctor_get(x_4, 1);
x_103 = lean_ctor_get(x_4, 2);
x_104 = lean_ctor_get(x_4, 3);
x_105 = lean_ctor_get(x_4, 4);
x_106 = lean_ctor_get(x_4, 5);
x_107 = lean_ctor_get_uint8(x_4, sizeof(void*)*20);
x_108 = lean_ctor_get(x_4, 6);
x_109 = lean_ctor_get(x_4, 7);
x_110 = lean_ctor_get(x_4, 8);
x_111 = lean_ctor_get(x_4, 9);
x_112 = lean_ctor_get(x_4, 10);
x_113 = lean_ctor_get(x_4, 11);
x_114 = lean_ctor_get(x_4, 12);
x_115 = lean_ctor_get(x_4, 13);
x_116 = lean_ctor_get(x_4, 14);
x_117 = lean_ctor_get(x_4, 15);
x_118 = lean_ctor_get(x_4, 16);
x_119 = lean_ctor_get(x_4, 17);
x_120 = lean_ctor_get(x_4, 18);
x_121 = lean_ctor_get(x_4, 19);
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
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_122 = l_Lean_MVarId_assert(x_101, x_70, x_2, x_1, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_102);
lean_ctor_set(x_125, 2, x_103);
lean_ctor_set(x_125, 3, x_104);
lean_ctor_set(x_125, 4, x_105);
lean_ctor_set(x_125, 5, x_106);
lean_ctor_set(x_125, 6, x_108);
lean_ctor_set(x_125, 7, x_109);
lean_ctor_set(x_125, 8, x_110);
lean_ctor_set(x_125, 9, x_111);
lean_ctor_set(x_125, 10, x_112);
lean_ctor_set(x_125, 11, x_113);
lean_ctor_set(x_125, 12, x_114);
lean_ctor_set(x_125, 13, x_115);
lean_ctor_set(x_125, 14, x_116);
lean_ctor_set(x_125, 15, x_117);
lean_ctor_set(x_125, 16, x_118);
lean_ctor_set(x_125, 17, x_119);
lean_ctor_set(x_125, 18, x_120);
lean_ctor_set(x_125, 19, x_121);
lean_ctor_set_uint8(x_125, sizeof(void*)*20, x_107);
x_126 = l_Lean_Meta_Grind_intros(x_3, x_125, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_124);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
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
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_31 = l_Std_Queue_dequeue_x3f___rarg(x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_1);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
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
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 2);
lean_inc(x_40);
lean_dec(x_36);
lean_ctor_set(x_1, 14, x_37);
x_41 = l_Lean_Meta_Grind_assertAt(x_38, x_39, x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_41, 0, x_31);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set(x_31, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_free_object(x_31);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
lean_dec(x_31);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 2);
lean_inc(x_56);
lean_dec(x_52);
lean_ctor_set(x_1, 14, x_53);
x_57 = l_Lean_Meta_Grind_assertAt(x_54, x_55, x_56, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
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
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
x_69 = lean_ctor_get(x_1, 2);
x_70 = lean_ctor_get(x_1, 3);
x_71 = lean_ctor_get(x_1, 4);
x_72 = lean_ctor_get(x_1, 5);
x_73 = lean_ctor_get_uint8(x_1, sizeof(void*)*20);
x_74 = lean_ctor_get(x_1, 6);
x_75 = lean_ctor_get(x_1, 7);
x_76 = lean_ctor_get(x_1, 8);
x_77 = lean_ctor_get(x_1, 9);
x_78 = lean_ctor_get(x_1, 10);
x_79 = lean_ctor_get(x_1, 11);
x_80 = lean_ctor_get(x_1, 12);
x_81 = lean_ctor_get(x_1, 13);
x_82 = lean_ctor_get(x_1, 14);
x_83 = lean_ctor_get(x_1, 15);
x_84 = lean_ctor_get(x_1, 16);
x_85 = lean_ctor_get(x_1, 17);
x_86 = lean_ctor_get(x_1, 18);
x_87 = lean_ctor_get(x_1, 19);
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
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_1);
x_88 = l_Std_Queue_dequeue_x3f___rarg(x_82);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_9);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 2);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(x_98, 0, x_67);
lean_ctor_set(x_98, 1, x_68);
lean_ctor_set(x_98, 2, x_69);
lean_ctor_set(x_98, 3, x_70);
lean_ctor_set(x_98, 4, x_71);
lean_ctor_set(x_98, 5, x_72);
lean_ctor_set(x_98, 6, x_74);
lean_ctor_set(x_98, 7, x_75);
lean_ctor_set(x_98, 8, x_76);
lean_ctor_set(x_98, 9, x_77);
lean_ctor_set(x_98, 10, x_78);
lean_ctor_set(x_98, 11, x_79);
lean_ctor_set(x_98, 12, x_80);
lean_ctor_set(x_98, 13, x_81);
lean_ctor_set(x_98, 14, x_94);
lean_ctor_set(x_98, 15, x_83);
lean_ctor_set(x_98, 16, x_84);
lean_ctor_set(x_98, 17, x_85);
lean_ctor_set(x_98, 18, x_86);
lean_ctor_set(x_98, 19, x_87);
lean_ctor_set_uint8(x_98, sizeof(void*)*20, x_73);
x_99 = l_Lean_Meta_Grind_assertAt(x_95, x_96, x_97, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_92;
}
lean_ctor_set(x_103, 0, x_100);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_92);
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
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
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__3);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__4);
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
