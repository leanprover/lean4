// Lean compiler output
// Module: Lean.Meta.Tactic.Injection
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Intro
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_injectionIntro___closed__0;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__2;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__5;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___closed__0;
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__0;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__4;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__0;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___closed__1;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__16;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__1;
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__3;
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__8;
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__4;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__12;
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__14;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__15;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__2;
static uint64_t l_Lean_Meta_injectionCore___lam__0___closed__10;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_nat_dec_lt(x_7, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_nat_add(x_17, x_7);
lean_inc(x_2);
x_19 = lean_array_get(x_2, x_3, x_18);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = lean_infer_type(x_19, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_isProp(x_21, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_30 = lean_unbox(x_24);
lean_dec(x_24);
if (x_30 == 0)
{
x_26 = x_6;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_26 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_27; 
x_27 = lean_nat_add(x_7, x_14);
lean_dec(x_7);
x_6 = x_26;
x_7 = x_27;
x_12 = x_25;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
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
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(x_2, x_3, x_4, x_12, x_13, x_11, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getCtorNumPropFields___lam__0___boxed), 10, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_9, x_11, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getCtorNumPropFields___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality of constructor applications expected", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__7;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_injectionCore___lam__0___closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(1);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed noConfusion auxiliary construction", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__12;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__13;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lam__0___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_270; 
lean_inc(x_2);
lean_inc(x_1);
x_270 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
lean_inc(x_4);
lean_inc(x_3);
x_272 = l_Lean_FVarId_getDecl___redArg(x_3, x_4, x_6, x_7, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_318; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_318 = lean_ctor_get(x_273, 3);
lean_inc(x_318);
lean_dec(x_273);
x_275 = x_318;
goto block_317;
block_317:
{
lean_object* x_276; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_276 = lean_whnf(x_275, x_4, x_5, x_6, x_7, x_274);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_3);
x_279 = l_Lean_Expr_fvar___override(x_3);
x_280 = l_Lean_Meta_injectionCore___lam__0___closed__16;
x_281 = lean_unsigned_to_nat(4u);
x_282 = l_Lean_Expr_isAppOfArity(x_277, x_280, x_281);
if (x_282 == 0)
{
x_17 = x_277;
x_18 = x_279;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_278;
goto block_269;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_283 = l_Lean_Expr_appFn_x21(x_277);
x_284 = l_Lean_Expr_appFn_x21(x_283);
x_285 = l_Lean_Expr_appFn_x21(x_284);
x_286 = l_Lean_Expr_appArg_x21(x_285);
lean_dec(x_285);
x_287 = l_Lean_Expr_appArg_x21(x_283);
lean_dec(x_283);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_288 = l_Lean_Meta_isExprDefEq(x_286, x_287, x_4, x_5, x_6, x_7, x_278);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_unbox(x_289);
lean_dec(x_289);
if (x_290 == 0)
{
lean_object* x_291; 
lean_dec(x_284);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_17 = x_277;
x_18 = x_279;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_291;
goto block_269;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
lean_dec(x_288);
x_293 = l_Lean_Expr_appArg_x21(x_284);
lean_dec(x_284);
x_294 = l_Lean_Expr_appArg_x21(x_277);
lean_dec(x_277);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_295 = l_Lean_Meta_mkEq(x_293, x_294, x_4, x_5, x_6, x_7, x_292);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_298 = l_Lean_Meta_mkEqOfHEq(x_279, x_282, x_4, x_5, x_6, x_7, x_297);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_17 = x_296;
x_18 = x_299;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_300;
goto block_269;
}
else
{
uint8_t x_301; 
lean_dec(x_296);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_298);
if (x_301 == 0)
{
return x_298;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_298, 0);
x_303 = lean_ctor_get(x_298, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_298);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_279);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_295);
if (x_305 == 0)
{
return x_295;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_295, 0);
x_307 = lean_ctor_get(x_295, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_295);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_284);
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_309 = !lean_is_exclusive(x_288);
if (x_309 == 0)
{
return x_288;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_288, 0);
x_311 = lean_ctor_get(x_288, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_288);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
}
else
{
uint8_t x_313; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_276);
if (x_313 == 0)
{
return x_276;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_276, 0);
x_315 = lean_ctor_get(x_276, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_276);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_319 = !lean_is_exclusive(x_272);
if (x_319 == 0)
{
return x_272;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_272, 0);
x_321 = lean_ctor_get(x_272, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_272);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
uint8_t x_323; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_270);
if (x_323 == 0)
{
return x_270;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_270, 0);
x_325 = lean_ctor_get(x_270, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_270);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_injectionCore___lam__0___closed__3;
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_15;
}
block_269:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Meta_injectionCore___lam__0___closed__5;
x_25 = lean_unsigned_to_nat(3u);
x_26 = l_Lean_Expr_isAppOfArity(x_17, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
x_27 = l_Lean_Meta_injectionCore___lam__0___closed__9;
x_28 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_27, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_28;
}
else
{
lean_object* x_29; 
lean_inc(x_1);
x_29 = l_Lean_MVarId_getType(x_1, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_appFn_x21(x_17);
x_33 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_34 = l_Lean_Meta_isConstructorApp_x27_x3f(x_33, x_19, x_20, x_21, x_22, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_38 = l_Lean_Meta_isConstructorApp_x27_x3f(x_37, x_19, x_20, x_21, x_22, x_36);
if (lean_obj_tag(x_38) == 0)
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_3);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_9 = x_19;
x_10 = x_20;
x_11 = x_21;
x_12 = x_22;
x_13 = x_39;
goto block_16;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_3);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_9 = x_19;
x_10 = x_20;
x_11 = x_21;
x_12 = x_22;
x_13 = x_41;
goto block_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_ctor_get_uint64(x_19, sizeof(void*)*7);
x_47 = lean_ctor_get_uint8(x_19, sizeof(void*)*7 + 8);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_19, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_19, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_19, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_19, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_19, 6);
lean_inc(x_53);
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get_uint8(x_19, sizeof(void*)*7 + 9);
x_56 = lean_ctor_get_uint8(x_19, sizeof(void*)*7 + 10);
x_57 = lean_box(1);
x_58 = lean_unbox(x_57);
lean_ctor_set_uint8(x_42, 9, x_58);
x_59 = 2;
x_60 = lean_uint64_shift_right(x_46, x_59);
x_61 = lean_uint64_shift_left(x_60, x_59);
x_62 = l_Lean_Meta_injectionCore___lam__0___closed__10;
x_63 = lean_uint64_lor(x_61, x_62);
x_64 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_64, 0, x_42);
lean_ctor_set(x_64, 1, x_48);
lean_ctor_set(x_64, 2, x_49);
lean_ctor_set(x_64, 3, x_50);
lean_ctor_set(x_64, 4, x_51);
lean_ctor_set(x_64, 5, x_52);
lean_ctor_set(x_64, 6, x_53);
lean_ctor_set_uint64(x_64, sizeof(void*)*7, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 8, x_47);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 9, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 10, x_56);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_65 = l_Lean_Meta_mkNoConfusion(x_30, x_18, x_64, x_20, x_21, x_22, x_43);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_44, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
lean_dec(x_45);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_ctor_get(x_44, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_name_eq(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_70);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
x_74 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_68, x_20, x_69);
lean_dec(x_20);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_68);
x_81 = lean_infer_type(x_68, x_19, x_20, x_21, x_22, x_69);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_84 = l_Lean_Meta_whnfD(x_82, x_19, x_20, x_21, x_22, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 7)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_2);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_1);
x_88 = l_Lean_MVarId_getTag(x_1, x_19, x_20, x_21, x_22, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Expr_headBeta(x_87);
lean_inc(x_19);
x_92 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_91, x_89, x_19, x_20, x_21, x_22, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_93);
x_95 = l_Lean_Expr_app___override(x_68, x_93);
x_96 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_95, x_20, x_94);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 1);
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
x_100 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_101 = l_Lean_MVarId_tryClear(x_100, x_3, x_19, x_20, x_21, x_22, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Meta_getCtorNumPropFields(x_44, x_19, x_20, x_21, x_22, x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_nat_sub(x_70, x_106);
lean_dec(x_106);
lean_dec(x_70);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_107);
lean_ctor_set(x_96, 0, x_102);
lean_ctor_set(x_104, 0, x_96);
return x_104;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_104, 0);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_104);
x_110 = lean_nat_sub(x_70, x_108);
lean_dec(x_108);
lean_dec(x_70);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_110);
lean_ctor_set(x_96, 0, x_102);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_96);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_dec(x_102);
lean_free_object(x_96);
lean_dec(x_70);
x_112 = !lean_is_exclusive(x_104);
if (x_112 == 0)
{
return x_104;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_104, 0);
x_114 = lean_ctor_get(x_104, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_104);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_96);
lean_dec(x_70);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_116 = !lean_is_exclusive(x_101);
if (x_116 == 0)
{
return x_101;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_101, 0);
x_118 = lean_ctor_get(x_101, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_101);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_96, 1);
lean_inc(x_120);
lean_dec(x_96);
x_121 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_122 = l_Lean_MVarId_tryClear(x_121, x_3, x_19, x_20, x_21, x_22, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Meta_getCtorNumPropFields(x_44, x_19, x_20, x_21, x_22, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_nat_sub(x_70, x_126);
lean_dec(x_126);
lean_dec(x_70);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_123);
lean_ctor_set(x_130, 1, x_129);
if (lean_is_scalar(x_128)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_128;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_127);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_123);
lean_dec(x_70);
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_134 = x_125;
} else {
 lean_dec_ref(x_125);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_70);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_136 = lean_ctor_get(x_122, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_122, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_138 = x_122;
} else {
 lean_dec_ref(x_122);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_87);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_88);
if (x_140 == 0)
{
return x_88;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_88, 0);
x_142 = lean_ctor_get(x_88, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_88);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_85);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_44);
lean_dec(x_3);
x_144 = lean_ctor_get(x_84, 1);
lean_inc(x_144);
lean_dec(x_84);
x_145 = l_Lean_Meta_injectionCore___lam__0___closed__14;
x_146 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_145, x_19, x_20, x_21, x_22, x_144);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_146;
}
}
else
{
uint8_t x_147; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_84);
if (x_147 == 0)
{
return x_84;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_84, 0);
x_149 = lean_ctor_get(x_84, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_84);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_81);
if (x_151 == 0)
{
return x_81;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_81, 0);
x_153 = lean_ctor_get(x_81, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_81);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_65);
if (x_155 == 0)
{
return x_65;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_65, 0);
x_157 = lean_ctor_get(x_65, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_65);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; lean_object* x_186; lean_object* x_187; 
x_159 = lean_ctor_get_uint8(x_19, sizeof(void*)*7 + 9);
x_160 = lean_ctor_get_uint8(x_19, sizeof(void*)*7 + 10);
x_161 = lean_ctor_get_uint8(x_42, 0);
x_162 = lean_ctor_get_uint8(x_42, 1);
x_163 = lean_ctor_get_uint8(x_42, 2);
x_164 = lean_ctor_get_uint8(x_42, 3);
x_165 = lean_ctor_get_uint8(x_42, 4);
x_166 = lean_ctor_get_uint8(x_42, 5);
x_167 = lean_ctor_get_uint8(x_42, 6);
x_168 = lean_ctor_get_uint8(x_42, 7);
x_169 = lean_ctor_get_uint8(x_42, 8);
x_170 = lean_ctor_get_uint8(x_42, 10);
x_171 = lean_ctor_get_uint8(x_42, 11);
x_172 = lean_ctor_get_uint8(x_42, 12);
x_173 = lean_ctor_get_uint8(x_42, 13);
x_174 = lean_ctor_get_uint8(x_42, 14);
x_175 = lean_ctor_get_uint8(x_42, 15);
x_176 = lean_ctor_get_uint8(x_42, 16);
x_177 = lean_ctor_get_uint8(x_42, 17);
lean_dec(x_42);
x_178 = lean_box(1);
x_179 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_179, 0, x_161);
lean_ctor_set_uint8(x_179, 1, x_162);
lean_ctor_set_uint8(x_179, 2, x_163);
lean_ctor_set_uint8(x_179, 3, x_164);
lean_ctor_set_uint8(x_179, 4, x_165);
lean_ctor_set_uint8(x_179, 5, x_166);
lean_ctor_set_uint8(x_179, 6, x_167);
lean_ctor_set_uint8(x_179, 7, x_168);
lean_ctor_set_uint8(x_179, 8, x_169);
x_180 = lean_unbox(x_178);
lean_ctor_set_uint8(x_179, 9, x_180);
lean_ctor_set_uint8(x_179, 10, x_170);
lean_ctor_set_uint8(x_179, 11, x_171);
lean_ctor_set_uint8(x_179, 12, x_172);
lean_ctor_set_uint8(x_179, 13, x_173);
lean_ctor_set_uint8(x_179, 14, x_174);
lean_ctor_set_uint8(x_179, 15, x_175);
lean_ctor_set_uint8(x_179, 16, x_176);
lean_ctor_set_uint8(x_179, 17, x_177);
x_181 = 2;
x_182 = lean_uint64_shift_right(x_46, x_181);
x_183 = lean_uint64_shift_left(x_182, x_181);
x_184 = l_Lean_Meta_injectionCore___lam__0___closed__10;
x_185 = lean_uint64_lor(x_183, x_184);
x_186 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_186, 0, x_179);
lean_ctor_set(x_186, 1, x_48);
lean_ctor_set(x_186, 2, x_49);
lean_ctor_set(x_186, 3, x_50);
lean_ctor_set(x_186, 4, x_51);
lean_ctor_set(x_186, 5, x_52);
lean_ctor_set(x_186, 6, x_53);
lean_ctor_set_uint64(x_186, sizeof(void*)*7, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*7 + 8, x_47);
lean_ctor_set_uint8(x_186, sizeof(void*)*7 + 9, x_159);
lean_ctor_set_uint8(x_186, sizeof(void*)*7 + 10, x_160);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_187 = l_Lean_Meta_mkNoConfusion(x_30, x_18, x_186, x_20, x_21, x_22, x_43);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_188 = lean_ctor_get(x_44, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_45, 0);
lean_inc(x_189);
lean_dec(x_45);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
x_192 = lean_ctor_get(x_44, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_194);
lean_dec(x_189);
x_195 = lean_name_eq(x_193, x_194);
lean_dec(x_194);
lean_dec(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_192);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
x_196 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_190, x_20, x_191);
lean_dec(x_20);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
else
{
lean_object* x_201; 
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_190);
x_201 = lean_infer_type(x_190, x_19, x_20, x_21, x_22, x_191);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_204 = l_Lean_Meta_whnfD(x_202, x_19, x_20, x_21, x_22, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 7)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_2);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
lean_inc(x_1);
x_208 = l_Lean_MVarId_getTag(x_1, x_19, x_20, x_21, x_22, x_206);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Expr_headBeta(x_207);
lean_inc(x_19);
x_212 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_211, x_209, x_19, x_20, x_21, x_22, x_210);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_213);
x_215 = l_Lean_Expr_app___override(x_190, x_213);
x_216 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_215, x_20, x_214);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_218 = x_216;
} else {
 lean_dec_ref(x_216);
 x_218 = lean_box(0);
}
x_219 = l_Lean_Expr_mvarId_x21(x_213);
lean_dec(x_213);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_220 = l_Lean_MVarId_tryClear(x_219, x_3, x_19, x_20, x_21, x_22, x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_Lean_Meta_getCtorNumPropFields(x_44, x_19, x_20, x_21, x_22, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = lean_nat_sub(x_192, x_224);
lean_dec(x_224);
lean_dec(x_192);
if (lean_is_scalar(x_218)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_218;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_226)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_226;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_225);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_221);
lean_dec(x_218);
lean_dec(x_192);
x_230 = lean_ctor_get(x_223, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_223, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_232 = x_223;
} else {
 lean_dec_ref(x_223);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_218);
lean_dec(x_192);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_234 = lean_ctor_get(x_220, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_220, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_236 = x_220;
} else {
 lean_dec_ref(x_220);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_207);
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_238 = lean_ctor_get(x_208, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_208, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_240 = x_208;
} else {
 lean_dec_ref(x_208);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_205);
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_44);
lean_dec(x_3);
x_242 = lean_ctor_get(x_204, 1);
lean_inc(x_242);
lean_dec(x_204);
x_243 = l_Lean_Meta_injectionCore___lam__0___closed__14;
x_244 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_243, x_19, x_20, x_21, x_22, x_242);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_245 = lean_ctor_get(x_204, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_204, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_247 = x_204;
} else {
 lean_dec_ref(x_204);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_201, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_201, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_251 = x_201;
} else {
 lean_dec_ref(x_201);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_187, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_187, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_255 = x_187;
} else {
 lean_dec_ref(x_187);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_38);
if (x_257 == 0)
{
return x_38;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_38, 0);
x_259 = lean_ctor_get(x_38, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_38);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_34);
if (x_261 == 0)
{
return x_34;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_34, 0);
x_263 = lean_ctor_get(x_34, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_34);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_29);
if (x_265 == 0)
{
return x_29;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_29, 0);
x_267 = lean_ctor_get(x_29, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_29);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injection", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_injectionCore___closed__1;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Meta_intro1Core(x_3, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_heqToEq(x_21, x_20, x_1, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_array_push(x_4, x_25);
x_2 = x_16;
x_3 = x_26;
x_4 = x_27;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_MVarId_intro(x_3, x_37, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Meta_heqToEq(x_43, x_42, x_1, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_array_push(x_4, x_47);
x_2 = x_16;
x_3 = x_48;
x_4 = x_49;
x_5 = x_38;
x_10 = x_46;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_injectionIntro_go(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_injectionIntro___closed__0;
x_11 = l_Lean_Meta_injectionIntro_go(x_4, x_2, x_1, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_injectionIntro(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_injectionCore(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Meta_injectionIntro(x_18, x_19, x_3, x_21, x_4, x_5, x_6, x_7, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_20 = l_Lean_Exception_isInterrupt(x_11);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_11);
x_13 = x_21;
goto block_19;
}
else
{
x_13 = x_20;
goto block_19;
}
block_19:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_14 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_12 = l_Lean_Meta_injection(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 2);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_array_to_list(x_22);
x_25 = l_List_appendTR___redArg(x_24, x_4);
x_26 = l_Lean_FVarIdSet_insert(x_5, x_2);
lean_inc(x_21);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go), 10, 5);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_21);
lean_closure_set(x_27, 3, x_23);
lean_closure_set(x_27, 4, x_26);
x_28 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_21, x_27, x_7, x_8, x_9, x_10, x_20);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injections", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recursion depth exceeded", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_1, x_11);
if (x_12 == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Meta_injections_go___closed__1;
x_14 = l_Lean_Meta_injections_go___closed__5;
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_13, x_3, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_28; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_1, x_20);
lean_dec(x_1);
x_22 = lean_nat_add(x_21, x_20);
x_28 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_5, x_18);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_inc(x_6);
lean_inc(x_18);
x_29 = l_Lean_FVarId_getType___redArg(x_18, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = l_Lean_Meta_matchEqHEq_x3f(x_30, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_21);
lean_dec(x_18);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_1 = x_22;
x_2 = x_19;
x_10 = x_34;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = lean_whnf(x_39, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = lean_whnf(x_40, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_56; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_5);
lean_inc(x_19);
lean_inc(x_4);
lean_inc(x_3);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go___lam__0), 11, 6);
lean_closure_set(x_47, 0, x_3);
lean_closure_set(x_47, 1, x_18);
lean_closure_set(x_47, 2, x_4);
lean_closure_set(x_47, 3, x_19);
lean_closure_set(x_47, 4, x_5);
lean_closure_set(x_47, 5, x_21);
x_56 = l_Lean_Expr_isRawNatLit(x_42);
lean_dec(x_42);
if (x_56 == 0)
{
lean_dec(x_45);
x_48 = x_56;
goto block_55;
}
else
{
uint8_t x_57; 
x_57 = l_Lean_Expr_isRawNatLit(x_45);
lean_dec(x_45);
x_48 = x_57;
goto block_55;
}
block_55:
{
if (x_48 == 0)
{
lean_object* x_49; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(x_47, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
x_52 = l_Lean_Exception_isInterrupt(x_50);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Exception_isRuntime(x_50);
lean_dec(x_50);
x_23 = x_49;
x_24 = x_51;
x_25 = x_53;
goto block_27;
}
else
{
lean_dec(x_50);
x_23 = x_49;
x_24 = x_51;
x_25 = x_52;
goto block_27;
}
}
}
else
{
lean_dec(x_47);
x_1 = x_22;
x_2 = x_19;
x_10 = x_46;
goto _start;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_42);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
return x_44;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_44, 0);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_44);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_41);
if (x_62 == 0)
{
return x_41;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_32);
if (x_66 == 0)
{
return x_32;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_32, 0);
x_68 = lean_ctor_get(x_32, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_32);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_18);
x_1 = x_22;
x_2 = x_19;
goto _start;
}
block_27:
{
if (x_25 == 0)
{
lean_dec(x_23);
x_1 = x_22;
x_2 = x_19;
x_10 = x_24;
goto _start;
}
else
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = l_Lean_LocalContext_getFVarIds(x_10);
lean_dec(x_10);
x_12 = lean_array_to_list(x_11);
x_13 = l_Lean_Meta_injections_go(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0), 9, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_4);
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_injectionCore___lam__0___closed__0 = _init_l_Lean_Meta_injectionCore___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__0);
l_Lean_Meta_injectionCore___lam__0___closed__1 = _init_l_Lean_Meta_injectionCore___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__1);
l_Lean_Meta_injectionCore___lam__0___closed__2 = _init_l_Lean_Meta_injectionCore___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__2);
l_Lean_Meta_injectionCore___lam__0___closed__3 = _init_l_Lean_Meta_injectionCore___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__3);
l_Lean_Meta_injectionCore___lam__0___closed__4 = _init_l_Lean_Meta_injectionCore___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__4);
l_Lean_Meta_injectionCore___lam__0___closed__5 = _init_l_Lean_Meta_injectionCore___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__5);
l_Lean_Meta_injectionCore___lam__0___closed__6 = _init_l_Lean_Meta_injectionCore___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__6);
l_Lean_Meta_injectionCore___lam__0___closed__7 = _init_l_Lean_Meta_injectionCore___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__7);
l_Lean_Meta_injectionCore___lam__0___closed__8 = _init_l_Lean_Meta_injectionCore___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__8);
l_Lean_Meta_injectionCore___lam__0___closed__9 = _init_l_Lean_Meta_injectionCore___lam__0___closed__9();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__9);
l_Lean_Meta_injectionCore___lam__0___closed__10 = _init_l_Lean_Meta_injectionCore___lam__0___closed__10();
l_Lean_Meta_injectionCore___lam__0___closed__11 = _init_l_Lean_Meta_injectionCore___lam__0___closed__11();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__11);
l_Lean_Meta_injectionCore___lam__0___closed__12 = _init_l_Lean_Meta_injectionCore___lam__0___closed__12();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__12);
l_Lean_Meta_injectionCore___lam__0___closed__13 = _init_l_Lean_Meta_injectionCore___lam__0___closed__13();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__13);
l_Lean_Meta_injectionCore___lam__0___closed__14 = _init_l_Lean_Meta_injectionCore___lam__0___closed__14();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__14);
l_Lean_Meta_injectionCore___lam__0___closed__15 = _init_l_Lean_Meta_injectionCore___lam__0___closed__15();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__15);
l_Lean_Meta_injectionCore___lam__0___closed__16 = _init_l_Lean_Meta_injectionCore___lam__0___closed__16();
lean_mark_persistent(l_Lean_Meta_injectionCore___lam__0___closed__16);
l_Lean_Meta_injectionCore___closed__0 = _init_l_Lean_Meta_injectionCore___closed__0();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__0);
l_Lean_Meta_injectionCore___closed__1 = _init_l_Lean_Meta_injectionCore___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__1);
l_Lean_Meta_injectionIntro___closed__0 = _init_l_Lean_Meta_injectionIntro___closed__0();
lean_mark_persistent(l_Lean_Meta_injectionIntro___closed__0);
l_Lean_Meta_injections_go___closed__0 = _init_l_Lean_Meta_injections_go___closed__0();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__0);
l_Lean_Meta_injections_go___closed__1 = _init_l_Lean_Meta_injections_go___closed__1();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__1);
l_Lean_Meta_injections_go___closed__2 = _init_l_Lean_Meta_injections_go___closed__2();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__2);
l_Lean_Meta_injections_go___closed__3 = _init_l_Lean_Meta_injections_go___closed__3();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__3);
l_Lean_Meta_injections_go___closed__4 = _init_l_Lean_Meta_injections_go___closed__4();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__4);
l_Lean_Meta_injections_go___closed__5 = _init_l_Lean_Meta_injections_go___closed__5();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
