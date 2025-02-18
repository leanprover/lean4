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
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__16;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at_Lean_Meta_injections_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__10;
static lean_object* l_Lean_Meta_injectionCore___closed__2;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__17;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__1;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__6;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__5;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__6;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__12;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__4;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__5;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__7;
static lean_object* l_Lean_Meta_injectionIntro___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__1;
static lean_object* l_Lean_Meta_injectionCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__15;
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static uint64_t l_Lean_Meta_injectionCore___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__9;
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__4;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__14;
static lean_object* l_Lean_Meta_injections_go___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_nat_dec_lt(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_nat_add(x_17, x_6);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_2, x_18);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = lean_infer_type(x_20, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l_Lean_Meta_isProp(x_22, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_4, 2);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_13 = x_27;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_5, x_32);
lean_dec(x_5);
x_34 = lean_ctor_get(x_4, 2);
x_35 = lean_nat_add(x_6, x_34);
lean_dec(x_6);
x_5 = x_33;
x_6 = x_35;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_13 = x_31;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_12, x_12, x_10, x_10, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8);
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = 0;
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getCtorNumPropFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injectionCore___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injectionCore___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality of constructor applications expected", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__11;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_injectionCore___lambda__1___closed__13() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed noConfusion auxiliary construction", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__15;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_FVarId_getDecl(x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_whnf(x_14, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Expr_fvar___override(x_3);
x_19 = l_Lean_Meta_injectionCore___lambda__1___closed__2;
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_Expr_isAppOfArity(x_16, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Expr_isAppOfArity(x_16, x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
x_25 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_25, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Expr_appFn_x21(x_16);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
lean_inc(x_1);
x_30 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Meta_isConstructorApp_x27_x3f(x_28, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Meta_isConstructorApp_x27_x3f(x_29, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_3);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_42, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 6);
lean_inc(x_55);
x_56 = !lean_is_exclusive(x_44);
if (x_56 == 0)
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_59 = 1;
lean_ctor_set_uint8(x_44, 9, x_59);
x_60 = 2;
x_61 = lean_uint64_shift_right(x_48, x_60);
x_62 = lean_uint64_shift_left(x_61, x_60);
x_63 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_64 = lean_uint64_lor(x_62, x_63);
x_65 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_65, 0, x_44);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 2, x_51);
lean_ctor_set(x_65, 3, x_52);
lean_ctor_set(x_65, 4, x_53);
lean_ctor_set(x_65, 5, x_54);
lean_ctor_set(x_65, 6, x_55);
lean_ctor_set_uint64(x_65, sizeof(void*)*7, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 8, x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 9, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 10, x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_66 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_65, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
lean_dec(x_47);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_name_eq(x_70, x_72);
lean_dec(x_72);
lean_dec(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_74 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_67, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_67);
x_81 = lean_infer_type(x_67, x_4, x_5, x_6, x_7, x_68);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_84 = l_Lean_Meta_whnfD(x_82, x_4, x_5, x_6, x_7, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 7)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Expr_headBeta(x_87);
lean_inc(x_1);
x_89 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_4);
x_92 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_88, x_90, x_4, x_5, x_6, x_7, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_93);
x_95 = l_Lean_Expr_app___override(x_67, x_93);
x_96 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_95, x_4, x_5, x_6, x_7, x_94);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 1);
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
x_100 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_101 = l_Lean_MVarId_tryClear(x_100, x_3, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_46);
x_104 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_46, 4);
lean_inc(x_107);
lean_dec(x_46);
x_108 = lean_nat_sub(x_107, x_106);
lean_dec(x_106);
lean_dec(x_107);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_108);
lean_ctor_set(x_96, 0, x_102);
lean_ctor_set(x_104, 0, x_96);
return x_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_104, 0);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_104);
x_111 = lean_ctor_get(x_46, 4);
lean_inc(x_111);
lean_dec(x_46);
x_112 = lean_nat_sub(x_111, x_109);
lean_dec(x_109);
lean_dec(x_111);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_112);
lean_ctor_set(x_96, 0, x_102);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_96);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_102);
lean_free_object(x_96);
lean_dec(x_46);
x_114 = !lean_is_exclusive(x_104);
if (x_114 == 0)
{
return x_104;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_104, 0);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_104);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_free_object(x_96);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_118 = !lean_is_exclusive(x_101);
if (x_118 == 0)
{
return x_101;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_101, 0);
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_101);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_96, 1);
lean_inc(x_122);
lean_dec(x_96);
x_123 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_124 = l_Lean_MVarId_tryClear(x_123, x_3, x_4, x_5, x_6, x_7, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_46);
x_127 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_46, 4);
lean_inc(x_131);
lean_dec(x_46);
x_132 = lean_nat_sub(x_131, x_128);
lean_dec(x_128);
lean_dec(x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_130)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_130;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
lean_dec(x_46);
x_135 = lean_ctor_get(x_127, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = lean_ctor_get(x_124, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_141 = x_124;
} else {
 lean_dec_ref(x_124);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_88);
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_89);
if (x_143 == 0)
{
return x_89;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_89, 0);
x_145 = lean_ctor_get(x_89, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_89);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_85);
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_3);
x_147 = lean_ctor_get(x_84, 1);
lean_inc(x_147);
lean_dec(x_84);
x_148 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_149 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_148, x_4, x_5, x_6, x_7, x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_84);
if (x_150 == 0)
{
return x_84;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_84, 0);
x_152 = lean_ctor_get(x_84, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_84);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_81);
if (x_154 == 0)
{
return x_81;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_81, 0);
x_156 = lean_ctor_get(x_81, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_81);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_66);
if (x_158 == 0)
{
return x_66;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_66, 0);
x_160 = lean_ctor_get(x_66, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_66);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; lean_object* x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; lean_object* x_188; lean_object* x_189; 
x_162 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_163 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_164 = lean_ctor_get_uint8(x_44, 0);
x_165 = lean_ctor_get_uint8(x_44, 1);
x_166 = lean_ctor_get_uint8(x_44, 2);
x_167 = lean_ctor_get_uint8(x_44, 3);
x_168 = lean_ctor_get_uint8(x_44, 4);
x_169 = lean_ctor_get_uint8(x_44, 5);
x_170 = lean_ctor_get_uint8(x_44, 6);
x_171 = lean_ctor_get_uint8(x_44, 7);
x_172 = lean_ctor_get_uint8(x_44, 8);
x_173 = lean_ctor_get_uint8(x_44, 10);
x_174 = lean_ctor_get_uint8(x_44, 11);
x_175 = lean_ctor_get_uint8(x_44, 12);
x_176 = lean_ctor_get_uint8(x_44, 13);
x_177 = lean_ctor_get_uint8(x_44, 14);
x_178 = lean_ctor_get_uint8(x_44, 15);
x_179 = lean_ctor_get_uint8(x_44, 16);
x_180 = lean_ctor_get_uint8(x_44, 17);
lean_dec(x_44);
x_181 = 1;
x_182 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_182, 0, x_164);
lean_ctor_set_uint8(x_182, 1, x_165);
lean_ctor_set_uint8(x_182, 2, x_166);
lean_ctor_set_uint8(x_182, 3, x_167);
lean_ctor_set_uint8(x_182, 4, x_168);
lean_ctor_set_uint8(x_182, 5, x_169);
lean_ctor_set_uint8(x_182, 6, x_170);
lean_ctor_set_uint8(x_182, 7, x_171);
lean_ctor_set_uint8(x_182, 8, x_172);
lean_ctor_set_uint8(x_182, 9, x_181);
lean_ctor_set_uint8(x_182, 10, x_173);
lean_ctor_set_uint8(x_182, 11, x_174);
lean_ctor_set_uint8(x_182, 12, x_175);
lean_ctor_set_uint8(x_182, 13, x_176);
lean_ctor_set_uint8(x_182, 14, x_177);
lean_ctor_set_uint8(x_182, 15, x_178);
lean_ctor_set_uint8(x_182, 16, x_179);
lean_ctor_set_uint8(x_182, 17, x_180);
x_183 = 2;
x_184 = lean_uint64_shift_right(x_48, x_183);
x_185 = lean_uint64_shift_left(x_184, x_183);
x_186 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_187 = lean_uint64_lor(x_185, x_186);
x_188 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_188, 0, x_182);
lean_ctor_set(x_188, 1, x_50);
lean_ctor_set(x_188, 2, x_51);
lean_ctor_set(x_188, 3, x_52);
lean_ctor_set(x_188, 4, x_53);
lean_ctor_set(x_188, 5, x_54);
lean_ctor_set(x_188, 6, x_55);
lean_ctor_set_uint64(x_188, sizeof(void*)*7, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 8, x_49);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 9, x_162);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 10, x_163);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_189 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_188, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_46, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_ctor_get(x_47, 0);
lean_inc(x_194);
lean_dec(x_47);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_name_eq(x_193, x_195);
lean_dec(x_195);
lean_dec(x_193);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_197 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_190, x_4, x_5, x_6, x_7, x_191);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
else
{
lean_object* x_202; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_190);
x_202 = lean_infer_type(x_190, x_4, x_5, x_6, x_7, x_191);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_205 = l_Lean_Meta_whnfD(x_203, x_4, x_5, x_6, x_7, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 7)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_2);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = l_Lean_Expr_headBeta(x_208);
lean_inc(x_1);
x_210 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_207);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_4);
x_213 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_209, x_211, x_4, x_5, x_6, x_7, x_212);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_214);
x_216 = l_Lean_Expr_app___override(x_190, x_214);
x_217 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_216, x_4, x_5, x_6, x_7, x_215);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
x_220 = l_Lean_Expr_mvarId_x21(x_214);
lean_dec(x_214);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_221 = l_Lean_MVarId_tryClear(x_220, x_3, x_4, x_5, x_6, x_7, x_218);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_46);
x_224 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_46, 4);
lean_inc(x_228);
lean_dec(x_46);
x_229 = lean_nat_sub(x_228, x_225);
lean_dec(x_225);
lean_dec(x_228);
if (lean_is_scalar(x_219)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_219;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_222);
lean_ctor_set(x_230, 1, x_229);
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_227;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_226);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_46);
x_232 = lean_ctor_get(x_224, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_224, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_234 = x_224;
} else {
 lean_dec_ref(x_224);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_219);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_236 = lean_ctor_get(x_221, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_221, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_238 = x_221;
} else {
 lean_dec_ref(x_221);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_209);
lean_dec(x_190);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_240 = lean_ctor_get(x_210, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_210, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_242 = x_210;
} else {
 lean_dec_ref(x_210);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_206);
lean_dec(x_190);
lean_dec(x_46);
lean_dec(x_3);
x_244 = lean_ctor_get(x_205, 1);
lean_inc(x_244);
lean_dec(x_205);
x_245 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_246 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_245, x_4, x_5, x_6, x_7, x_244);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_190);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = lean_ctor_get(x_205, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_205, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_249 = x_205;
} else {
 lean_dec_ref(x_205);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_190);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_ctor_get(x_202, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_202, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_253 = x_202;
} else {
 lean_dec_ref(x_202);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = lean_ctor_get(x_189, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_189, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_257 = x_189;
} else {
 lean_dec_ref(x_189);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_36);
if (x_259 == 0)
{
return x_36;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_36, 0);
x_261 = lean_ctor_get(x_36, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_36);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = !lean_is_exclusive(x_33);
if (x_263 == 0)
{
return x_33;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_33, 0);
x_265 = lean_ctor_get(x_33, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_33);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_30);
if (x_267 == 0)
{
return x_30;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_30, 0);
x_269 = lean_ctor_get(x_30, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_30);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_271 = l_Lean_Expr_appFn_x21(x_16);
x_272 = l_Lean_Expr_appFn_x21(x_271);
x_273 = l_Lean_Expr_appFn_x21(x_272);
x_274 = l_Lean_Expr_appArg_x21(x_273);
lean_dec(x_273);
x_275 = l_Lean_Expr_appArg_x21(x_272);
lean_dec(x_272);
x_276 = l_Lean_Expr_appArg_x21(x_271);
lean_dec(x_271);
x_277 = l_Lean_Expr_appArg_x21(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_276);
x_278 = l_Lean_Meta_isExprDefEq(x_274, x_276, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_unbox(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_275);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
lean_dec(x_278);
x_282 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_283 = lean_unsigned_to_nat(3u);
x_284 = l_Lean_Expr_isAppOfArity(x_16, x_282, x_283);
lean_dec(x_16);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_18);
lean_dec(x_3);
x_285 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_286 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_285, x_4, x_5, x_6, x_7, x_281);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_286;
}
else
{
lean_object* x_287; 
lean_inc(x_1);
x_287 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_281);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_290 = l_Lean_Meta_isConstructorApp_x27_x3f(x_276, x_4, x_5, x_6, x_7, x_289);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_293 = l_Lean_Meta_isConstructorApp_x27_x3f(x_277, x_4, x_5, x_6, x_7, x_292);
if (lean_obj_tag(x_293) == 0)
{
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_288);
lean_dec(x_18);
lean_dec(x_3);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
x_295 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_296 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_295, x_4, x_5, x_6, x_7, x_294);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_296;
}
else
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_293, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_18);
lean_dec(x_3);
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_dec(x_293);
x_299 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_300 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_299, x_4, x_5, x_6, x_7, x_298);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint64_t x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_301 = lean_ctor_get(x_4, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_293, 1);
lean_inc(x_302);
lean_dec(x_293);
x_303 = lean_ctor_get(x_291, 0);
lean_inc(x_303);
lean_dec(x_291);
x_304 = lean_ctor_get(x_297, 0);
lean_inc(x_304);
lean_dec(x_297);
x_305 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_306 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_307 = lean_ctor_get(x_4, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_4, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_4, 3);
lean_inc(x_309);
x_310 = lean_ctor_get(x_4, 4);
lean_inc(x_310);
x_311 = lean_ctor_get(x_4, 5);
lean_inc(x_311);
x_312 = lean_ctor_get(x_4, 6);
lean_inc(x_312);
x_313 = !lean_is_exclusive(x_301);
if (x_313 == 0)
{
uint8_t x_314; uint8_t x_315; uint8_t x_316; uint64_t x_317; uint64_t x_318; uint64_t x_319; uint64_t x_320; uint64_t x_321; lean_object* x_322; lean_object* x_323; 
x_314 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_315 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_316 = 1;
lean_ctor_set_uint8(x_301, 9, x_316);
x_317 = 2;
x_318 = lean_uint64_shift_right(x_305, x_317);
x_319 = lean_uint64_shift_left(x_318, x_317);
x_320 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_321 = lean_uint64_lor(x_319, x_320);
x_322 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_322, 0, x_301);
lean_ctor_set(x_322, 1, x_307);
lean_ctor_set(x_322, 2, x_308);
lean_ctor_set(x_322, 3, x_309);
lean_ctor_set(x_322, 4, x_310);
lean_ctor_set(x_322, 5, x_311);
lean_ctor_set(x_322, 6, x_312);
lean_ctor_set_uint64(x_322, sizeof(void*)*7, x_321);
lean_ctor_set_uint8(x_322, sizeof(void*)*7 + 8, x_306);
lean_ctor_set_uint8(x_322, sizeof(void*)*7 + 9, x_314);
lean_ctor_set_uint8(x_322, sizeof(void*)*7 + 10, x_315);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_323 = l_Lean_Meta_mkNoConfusion(x_288, x_18, x_322, x_5, x_6, x_7, x_302);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_303, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
lean_dec(x_326);
x_328 = lean_ctor_get(x_304, 0);
lean_inc(x_328);
lean_dec(x_304);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_name_eq(x_327, x_329);
lean_dec(x_329);
lean_dec(x_327);
if (x_330 == 0)
{
lean_object* x_331; uint8_t x_332; 
lean_dec(x_303);
lean_dec(x_3);
lean_dec(x_2);
x_331 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_324, x_4, x_5, x_6, x_7, x_325);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_332 = !lean_is_exclusive(x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_331, 0);
lean_dec(x_333);
x_334 = lean_box(0);
lean_ctor_set(x_331, 0, x_334);
return x_331;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_331, 1);
lean_inc(x_335);
lean_dec(x_331);
x_336 = lean_box(0);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
}
else
{
lean_object* x_338; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_324);
x_338 = lean_infer_type(x_324, x_4, x_5, x_6, x_7, x_325);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_341 = l_Lean_Meta_whnfD(x_339, x_4, x_5, x_6, x_7, x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 7)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_2);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = l_Lean_Expr_headBeta(x_344);
lean_inc(x_1);
x_346 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_343);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_4);
x_349 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_345, x_347, x_4, x_5, x_6, x_7, x_348);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
lean_inc(x_350);
x_352 = l_Lean_Expr_app___override(x_324, x_350);
x_353 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_352, x_4, x_5, x_6, x_7, x_351);
x_354 = !lean_is_exclusive(x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_353, 1);
x_356 = lean_ctor_get(x_353, 0);
lean_dec(x_356);
x_357 = l_Lean_Expr_mvarId_x21(x_350);
lean_dec(x_350);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_358 = l_Lean_MVarId_tryClear(x_357, x_3, x_4, x_5, x_6, x_7, x_355);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_303);
x_361 = l_Lean_Meta_getCtorNumPropFields(x_303, x_4, x_5, x_6, x_7, x_360);
if (lean_obj_tag(x_361) == 0)
{
uint8_t x_362; 
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_361, 0);
x_364 = lean_ctor_get(x_303, 4);
lean_inc(x_364);
lean_dec(x_303);
x_365 = lean_nat_sub(x_364, x_363);
lean_dec(x_363);
lean_dec(x_364);
lean_ctor_set_tag(x_353, 1);
lean_ctor_set(x_353, 1, x_365);
lean_ctor_set(x_353, 0, x_359);
lean_ctor_set(x_361, 0, x_353);
return x_361;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_361, 0);
x_367 = lean_ctor_get(x_361, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_361);
x_368 = lean_ctor_get(x_303, 4);
lean_inc(x_368);
lean_dec(x_303);
x_369 = lean_nat_sub(x_368, x_366);
lean_dec(x_366);
lean_dec(x_368);
lean_ctor_set_tag(x_353, 1);
lean_ctor_set(x_353, 1, x_369);
lean_ctor_set(x_353, 0, x_359);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_353);
lean_ctor_set(x_370, 1, x_367);
return x_370;
}
}
else
{
uint8_t x_371; 
lean_dec(x_359);
lean_free_object(x_353);
lean_dec(x_303);
x_371 = !lean_is_exclusive(x_361);
if (x_371 == 0)
{
return x_361;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_361, 0);
x_373 = lean_ctor_get(x_361, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_361);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_free_object(x_353);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_375 = !lean_is_exclusive(x_358);
if (x_375 == 0)
{
return x_358;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_358, 0);
x_377 = lean_ctor_get(x_358, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_358);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_353, 1);
lean_inc(x_379);
lean_dec(x_353);
x_380 = l_Lean_Expr_mvarId_x21(x_350);
lean_dec(x_350);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_381 = l_Lean_MVarId_tryClear(x_380, x_3, x_4, x_5, x_6, x_7, x_379);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
lean_inc(x_303);
x_384 = l_Lean_Meta_getCtorNumPropFields(x_303, x_4, x_5, x_6, x_7, x_383);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_387 = x_384;
} else {
 lean_dec_ref(x_384);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_303, 4);
lean_inc(x_388);
lean_dec(x_303);
x_389 = lean_nat_sub(x_388, x_385);
lean_dec(x_385);
lean_dec(x_388);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_382);
lean_ctor_set(x_390, 1, x_389);
if (lean_is_scalar(x_387)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_387;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_386);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_382);
lean_dec(x_303);
x_392 = lean_ctor_get(x_384, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_384, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_394 = x_384;
} else {
 lean_dec_ref(x_384);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_396 = lean_ctor_get(x_381, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_381, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_398 = x_381;
} else {
 lean_dec_ref(x_381);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_345);
lean_dec(x_324);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_400 = !lean_is_exclusive(x_346);
if (x_400 == 0)
{
return x_346;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_346, 0);
x_402 = lean_ctor_get(x_346, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_346);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_342);
lean_dec(x_324);
lean_dec(x_303);
lean_dec(x_3);
x_404 = lean_ctor_get(x_341, 1);
lean_inc(x_404);
lean_dec(x_341);
x_405 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_406 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_405, x_4, x_5, x_6, x_7, x_404);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_406;
}
}
else
{
uint8_t x_407; 
lean_dec(x_324);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_407 = !lean_is_exclusive(x_341);
if (x_407 == 0)
{
return x_341;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_341, 0);
x_409 = lean_ctor_get(x_341, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_341);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
else
{
uint8_t x_411; 
lean_dec(x_324);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_411 = !lean_is_exclusive(x_338);
if (x_411 == 0)
{
return x_338;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_338, 0);
x_413 = lean_ctor_get(x_338, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_338);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_415 = !lean_is_exclusive(x_323);
if (x_415 == 0)
{
return x_323;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_323, 0);
x_417 = lean_ctor_get(x_323, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_323);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
else
{
uint8_t x_419; uint8_t x_420; uint8_t x_421; uint8_t x_422; uint8_t x_423; uint8_t x_424; uint8_t x_425; uint8_t x_426; uint8_t x_427; uint8_t x_428; uint8_t x_429; uint8_t x_430; uint8_t x_431; uint8_t x_432; uint8_t x_433; uint8_t x_434; uint8_t x_435; uint8_t x_436; uint8_t x_437; uint8_t x_438; lean_object* x_439; uint64_t x_440; uint64_t x_441; uint64_t x_442; uint64_t x_443; uint64_t x_444; lean_object* x_445; lean_object* x_446; 
x_419 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_420 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_421 = lean_ctor_get_uint8(x_301, 0);
x_422 = lean_ctor_get_uint8(x_301, 1);
x_423 = lean_ctor_get_uint8(x_301, 2);
x_424 = lean_ctor_get_uint8(x_301, 3);
x_425 = lean_ctor_get_uint8(x_301, 4);
x_426 = lean_ctor_get_uint8(x_301, 5);
x_427 = lean_ctor_get_uint8(x_301, 6);
x_428 = lean_ctor_get_uint8(x_301, 7);
x_429 = lean_ctor_get_uint8(x_301, 8);
x_430 = lean_ctor_get_uint8(x_301, 10);
x_431 = lean_ctor_get_uint8(x_301, 11);
x_432 = lean_ctor_get_uint8(x_301, 12);
x_433 = lean_ctor_get_uint8(x_301, 13);
x_434 = lean_ctor_get_uint8(x_301, 14);
x_435 = lean_ctor_get_uint8(x_301, 15);
x_436 = lean_ctor_get_uint8(x_301, 16);
x_437 = lean_ctor_get_uint8(x_301, 17);
lean_dec(x_301);
x_438 = 1;
x_439 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_439, 0, x_421);
lean_ctor_set_uint8(x_439, 1, x_422);
lean_ctor_set_uint8(x_439, 2, x_423);
lean_ctor_set_uint8(x_439, 3, x_424);
lean_ctor_set_uint8(x_439, 4, x_425);
lean_ctor_set_uint8(x_439, 5, x_426);
lean_ctor_set_uint8(x_439, 6, x_427);
lean_ctor_set_uint8(x_439, 7, x_428);
lean_ctor_set_uint8(x_439, 8, x_429);
lean_ctor_set_uint8(x_439, 9, x_438);
lean_ctor_set_uint8(x_439, 10, x_430);
lean_ctor_set_uint8(x_439, 11, x_431);
lean_ctor_set_uint8(x_439, 12, x_432);
lean_ctor_set_uint8(x_439, 13, x_433);
lean_ctor_set_uint8(x_439, 14, x_434);
lean_ctor_set_uint8(x_439, 15, x_435);
lean_ctor_set_uint8(x_439, 16, x_436);
lean_ctor_set_uint8(x_439, 17, x_437);
x_440 = 2;
x_441 = lean_uint64_shift_right(x_305, x_440);
x_442 = lean_uint64_shift_left(x_441, x_440);
x_443 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_444 = lean_uint64_lor(x_442, x_443);
x_445 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_445, 0, x_439);
lean_ctor_set(x_445, 1, x_307);
lean_ctor_set(x_445, 2, x_308);
lean_ctor_set(x_445, 3, x_309);
lean_ctor_set(x_445, 4, x_310);
lean_ctor_set(x_445, 5, x_311);
lean_ctor_set(x_445, 6, x_312);
lean_ctor_set_uint64(x_445, sizeof(void*)*7, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*7 + 8, x_306);
lean_ctor_set_uint8(x_445, sizeof(void*)*7 + 9, x_419);
lean_ctor_set_uint8(x_445, sizeof(void*)*7 + 10, x_420);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_446 = l_Lean_Meta_mkNoConfusion(x_288, x_18, x_445, x_5, x_6, x_7, x_302);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
x_449 = lean_ctor_get(x_303, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
lean_dec(x_449);
x_451 = lean_ctor_get(x_304, 0);
lean_inc(x_451);
lean_dec(x_304);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
lean_dec(x_451);
x_453 = lean_name_eq(x_450, x_452);
lean_dec(x_452);
lean_dec(x_450);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_303);
lean_dec(x_3);
lean_dec(x_2);
x_454 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_447, x_4, x_5, x_6, x_7, x_448);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_456 = x_454;
} else {
 lean_dec_ref(x_454);
 x_456 = lean_box(0);
}
x_457 = lean_box(0);
if (lean_is_scalar(x_456)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_456;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_455);
return x_458;
}
else
{
lean_object* x_459; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_447);
x_459 = lean_infer_type(x_447, x_4, x_5, x_6, x_7, x_448);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_462 = l_Lean_Meta_whnfD(x_460, x_4, x_5, x_6, x_7, x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
if (lean_obj_tag(x_463) == 7)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_2);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = l_Lean_Expr_headBeta(x_465);
lean_inc(x_1);
x_467 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_464);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
lean_inc(x_4);
x_470 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_466, x_468, x_4, x_5, x_6, x_7, x_469);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
lean_inc(x_471);
x_473 = l_Lean_Expr_app___override(x_447, x_471);
x_474 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_473, x_4, x_5, x_6, x_7, x_472);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_476 = x_474;
} else {
 lean_dec_ref(x_474);
 x_476 = lean_box(0);
}
x_477 = l_Lean_Expr_mvarId_x21(x_471);
lean_dec(x_471);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_478 = l_Lean_MVarId_tryClear(x_477, x_3, x_4, x_5, x_6, x_7, x_475);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
lean_inc(x_303);
x_481 = l_Lean_Meta_getCtorNumPropFields(x_303, x_4, x_5, x_6, x_7, x_480);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_484 = x_481;
} else {
 lean_dec_ref(x_481);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_303, 4);
lean_inc(x_485);
lean_dec(x_303);
x_486 = lean_nat_sub(x_485, x_482);
lean_dec(x_482);
lean_dec(x_485);
if (lean_is_scalar(x_476)) {
 x_487 = lean_alloc_ctor(1, 2, 0);
} else {
 x_487 = x_476;
 lean_ctor_set_tag(x_487, 1);
}
lean_ctor_set(x_487, 0, x_479);
lean_ctor_set(x_487, 1, x_486);
if (lean_is_scalar(x_484)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_484;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_483);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_479);
lean_dec(x_476);
lean_dec(x_303);
x_489 = lean_ctor_get(x_481, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_481, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_491 = x_481;
} else {
 lean_dec_ref(x_481);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_476);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_493 = lean_ctor_get(x_478, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_478, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_495 = x_478;
} else {
 lean_dec_ref(x_478);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_466);
lean_dec(x_447);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_497 = lean_ctor_get(x_467, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_467, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_499 = x_467;
} else {
 lean_dec_ref(x_467);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_463);
lean_dec(x_447);
lean_dec(x_303);
lean_dec(x_3);
x_501 = lean_ctor_get(x_462, 1);
lean_inc(x_501);
lean_dec(x_462);
x_502 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_503 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_502, x_4, x_5, x_6, x_7, x_501);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_447);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = lean_ctor_get(x_462, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_462, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_506 = x_462;
} else {
 lean_dec_ref(x_462);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_447);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_508 = lean_ctor_get(x_459, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_459, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_510 = x_459;
} else {
 lean_dec_ref(x_459);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_512 = lean_ctor_get(x_446, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_446, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_514 = x_446;
} else {
 lean_dec_ref(x_446);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
}
}
}
else
{
uint8_t x_516; 
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_516 = !lean_is_exclusive(x_293);
if (x_516 == 0)
{
return x_293;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_293, 0);
x_518 = lean_ctor_get(x_293, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_293);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
else
{
uint8_t x_520; 
lean_dec(x_288);
lean_dec(x_277);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_520 = !lean_is_exclusive(x_290);
if (x_520 == 0)
{
return x_290;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_290, 0);
x_522 = lean_ctor_get(x_290, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_290);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
else
{
uint8_t x_524; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_524 = !lean_is_exclusive(x_287);
if (x_524 == 0)
{
return x_287;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_287, 0);
x_526 = lean_ctor_get(x_287, 1);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_287);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
return x_527;
}
}
}
}
else
{
lean_object* x_528; lean_object* x_529; 
lean_dec(x_276);
lean_dec(x_16);
x_528 = lean_ctor_get(x_278, 1);
lean_inc(x_528);
lean_dec(x_278);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_529 = l_Lean_Meta_mkEq(x_275, x_277, x_4, x_5, x_6, x_7, x_528);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_533 = l_Lean_Meta_mkEqOfHEq(x_18, x_532, x_4, x_5, x_6, x_7, x_531);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_536 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_537 = lean_unsigned_to_nat(3u);
x_538 = l_Lean_Expr_isAppOfArity(x_530, x_536, x_537);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; 
lean_dec(x_534);
lean_dec(x_530);
lean_dec(x_3);
x_539 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_540 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_539, x_4, x_5, x_6, x_7, x_535);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_541 = l_Lean_Expr_appFn_x21(x_530);
x_542 = l_Lean_Expr_appArg_x21(x_541);
lean_dec(x_541);
x_543 = l_Lean_Expr_appArg_x21(x_530);
lean_dec(x_530);
lean_inc(x_1);
x_544 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_535);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_547 = l_Lean_Meta_isConstructorApp_x27_x3f(x_542, x_4, x_5, x_6, x_7, x_546);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_550 = l_Lean_Meta_isConstructorApp_x27_x3f(x_543, x_4, x_5, x_6, x_7, x_549);
if (lean_obj_tag(x_550) == 0)
{
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_545);
lean_dec(x_534);
lean_dec(x_3);
x_551 = lean_ctor_get(x_550, 1);
lean_inc(x_551);
lean_dec(x_550);
x_552 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_553 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_552, x_4, x_5, x_6, x_7, x_551);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_553;
}
else
{
lean_object* x_554; 
x_554 = lean_ctor_get(x_550, 0);
lean_inc(x_554);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_548);
lean_dec(x_545);
lean_dec(x_534);
lean_dec(x_3);
x_555 = lean_ctor_get(x_550, 1);
lean_inc(x_555);
lean_dec(x_550);
x_556 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_557 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_556, x_4, x_5, x_6, x_7, x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_557;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint64_t x_562; uint8_t x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_558 = lean_ctor_get(x_4, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_550, 1);
lean_inc(x_559);
lean_dec(x_550);
x_560 = lean_ctor_get(x_548, 0);
lean_inc(x_560);
lean_dec(x_548);
x_561 = lean_ctor_get(x_554, 0);
lean_inc(x_561);
lean_dec(x_554);
x_562 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_563 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_564 = lean_ctor_get(x_4, 1);
lean_inc(x_564);
x_565 = lean_ctor_get(x_4, 2);
lean_inc(x_565);
x_566 = lean_ctor_get(x_4, 3);
lean_inc(x_566);
x_567 = lean_ctor_get(x_4, 4);
lean_inc(x_567);
x_568 = lean_ctor_get(x_4, 5);
lean_inc(x_568);
x_569 = lean_ctor_get(x_4, 6);
lean_inc(x_569);
x_570 = !lean_is_exclusive(x_558);
if (x_570 == 0)
{
uint8_t x_571; uint8_t x_572; uint8_t x_573; uint64_t x_574; uint64_t x_575; uint64_t x_576; uint64_t x_577; uint64_t x_578; lean_object* x_579; lean_object* x_580; 
x_571 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_572 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_573 = 1;
lean_ctor_set_uint8(x_558, 9, x_573);
x_574 = 2;
x_575 = lean_uint64_shift_right(x_562, x_574);
x_576 = lean_uint64_shift_left(x_575, x_574);
x_577 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_578 = lean_uint64_lor(x_576, x_577);
x_579 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_579, 0, x_558);
lean_ctor_set(x_579, 1, x_564);
lean_ctor_set(x_579, 2, x_565);
lean_ctor_set(x_579, 3, x_566);
lean_ctor_set(x_579, 4, x_567);
lean_ctor_set(x_579, 5, x_568);
lean_ctor_set(x_579, 6, x_569);
lean_ctor_set_uint64(x_579, sizeof(void*)*7, x_578);
lean_ctor_set_uint8(x_579, sizeof(void*)*7 + 8, x_563);
lean_ctor_set_uint8(x_579, sizeof(void*)*7 + 9, x_571);
lean_ctor_set_uint8(x_579, sizeof(void*)*7 + 10, x_572);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_580 = l_Lean_Meta_mkNoConfusion(x_545, x_534, x_579, x_5, x_6, x_7, x_559);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = lean_ctor_get(x_560, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
lean_dec(x_583);
x_585 = lean_ctor_get(x_561, 0);
lean_inc(x_585);
lean_dec(x_561);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
lean_dec(x_585);
x_587 = lean_name_eq(x_584, x_586);
lean_dec(x_586);
lean_dec(x_584);
if (x_587 == 0)
{
lean_object* x_588; uint8_t x_589; 
lean_dec(x_560);
lean_dec(x_3);
lean_dec(x_2);
x_588 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_581, x_4, x_5, x_6, x_7, x_582);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_589 = !lean_is_exclusive(x_588);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_588, 0);
lean_dec(x_590);
x_591 = lean_box(0);
lean_ctor_set(x_588, 0, x_591);
return x_588;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_588, 1);
lean_inc(x_592);
lean_dec(x_588);
x_593 = lean_box(0);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
else
{
lean_object* x_595; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_581);
x_595 = lean_infer_type(x_581, x_4, x_5, x_6, x_7, x_582);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_598 = l_Lean_Meta_whnfD(x_596, x_4, x_5, x_6, x_7, x_597);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
if (lean_obj_tag(x_599) == 7)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_2);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = l_Lean_Expr_headBeta(x_601);
lean_inc(x_1);
x_603 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_600);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
lean_inc(x_4);
x_606 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_602, x_604, x_4, x_5, x_6, x_7, x_605);
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
lean_inc(x_607);
x_609 = l_Lean_Expr_app___override(x_581, x_607);
x_610 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_609, x_4, x_5, x_6, x_7, x_608);
x_611 = !lean_is_exclusive(x_610);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_612 = lean_ctor_get(x_610, 1);
x_613 = lean_ctor_get(x_610, 0);
lean_dec(x_613);
x_614 = l_Lean_Expr_mvarId_x21(x_607);
lean_dec(x_607);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_615 = l_Lean_MVarId_tryClear(x_614, x_3, x_4, x_5, x_6, x_7, x_612);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
lean_inc(x_560);
x_618 = l_Lean_Meta_getCtorNumPropFields(x_560, x_4, x_5, x_6, x_7, x_617);
if (lean_obj_tag(x_618) == 0)
{
uint8_t x_619; 
x_619 = !lean_is_exclusive(x_618);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_618, 0);
x_621 = lean_ctor_get(x_560, 4);
lean_inc(x_621);
lean_dec(x_560);
x_622 = lean_nat_sub(x_621, x_620);
lean_dec(x_620);
lean_dec(x_621);
lean_ctor_set_tag(x_610, 1);
lean_ctor_set(x_610, 1, x_622);
lean_ctor_set(x_610, 0, x_616);
lean_ctor_set(x_618, 0, x_610);
return x_618;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_623 = lean_ctor_get(x_618, 0);
x_624 = lean_ctor_get(x_618, 1);
lean_inc(x_624);
lean_inc(x_623);
lean_dec(x_618);
x_625 = lean_ctor_get(x_560, 4);
lean_inc(x_625);
lean_dec(x_560);
x_626 = lean_nat_sub(x_625, x_623);
lean_dec(x_623);
lean_dec(x_625);
lean_ctor_set_tag(x_610, 1);
lean_ctor_set(x_610, 1, x_626);
lean_ctor_set(x_610, 0, x_616);
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_610);
lean_ctor_set(x_627, 1, x_624);
return x_627;
}
}
else
{
uint8_t x_628; 
lean_dec(x_616);
lean_free_object(x_610);
lean_dec(x_560);
x_628 = !lean_is_exclusive(x_618);
if (x_628 == 0)
{
return x_618;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_618, 0);
x_630 = lean_ctor_get(x_618, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_618);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
else
{
uint8_t x_632; 
lean_free_object(x_610);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_632 = !lean_is_exclusive(x_615);
if (x_632 == 0)
{
return x_615;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_615, 0);
x_634 = lean_ctor_get(x_615, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_615);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_610, 1);
lean_inc(x_636);
lean_dec(x_610);
x_637 = l_Lean_Expr_mvarId_x21(x_607);
lean_dec(x_607);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_638 = l_Lean_MVarId_tryClear(x_637, x_3, x_4, x_5, x_6, x_7, x_636);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
lean_inc(x_560);
x_641 = l_Lean_Meta_getCtorNumPropFields(x_560, x_4, x_5, x_6, x_7, x_640);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_644 = x_641;
} else {
 lean_dec_ref(x_641);
 x_644 = lean_box(0);
}
x_645 = lean_ctor_get(x_560, 4);
lean_inc(x_645);
lean_dec(x_560);
x_646 = lean_nat_sub(x_645, x_642);
lean_dec(x_642);
lean_dec(x_645);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_639);
lean_ctor_set(x_647, 1, x_646);
if (lean_is_scalar(x_644)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_644;
}
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_643);
return x_648;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_639);
lean_dec(x_560);
x_649 = lean_ctor_get(x_641, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_641, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_651 = x_641;
} else {
 lean_dec_ref(x_641);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_653 = lean_ctor_get(x_638, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_638, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 lean_ctor_release(x_638, 1);
 x_655 = x_638;
} else {
 lean_dec_ref(x_638);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
}
else
{
uint8_t x_657; 
lean_dec(x_602);
lean_dec(x_581);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_657 = !lean_is_exclusive(x_603);
if (x_657 == 0)
{
return x_603;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_603, 0);
x_659 = lean_ctor_get(x_603, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_603);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_599);
lean_dec(x_581);
lean_dec(x_560);
lean_dec(x_3);
x_661 = lean_ctor_get(x_598, 1);
lean_inc(x_661);
lean_dec(x_598);
x_662 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_663 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_662, x_4, x_5, x_6, x_7, x_661);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_663;
}
}
else
{
uint8_t x_664; 
lean_dec(x_581);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_664 = !lean_is_exclusive(x_598);
if (x_664 == 0)
{
return x_598;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_598, 0);
x_666 = lean_ctor_get(x_598, 1);
lean_inc(x_666);
lean_inc(x_665);
lean_dec(x_598);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_666);
return x_667;
}
}
}
else
{
uint8_t x_668; 
lean_dec(x_581);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_668 = !lean_is_exclusive(x_595);
if (x_668 == 0)
{
return x_595;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_595, 0);
x_670 = lean_ctor_get(x_595, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_595);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
return x_671;
}
}
}
}
else
{
uint8_t x_672; 
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_672 = !lean_is_exclusive(x_580);
if (x_672 == 0)
{
return x_580;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_580, 0);
x_674 = lean_ctor_get(x_580, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_580);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
else
{
uint8_t x_676; uint8_t x_677; uint8_t x_678; uint8_t x_679; uint8_t x_680; uint8_t x_681; uint8_t x_682; uint8_t x_683; uint8_t x_684; uint8_t x_685; uint8_t x_686; uint8_t x_687; uint8_t x_688; uint8_t x_689; uint8_t x_690; uint8_t x_691; uint8_t x_692; uint8_t x_693; uint8_t x_694; uint8_t x_695; lean_object* x_696; uint64_t x_697; uint64_t x_698; uint64_t x_699; uint64_t x_700; uint64_t x_701; lean_object* x_702; lean_object* x_703; 
x_676 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_677 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_678 = lean_ctor_get_uint8(x_558, 0);
x_679 = lean_ctor_get_uint8(x_558, 1);
x_680 = lean_ctor_get_uint8(x_558, 2);
x_681 = lean_ctor_get_uint8(x_558, 3);
x_682 = lean_ctor_get_uint8(x_558, 4);
x_683 = lean_ctor_get_uint8(x_558, 5);
x_684 = lean_ctor_get_uint8(x_558, 6);
x_685 = lean_ctor_get_uint8(x_558, 7);
x_686 = lean_ctor_get_uint8(x_558, 8);
x_687 = lean_ctor_get_uint8(x_558, 10);
x_688 = lean_ctor_get_uint8(x_558, 11);
x_689 = lean_ctor_get_uint8(x_558, 12);
x_690 = lean_ctor_get_uint8(x_558, 13);
x_691 = lean_ctor_get_uint8(x_558, 14);
x_692 = lean_ctor_get_uint8(x_558, 15);
x_693 = lean_ctor_get_uint8(x_558, 16);
x_694 = lean_ctor_get_uint8(x_558, 17);
lean_dec(x_558);
x_695 = 1;
x_696 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_696, 0, x_678);
lean_ctor_set_uint8(x_696, 1, x_679);
lean_ctor_set_uint8(x_696, 2, x_680);
lean_ctor_set_uint8(x_696, 3, x_681);
lean_ctor_set_uint8(x_696, 4, x_682);
lean_ctor_set_uint8(x_696, 5, x_683);
lean_ctor_set_uint8(x_696, 6, x_684);
lean_ctor_set_uint8(x_696, 7, x_685);
lean_ctor_set_uint8(x_696, 8, x_686);
lean_ctor_set_uint8(x_696, 9, x_695);
lean_ctor_set_uint8(x_696, 10, x_687);
lean_ctor_set_uint8(x_696, 11, x_688);
lean_ctor_set_uint8(x_696, 12, x_689);
lean_ctor_set_uint8(x_696, 13, x_690);
lean_ctor_set_uint8(x_696, 14, x_691);
lean_ctor_set_uint8(x_696, 15, x_692);
lean_ctor_set_uint8(x_696, 16, x_693);
lean_ctor_set_uint8(x_696, 17, x_694);
x_697 = 2;
x_698 = lean_uint64_shift_right(x_562, x_697);
x_699 = lean_uint64_shift_left(x_698, x_697);
x_700 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_701 = lean_uint64_lor(x_699, x_700);
x_702 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_702, 0, x_696);
lean_ctor_set(x_702, 1, x_564);
lean_ctor_set(x_702, 2, x_565);
lean_ctor_set(x_702, 3, x_566);
lean_ctor_set(x_702, 4, x_567);
lean_ctor_set(x_702, 5, x_568);
lean_ctor_set(x_702, 6, x_569);
lean_ctor_set_uint64(x_702, sizeof(void*)*7, x_701);
lean_ctor_set_uint8(x_702, sizeof(void*)*7 + 8, x_563);
lean_ctor_set_uint8(x_702, sizeof(void*)*7 + 9, x_676);
lean_ctor_set_uint8(x_702, sizeof(void*)*7 + 10, x_677);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_703 = l_Lean_Meta_mkNoConfusion(x_545, x_534, x_702, x_5, x_6, x_7, x_559);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; uint8_t x_710; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_706 = lean_ctor_get(x_560, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
lean_dec(x_706);
x_708 = lean_ctor_get(x_561, 0);
lean_inc(x_708);
lean_dec(x_561);
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
lean_dec(x_708);
x_710 = lean_name_eq(x_707, x_709);
lean_dec(x_709);
lean_dec(x_707);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_dec(x_560);
lean_dec(x_3);
lean_dec(x_2);
x_711 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_704, x_4, x_5, x_6, x_7, x_705);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_713 = x_711;
} else {
 lean_dec_ref(x_711);
 x_713 = lean_box(0);
}
x_714 = lean_box(0);
if (lean_is_scalar(x_713)) {
 x_715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_715 = x_713;
}
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_712);
return x_715;
}
else
{
lean_object* x_716; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_704);
x_716 = lean_infer_type(x_704, x_4, x_5, x_6, x_7, x_705);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec(x_716);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_719 = l_Lean_Meta_whnfD(x_717, x_4, x_5, x_6, x_7, x_718);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
if (lean_obj_tag(x_720) == 7)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_2);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
x_723 = l_Lean_Expr_headBeta(x_722);
lean_inc(x_1);
x_724 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_721);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
lean_inc(x_4);
x_727 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_723, x_725, x_4, x_5, x_6, x_7, x_726);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
lean_inc(x_728);
x_730 = l_Lean_Expr_app___override(x_704, x_728);
x_731 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_730, x_4, x_5, x_6, x_7, x_729);
x_732 = lean_ctor_get(x_731, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_733 = x_731;
} else {
 lean_dec_ref(x_731);
 x_733 = lean_box(0);
}
x_734 = l_Lean_Expr_mvarId_x21(x_728);
lean_dec(x_728);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_735 = l_Lean_MVarId_tryClear(x_734, x_3, x_4, x_5, x_6, x_7, x_732);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
lean_inc(x_560);
x_738 = l_Lean_Meta_getCtorNumPropFields(x_560, x_4, x_5, x_6, x_7, x_737);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_741 = x_738;
} else {
 lean_dec_ref(x_738);
 x_741 = lean_box(0);
}
x_742 = lean_ctor_get(x_560, 4);
lean_inc(x_742);
lean_dec(x_560);
x_743 = lean_nat_sub(x_742, x_739);
lean_dec(x_739);
lean_dec(x_742);
if (lean_is_scalar(x_733)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_733;
 lean_ctor_set_tag(x_744, 1);
}
lean_ctor_set(x_744, 0, x_736);
lean_ctor_set(x_744, 1, x_743);
if (lean_is_scalar(x_741)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_741;
}
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_740);
return x_745;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_736);
lean_dec(x_733);
lean_dec(x_560);
x_746 = lean_ctor_get(x_738, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_738, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_748 = x_738;
} else {
 lean_dec_ref(x_738);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_749 = x_748;
}
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_747);
return x_749;
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_733);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_750 = lean_ctor_get(x_735, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_735, 1);
lean_inc(x_751);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_752 = x_735;
} else {
 lean_dec_ref(x_735);
 x_752 = lean_box(0);
}
if (lean_is_scalar(x_752)) {
 x_753 = lean_alloc_ctor(1, 2, 0);
} else {
 x_753 = x_752;
}
lean_ctor_set(x_753, 0, x_750);
lean_ctor_set(x_753, 1, x_751);
return x_753;
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec(x_723);
lean_dec(x_704);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_754 = lean_ctor_get(x_724, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_724, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_756 = x_724;
} else {
 lean_dec_ref(x_724);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 2, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_754);
lean_ctor_set(x_757, 1, x_755);
return x_757;
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_720);
lean_dec(x_704);
lean_dec(x_560);
lean_dec(x_3);
x_758 = lean_ctor_get(x_719, 1);
lean_inc(x_758);
lean_dec(x_719);
x_759 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_760 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_759, x_4, x_5, x_6, x_7, x_758);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_760;
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_704);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_761 = lean_ctor_get(x_719, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_719, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_763 = x_719;
} else {
 lean_dec_ref(x_719);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_762);
return x_764;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_704);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_765 = lean_ctor_get(x_716, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_716, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_767 = x_716;
} else {
 lean_dec_ref(x_716);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
return x_768;
}
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_769 = lean_ctor_get(x_703, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_703, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_771 = x_703;
} else {
 lean_dec_ref(x_703);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
}
}
}
}
else
{
uint8_t x_773; 
lean_dec(x_548);
lean_dec(x_545);
lean_dec(x_534);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_773 = !lean_is_exclusive(x_550);
if (x_773 == 0)
{
return x_550;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_550, 0);
x_775 = lean_ctor_get(x_550, 1);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_550);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
return x_776;
}
}
}
else
{
uint8_t x_777; 
lean_dec(x_545);
lean_dec(x_543);
lean_dec(x_534);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_777 = !lean_is_exclusive(x_547);
if (x_777 == 0)
{
return x_547;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_547, 0);
x_779 = lean_ctor_get(x_547, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_547);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
return x_780;
}
}
}
else
{
uint8_t x_781; 
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_534);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_781 = !lean_is_exclusive(x_544);
if (x_781 == 0)
{
return x_544;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_544, 0);
x_783 = lean_ctor_get(x_544, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_544);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
}
}
}
}
else
{
uint8_t x_785; 
lean_dec(x_530);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_785 = !lean_is_exclusive(x_533);
if (x_785 == 0)
{
return x_533;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_533, 0);
x_787 = lean_ctor_get(x_533, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_533);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
else
{
uint8_t x_789; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_789 = !lean_is_exclusive(x_529);
if (x_789 == 0)
{
return x_529;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_529, 0);
x_791 = lean_ctor_get(x_529, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_529);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
return x_792;
}
}
}
}
else
{
uint8_t x_793; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_793 = !lean_is_exclusive(x_278);
if (x_793 == 0)
{
return x_278;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = lean_ctor_get(x_278, 0);
x_795 = lean_ctor_get(x_278, 1);
lean_inc(x_795);
lean_inc(x_794);
lean_dec(x_278);
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
return x_796;
}
}
}
}
else
{
uint8_t x_797; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_797 = !lean_is_exclusive(x_15);
if (x_797 == 0)
{
return x_15;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_798 = lean_ctor_get(x_15, 0);
x_799 = lean_ctor_get(x_15, 1);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_15);
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
return x_800;
}
}
}
else
{
uint8_t x_801; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_801 = !lean_is_exclusive(x_11);
if (x_801 == 0)
{
return x_11;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_11, 0);
x_803 = lean_ctor_get(x_11, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_11);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
}
}
else
{
uint8_t x_805; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_805 = !lean_is_exclusive(x_9);
if (x_805 == 0)
{
return x_9;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_ctor_get(x_9, 0);
x_807 = lean_ctor_get(x_9, 1);
lean_inc(x_807);
lean_inc(x_806);
lean_dec(x_9);
x_808 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_808, 0, x_806);
lean_ctor_set(x_808, 1, x_807);
return x_808;
}
}
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injection", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injectionCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_injectionCore___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_intro1Core(x_3, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_heqToEq(x_20, x_19, x_1, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_array_push(x_4, x_24);
x_27 = lean_box(0);
x_2 = x_14;
x_3 = x_25;
x_4 = x_26;
x_5 = x_27;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
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
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
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
x_2 = x_14;
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
lean_dec(x_14);
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
lean_dec(x_14);
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
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_10);
return x_60;
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
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_injectionIntro___closed__1;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = 1;
x_21 = l_Lean_Meta_injectionIntro(x_18, x_19, x_3, x_20, x_4, x_5, x_6, x_7, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at_Lean_Meta_injections_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Exception_isInterrupt(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Exception_isRuntime(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_10);
x_16 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_25 = l_List_appendTR___rarg(x_24, x_4);
x_26 = lean_box(0);
x_27 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_5, x_2, x_26);
lean_inc(x_21);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go), 10, 5);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_21);
lean_closure_set(x_28, 3, x_23);
lean_closure_set(x_28, 4, x_27);
x_29 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_21, x_28, x_7, x_8, x_9, x_10, x_20);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injections", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injections_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recursion depth exceeded", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__5;
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
if (x_12 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_1, x_17);
lean_dec(x_1);
x_19 = lean_nat_add(x_18, x_17);
x_20 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_5, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_inc(x_6);
lean_inc(x_15);
x_21 = l_Lean_FVarId_getType(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_matchEqHEq_x3f(x_22, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_15);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_1 = x_19;
x_2 = x_16;
x_10 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = lean_whnf(x_31, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = lean_whnf(x_32, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_56; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_56 = l_Lean_Expr_isRawNatLit(x_34);
lean_dec(x_34);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_37);
x_57 = lean_box(0);
x_39 = x_57;
goto block_55;
}
else
{
uint8_t x_58; 
x_58 = l_Lean_Expr_isRawNatLit(x_37);
lean_dec(x_37);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_39 = x_59;
goto block_55;
}
else
{
lean_dec(x_18);
lean_dec(x_15);
x_1 = x_19;
x_2 = x_16;
x_10 = x_38;
goto _start;
}
}
block_55:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_39);
lean_inc(x_5);
lean_inc(x_16);
lean_inc(x_4);
lean_inc(x_3);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go___lambda__1), 11, 6);
lean_closure_set(x_40, 0, x_3);
lean_closure_set(x_40, 1, x_15);
lean_closure_set(x_40, 2, x_4);
lean_closure_set(x_40, 3, x_16);
lean_closure_set(x_40, 4, x_5);
lean_closure_set(x_40, 5, x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_commitIfNoEx___at_Lean_Meta_injections_go___spec__1(x_40, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Exception_isInterrupt(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Exception_isRuntime(x_43);
if (x_46 == 0)
{
lean_free_object(x_41);
lean_dec(x_43);
x_1 = x_19;
x_2 = x_16;
x_10 = x_44;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
}
else
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_50 = l_Lean_Exception_isInterrupt(x_48);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Exception_isRuntime(x_48);
if (x_51 == 0)
{
lean_dec(x_48);
x_1 = x_19;
x_2 = x_16;
x_10 = x_49;
goto _start;
}
else
{
lean_object* x_53; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
return x_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_24);
if (x_69 == 0)
{
return x_24;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_24, 0);
x_71 = lean_ctor_get(x_24, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_24);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_21);
if (x_73 == 0)
{
return x_21;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_21, 0);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_21);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_15);
x_1 = x_19;
x_2 = x_16;
goto _start;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_78 = l_Lean_Meta_injections_go___closed__2;
x_79 = l_Lean_Meta_injections_go___closed__6;
x_80 = l_Lean_Meta_throwTacticEx___rarg(x_78, x_3, x_79, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_injections___lambda__1), 9, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_4);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
l_Lean_Meta_injectionCore___lambda__1___closed__1 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__1);
l_Lean_Meta_injectionCore___lambda__1___closed__2 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__2);
l_Lean_Meta_injectionCore___lambda__1___closed__3 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__3);
l_Lean_Meta_injectionCore___lambda__1___closed__4 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__4);
l_Lean_Meta_injectionCore___lambda__1___closed__5 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__5);
l_Lean_Meta_injectionCore___lambda__1___closed__6 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__6);
l_Lean_Meta_injectionCore___lambda__1___closed__7 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__7);
l_Lean_Meta_injectionCore___lambda__1___closed__8 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__8);
l_Lean_Meta_injectionCore___lambda__1___closed__9 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__9);
l_Lean_Meta_injectionCore___lambda__1___closed__10 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__10);
l_Lean_Meta_injectionCore___lambda__1___closed__11 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__11);
l_Lean_Meta_injectionCore___lambda__1___closed__12 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__12);
l_Lean_Meta_injectionCore___lambda__1___closed__13 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__13();
l_Lean_Meta_injectionCore___lambda__1___closed__14 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__14);
l_Lean_Meta_injectionCore___lambda__1___closed__15 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__15);
l_Lean_Meta_injectionCore___lambda__1___closed__16 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__16);
l_Lean_Meta_injectionCore___lambda__1___closed__17 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__17);
l_Lean_Meta_injectionCore___closed__1 = _init_l_Lean_Meta_injectionCore___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__1);
l_Lean_Meta_injectionCore___closed__2 = _init_l_Lean_Meta_injectionCore___closed__2();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__2);
l_Lean_Meta_injectionIntro___closed__1 = _init_l_Lean_Meta_injectionIntro___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionIntro___closed__1);
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
l_Lean_Meta_injections_go___closed__6 = _init_l_Lean_Meta_injections_go___closed__6();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
