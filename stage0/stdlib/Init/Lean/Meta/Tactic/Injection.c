// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Injection
// Imports: Init.Lean.Meta.AppBuilder Init.Lean.Meta.Tactic.Clear Init.Lean.Meta.Tactic.Assert Init.Lean.Meta.Tactic.Intro
#include "runtime/lean.h"
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
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___closed__1;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__6;
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_WHNF_toCtorIfLit___closed__5;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkNoConfusion___closed__3;
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_WHNF_toCtorIfLit___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_constructorApp_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionIntro___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__7;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__3;
lean_object* l_Lean_Meta_constructorApp_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionIntro___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__5;
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__1;
lean_object* l_Lean_Meta_injectionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__8;
lean_object* l_Lean_Meta_injectionCore___closed__2;
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_10) == 6)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 4);
lean_inc(x_13);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_nat_dec_eq(x_2, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_free_object(x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; 
lean_ctor_set(x_6, 0, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_6);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 6)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_nat_dec_eq(x_2, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_constructorApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_WHNF_toCtorIfLit___closed__2;
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal(x_8, x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_WHNF_toCtorIfLit___closed__5;
x_12 = l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal(x_11, x_6, x_2, x_3);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_15);
x_17 = l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal(x_14, x_16, x_2, x_3);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_22);
x_24 = l___private_Init_Lean_Meta_Tactic_Injection_1__getConstructorVal(x_21, x_23, x_2, x_3);
lean_dec(x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_constructorApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_constructorApp_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality of constructor applications expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed noConfusion auxiliary construction");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Meta_getLocalDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_LocalDecl_type(x_8);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_Meta_whnf(x_10, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_eq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity___main(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_1);
x_17 = l_Lean_Meta_injectionCore___lambda__1___closed__2;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_17, x_5, x_13);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Expr_appFn_x21(x_12);
x_20 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_21 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_5);
x_22 = l_Lean_Meta_whnf(x_20, x_5, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
x_25 = l_Lean_Meta_whnf(x_21, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_3);
x_28 = l_Lean_Meta_getMVarType(x_3, x_5, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_constructorApp_x3f(x_23, x_5, x_30);
lean_dec(x_23);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_constructorApp_x3f(x_26, x_5, x_33);
lean_dec(x_26);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_injectionCore___lambda__1___closed__5;
x_37 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_36, x_5, x_35);
lean_dec(x_5);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_1);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Lean_Meta_injectionCore___lambda__1___closed__5;
x_41 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_40, x_5, x_39);
lean_dec(x_5);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
lean_dec(x_38);
lean_inc(x_1);
x_45 = l_Lean_mkFVar(x_1);
lean_inc(x_5);
x_46 = l_Lean_Meta_mkNoConfusion(x_29, x_45, x_5, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_name_eq(x_50, x_52);
lean_dec(x_52);
lean_dec(x_50);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_54 = l_Lean_Meta_assignExprMVar(x_3, x_47, x_5, x_48);
lean_dec(x_5);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_inc(x_5);
lean_inc(x_47);
x_65 = l_Lean_Meta_inferType(x_47, x_5, x_48);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_5);
x_68 = l_Lean_Meta_whnf(x_66, x_5, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 7)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_2);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Expr_headBeta(x_71);
lean_inc(x_3);
x_73 = l_Lean_Meta_getMVarTag(x_3, x_5, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = 2;
lean_inc(x_5);
x_77 = l_Lean_Meta_mkFreshExprMVar(x_72, x_74, x_76, x_5, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_78);
x_80 = l_Lean_mkApp(x_47, x_78);
x_81 = l_Lean_Meta_assignExprMVar(x_3, x_80, x_5, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_Expr_mvarId_x21(x_78);
lean_dec(x_78);
x_84 = l_Lean_Meta_tryClear(x_83, x_1, x_5, x_82);
lean_dec(x_5);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_43, 4);
lean_inc(x_87);
lean_dec(x_43);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_84, 0, x_88);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_84, 0);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_84);
x_91 = lean_ctor_get(x_43, 4);
lean_inc(x_91);
lean_dec(x_43);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_43);
x_94 = !lean_is_exclusive(x_84);
if (x_94 == 0)
{
return x_84;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_84, 0);
x_96 = lean_ctor_get(x_84, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_84);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_81);
if (x_98 == 0)
{
return x_81;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_81, 0);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_81);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_72);
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_73);
if (x_102 == 0)
{
return x_73;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_73, 0);
x_104 = lean_ctor_get(x_73, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_73);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_69);
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_1);
x_106 = lean_ctor_get(x_68, 1);
lean_inc(x_106);
lean_dec(x_68);
x_107 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_108 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_107, x_5, x_106);
lean_dec(x_5);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_68);
if (x_109 == 0)
{
return x_68;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_68, 0);
x_111 = lean_ctor_get(x_68, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_68);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_65);
if (x_113 == 0)
{
return x_65;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_65, 0);
x_115 = lean_ctor_get(x_65, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_65);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_46);
if (x_117 == 0)
{
return x_46;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_46, 0);
x_119 = lean_ctor_get(x_46, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_46);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_28);
if (x_121 == 0)
{
return x_28;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_28, 0);
x_123 = lean_ctor_get(x_28, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_28);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_25);
if (x_125 == 0)
{
return x_25;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_25, 0);
x_127 = lean_ctor_get(x_25, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_25);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_22);
if (x_129 == 0)
{
return x_22;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_22, 0);
x_131 = lean_ctor_get(x_22, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_22);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_11);
if (x_133 == 0)
{
return x_11;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_11, 0);
x_135 = lean_ctor_get(x_11, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_11);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_7);
if (x_137 == 0)
{
return x_7;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_7, 0);
x_139 = lean_ctor_get(x_7, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_7);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
lean_object* _init_l_Lean_Meta_injectionCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("injection");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_injectionCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injectionCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_injectionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Meta_injectionCore___closed__2;
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lambda__1___boxed), 6, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_1);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 4);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Meta_withLocalContext___rarg(x_12, x_13, x_8, x_3, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_injectionCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_injectionCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_injectionCore(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_LocalDecl_type(x_3);
lean_inc(x_4);
x_7 = l_Lean_Meta_whnf(x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_heq_x3f___closed__2;
x_12 = lean_unsigned_to_nat(4u);
x_13 = l_Lean_Expr_isAppOfArity___main(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_15 = l_Lean_Expr_appFn_x21(x_9);
x_16 = l_Lean_Expr_appFn_x21(x_15);
lean_dec(x_15);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_18 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_19 = l_Lean_mkFVar(x_1);
lean_inc(x_4);
x_20 = l_Lean_Meta_mkEqOfHEq(x_19, x_4, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_4);
x_23 = l_Lean_Meta_mkEq(x_17, x_18, x_4, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_userName(x_3);
x_27 = l_Lean_Meta_assert(x_2, x_26, x_24, x_21, x_4, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_clear(x_28, x_1, x_4, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 0;
x_34 = l_Lean_Meta_intro1(x_31, x_33, x_4, x_32);
lean_dec(x_4);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_4);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_20);
if (x_55 == 0)
{
return x_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_7);
x_61 = l_Lean_Expr_heq_x3f___closed__2;
x_62 = lean_unsigned_to_nat(4u);
x_63 = l_Lean_Expr_isAppOfArity___main(x_59, x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
lean_dec(x_4);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = l_Lean_Expr_appFn_x21(x_59);
x_67 = l_Lean_Expr_appFn_x21(x_66);
lean_dec(x_66);
x_68 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_69 = l_Lean_Expr_appArg_x21(x_59);
lean_dec(x_59);
lean_inc(x_1);
x_70 = l_Lean_mkFVar(x_1);
lean_inc(x_4);
x_71 = l_Lean_Meta_mkEqOfHEq(x_70, x_4, x_60);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_4);
x_74 = l_Lean_Meta_mkEq(x_68, x_69, x_4, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_LocalDecl_userName(x_3);
x_78 = l_Lean_Meta_assert(x_2, x_77, x_75, x_72, x_4, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_clear(x_79, x_1, x_4, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 0;
x_85 = l_Lean_Meta_intro1(x_82, x_84, x_4, x_83);
lean_dec(x_4);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
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
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_4);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_96 = x_81;
} else {
 lean_dec_ref(x_81);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_4);
lean_dec(x_1);
x_98 = lean_ctor_get(x_78, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_100 = x_78;
} else {
 lean_dec_ref(x_78);
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
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_72);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_74, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_74, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_104 = x_74;
} else {
 lean_dec_ref(x_74);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_71, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_71, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_108 = x_71;
} else {
 lean_dec_ref(x_71);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_7);
if (x_110 == 0)
{
return x_7;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_7, 0);
x_112 = lean_ctor_get(x_7, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_7);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_withLocalContext___rarg(x_11, x_12, x_7, x_3, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_injectionIntro___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Meta_intro1(x_2, x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq(x_16, x_15, x_5, x_14);
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
x_22 = lean_array_push(x_3, x_20);
x_1 = x_10;
x_2 = x_21;
x_3 = x_22;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_dec(x_4);
x_34 = l_Lean_Meta_intro(x_2, x_32, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l___private_Init_Lean_Meta_Tactic_Injection_2__heqToEq(x_38, x_37, x_5, x_36);
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
x_44 = lean_array_push(x_3, x_42);
x_1 = x_10;
x_2 = x_43;
x_3 = x_44;
x_4 = x_33;
x_6 = x_41;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
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
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_34);
if (x_50 == 0)
{
return x_34;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_34, 0);
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_34);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_3);
lean_ctor_set(x_54, 2, x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
}
lean_object* l_Lean_Meta_injectionIntro___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_injectionIntro___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_injectionIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_injectionIntro___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_injectionIntro(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_injection(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_injectionCore(x_1, x_2, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Array_empty___closed__1;
x_19 = l_Lean_Meta_injectionIntro___main(x_17, x_16, x_18, x_3, x_5, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_injection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_injection(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* initialize_Init_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Assert(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Intro(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Injection(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Assert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Intro(lean_io_mk_world());
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
l_Lean_Meta_injectionCore___closed__1 = _init_l_Lean_Meta_injectionCore___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__1);
l_Lean_Meta_injectionCore___closed__2 = _init_l_Lean_Meta_injectionCore___closed__2();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
