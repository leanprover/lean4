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
lean_object* l_Lean_Meta_injectionCore___closed__1;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__6;
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkNoConfusion___closed__3;
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_constructorApp_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__7;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__3;
lean_object* l_Lean_Meta_constructorApp_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__5;
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__1;
lean_object* l_Lean_Meta_injectionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__8;
lean_object* l_Lean_Meta_injectionCore___closed__2;
lean_object* l_Lean_Meta_constructorApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_6);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_environment_find(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_13) == 6)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_nat_dec_eq(x_7, x_17);
lean_dec(x_17);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_free_object(x_9);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; 
lean_ctor_set(x_9, 0, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
if (lean_obj_tag(x_24) == 6)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 4);
lean_inc(x_27);
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = lean_nat_dec_eq(x_7, x_28);
lean_dec(x_28);
lean_dec(x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
lean_dec(x_7);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Expr_getAppNumArgsAux___main(x_12, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
x_23 = lean_nat_sub(x_22, x_21);
lean_dec(x_22);
x_24 = l_Lean_Expr_getRevArg_x21___main(x_12, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_sub(x_20, x_25);
lean_dec(x_20);
x_27 = lean_nat_sub(x_26, x_21);
lean_dec(x_26);
x_28 = l_Lean_Expr_getRevArg_x21___main(x_12, x_27);
lean_dec(x_12);
lean_inc(x_5);
x_29 = l_Lean_Meta_whnf(x_24, x_5, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_5);
x_32 = l_Lean_Meta_whnf(x_28, x_5, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_3);
x_35 = l_Lean_Meta_getMVarType(x_3, x_5, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_constructorApp_x3f(x_30, x_5, x_37);
lean_dec(x_30);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_constructorApp_x3f(x_33, x_5, x_40);
lean_dec(x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Meta_injectionCore___lambda__1___closed__5;
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_43, x_5, x_42);
lean_dec(x_5);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_1);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Meta_injectionCore___lambda__1___closed__5;
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_47, x_5, x_46);
lean_dec(x_5);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
lean_inc(x_1);
x_52 = l_Lean_mkFVar(x_1);
lean_inc(x_5);
x_53 = l_Lean_Meta_mkNoConfusion(x_36, x_52, x_5, x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_name_eq(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_50);
lean_dec(x_2);
lean_dec(x_1);
x_61 = l_Lean_Meta_assignExprMVar(x_3, x_54, x_5, x_55);
lean_dec(x_5);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; 
lean_inc(x_5);
lean_inc(x_54);
x_72 = l_Lean_Meta_inferType(x_54, x_5, x_55);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_5);
x_75 = l_Lean_Meta_whnf(x_73, x_5, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 7)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Expr_headBeta(x_78);
lean_inc(x_3);
x_80 = l_Lean_Meta_getMVarTag(x_3, x_5, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = 2;
lean_inc(x_5);
x_84 = l_Lean_Meta_mkFreshExprMVar(x_79, x_81, x_83, x_5, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_85);
x_87 = l_Lean_mkApp(x_54, x_85);
x_88 = l_Lean_Meta_assignExprMVar(x_3, x_87, x_5, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Expr_mvarId_x21(x_85);
lean_dec(x_85);
lean_inc(x_90);
x_91 = l_Lean_Meta_tryClear(x_90, x_1, x_5, x_89);
lean_dec(x_5);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_50, 4);
lean_inc(x_94);
lean_dec(x_50);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_91, 0, x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_ctor_get(x_50, 4);
lean_inc(x_97);
lean_dec(x_50);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_90);
lean_dec(x_50);
x_100 = !lean_is_exclusive(x_91);
if (x_100 == 0)
{
return x_91;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_91, 0);
x_102 = lean_ctor_get(x_91, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_91);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_85);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_88);
if (x_104 == 0)
{
return x_88;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_88, 0);
x_106 = lean_ctor_get(x_88, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_88);
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
lean_dec(x_79);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_80);
if (x_108 == 0)
{
return x_80;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_80, 0);
x_110 = lean_ctor_get(x_80, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_80);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_76);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_1);
x_112 = lean_ctor_get(x_75, 1);
lean_inc(x_112);
lean_dec(x_75);
x_113 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_114 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_113, x_5, x_112);
lean_dec(x_5);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_75);
if (x_115 == 0)
{
return x_75;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_75, 0);
x_117 = lean_ctor_get(x_75, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_75);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_72);
if (x_119 == 0)
{
return x_72;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_72, 0);
x_121 = lean_ctor_get(x_72, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_72);
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
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_53);
if (x_123 == 0)
{
return x_53;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_53, 0);
x_125 = lean_ctor_get(x_53, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_53);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_35);
if (x_127 == 0)
{
return x_35;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_35, 0);
x_129 = lean_ctor_get(x_35, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_35);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_32);
if (x_131 == 0)
{
return x_32;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_32, 0);
x_133 = lean_ctor_get(x_32, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_32);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_29);
if (x_135 == 0)
{
return x_29;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_29, 0);
x_137 = lean_ctor_get(x_29, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_29);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_11);
if (x_139 == 0)
{
return x_11;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_11, 0);
x_141 = lean_ctor_get(x_11, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_11);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_7);
if (x_143 == 0)
{
return x_7;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_7, 0);
x_145 = lean_ctor_get(x_7, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_7);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_17);
x_18 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_4, x_16, x_17, x_3, x_5, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_drop___main___rarg(x_17, x_3);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_List_drop___main___rarg(x_17, x_3);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
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
