// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Rewrite
// Imports: Init.Lean.Meta.AppBuilder Init.Lean.Meta.KAbstract Init.Lean.Meta.Check Init.Lean.Meta.Tactic.Apply
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
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__11;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__8;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__17;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__9;
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__6;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___closed__1;
lean_object* l_Lean_Meta_rewriteCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_iff_x3f___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__7;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__16;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__13;
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__3;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__14;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__15;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__10;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__12;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Expr_mvarId_x21(x_4);
lean_dec(x_4);
x_7 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Expr_mvarId_x21(x_8);
lean_dec(x_8);
x_11 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality of iff proof expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_a");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive is not type correct");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find instance of the pattern in the target expression");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern is a metavariable");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("propext");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___lambda__1___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___lambda__1___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_1);
x_10 = l_Lean_Meta_inferType(x_1, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = 0;
lean_inc(x_8);
x_15 = l_Lean_Meta_forallMetaTelescopeReducing(x_11, x_13, x_14, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_19, x_19, x_22, x_1);
x_24 = l_Lean_Expr_iff_x3f___closed__2;
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Expr_isAppOfArity___main(x_21, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_eq_x3f___closed__2;
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Expr_isAppOfArity___main(x_21, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_30 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_31 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_30, x_8, x_18);
lean_dec(x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Expr_appFn_x21(x_21);
x_33 = l_Lean_Expr_appFn_x21(x_32);
x_34 = l_Lean_Expr_appArg_x21(x_33);
lean_dec(x_33);
x_35 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
x_36 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
if (x_4 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_getAppFn___main(x_35);
x_38 = l_Lean_Expr_isMVar(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_18);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_8);
lean_inc(x_40);
x_42 = l_Lean_Meta_kabstract(x_40, x_35, x_6, x_8, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_108; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_108 = l_Lean_Expr_hasLooseBVars(x_43);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_109 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_110 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_109, x_8, x_44);
lean_dec(x_8);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_110);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
x_45 = x_44;
goto block_107;
}
block_107:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_expr_instantiate1(x_43, x_36);
lean_dec(x_36);
x_47 = l_Lean_Meta_instantiateMVars(x_46, x_8, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_8);
lean_inc_n(x_40, 2);
x_50 = l_Lean_Meta_mkEq(x_40, x_40, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Expr_appFn_x21(x_51);
lean_dec(x_51);
x_54 = l_Lean_mkApp(x_53, x_43);
x_55 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_56 = 0;
x_57 = l_Lean_mkLambda(x_55, x_56, x_34, x_54);
lean_inc(x_8);
lean_inc(x_57);
x_92 = l_Lean_Meta_isTypeCorrect(x_57, x_8, x_52);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_57);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_97 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_96, x_8, x_95);
lean_dec(x_8);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
return x_97;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_dec(x_92);
x_58 = x_102;
goto block_91;
}
block_91:
{
lean_object* x_59; 
lean_inc(x_8);
x_59 = l_Lean_Meta_mkEqRefl(x_40, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_8);
x_62 = l_Lean_Meta_mkEqNDRec(x_57, x_60, x_23, x_8, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_8);
x_65 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_64);
lean_dec(x_20);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_66);
lean_dec(x_8);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = l_Array_toList___rarg(x_69);
lean_dec(x_69);
x_71 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_70);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_67, 0, x_72);
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = l_Array_toList___rarg(x_73);
lean_dec(x_73);
x_76 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_75);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_48);
lean_ctor_set(x_77, 1, x_63);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_63);
lean_dec(x_48);
lean_dec(x_19);
lean_dec(x_8);
x_79 = !lean_is_exclusive(x_65);
if (x_79 == 0)
{
return x_65;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_65, 0);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_65);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_48);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_62);
if (x_83 == 0)
{
return x_62;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_62, 0);
x_85 = lean_ctor_get(x_62, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_62);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_57);
lean_dec(x_48);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_59);
if (x_87 == 0)
{
return x_59;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_59, 0);
x_89 = lean_ctor_get(x_59, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_59);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_50);
if (x_103 == 0)
{
return x_50;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_50, 0);
x_105 = lean_ctor_get(x_50, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_50);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_42);
if (x_115 == 0)
{
return x_42;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_42, 0);
x_117 = lean_ctor_get(x_42, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_42);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_119 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_120 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_119, x_8, x_18);
lean_dec(x_8);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_120);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; 
lean_inc(x_8);
x_125 = l_Lean_Meta_mkEqSymm(x_23, x_8, x_18);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_210; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_8);
lean_inc(x_35);
lean_inc(x_36);
x_210 = l_Lean_Meta_mkEq(x_36, x_35, x_8, x_127);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_Expr_getAppFn___main(x_36);
x_213 = l_Lean_Expr_isMVar(x_212);
lean_dec(x_212);
if (x_213 == 0)
{
x_128 = x_211;
goto block_209;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_dec(x_126);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_214 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_215 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_214, x_8, x_211);
lean_dec(x_8);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
return x_215;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_215);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_126);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_220 = !lean_is_exclusive(x_210);
if (x_220 == 0)
{
return x_210;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_210, 0);
x_222 = lean_ctor_get(x_210, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_210);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
block_209:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_8);
lean_inc(x_130);
x_132 = l_Lean_Meta_kabstract(x_130, x_36, x_6, x_8, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_198; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_198 = l_Lean_Expr_hasLooseBVars(x_133);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
x_199 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_200 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_199, x_8, x_134);
lean_dec(x_8);
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
return x_200;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_200);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
else
{
x_135 = x_134;
goto block_197;
}
block_197:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_expr_instantiate1(x_133, x_35);
lean_dec(x_35);
x_137 = l_Lean_Meta_instantiateMVars(x_136, x_8, x_135);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_8);
lean_inc_n(x_130, 2);
x_140 = l_Lean_Meta_mkEq(x_130, x_130, x_8, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Expr_appFn_x21(x_141);
lean_dec(x_141);
x_144 = l_Lean_mkApp(x_143, x_133);
x_145 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_146 = 0;
x_147 = l_Lean_mkLambda(x_145, x_146, x_34, x_144);
lean_inc(x_8);
lean_inc(x_147);
x_182 = l_Lean_Meta_isTypeCorrect(x_147, x_8, x_142);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_147);
lean_dec(x_138);
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_20);
lean_dec(x_19);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_187 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_186, x_8, x_185);
lean_dec(x_8);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
return x_187;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_187);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
else
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_182, 1);
lean_inc(x_192);
lean_dec(x_182);
x_148 = x_192;
goto block_181;
}
block_181:
{
lean_object* x_149; 
lean_inc(x_8);
x_149 = l_Lean_Meta_mkEqRefl(x_130, x_8, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_8);
x_152 = l_Lean_Meta_mkEqNDRec(x_147, x_150, x_126, x_8, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_8);
x_155 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_154);
lean_dec(x_20);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_156);
lean_dec(x_8);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = l_Array_toList___rarg(x_159);
lean_dec(x_159);
x_161 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_160);
x_162 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_162, 0, x_138);
lean_ctor_set(x_162, 1, x_153);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_157, 0, x_162);
return x_157;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 0);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_165 = l_Array_toList___rarg(x_163);
lean_dec(x_163);
x_166 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_165);
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_138);
lean_ctor_set(x_167, 1, x_153);
lean_ctor_set(x_167, 2, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_164);
return x_168;
}
}
else
{
uint8_t x_169; 
lean_dec(x_153);
lean_dec(x_138);
lean_dec(x_19);
lean_dec(x_8);
x_169 = !lean_is_exclusive(x_155);
if (x_169 == 0)
{
return x_155;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_155, 0);
x_171 = lean_ctor_get(x_155, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_155);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_138);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_173 = !lean_is_exclusive(x_152);
if (x_173 == 0)
{
return x_152;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_152, 0);
x_175 = lean_ctor_get(x_152, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_152);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_147);
lean_dec(x_138);
lean_dec(x_126);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_149);
if (x_177 == 0)
{
return x_149;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_149, 0);
x_179 = lean_ctor_get(x_149, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_149);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_193 = !lean_is_exclusive(x_140);
if (x_193 == 0)
{
return x_140;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_140, 0);
x_195 = lean_ctor_get(x_140, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_140);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_132);
if (x_205 == 0)
{
return x_132;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_132, 0);
x_207 = lean_ctor_get(x_132, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_132);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_224 = !lean_is_exclusive(x_125);
if (x_224 == 0)
{
return x_125;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_125, 0);
x_226 = lean_ctor_get(x_125, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_125);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = l_Lean_Expr_appFn_x21(x_21);
x_229 = l_Lean_Expr_appArg_x21(x_228);
lean_dec(x_228);
x_230 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_230);
lean_inc(x_229);
x_231 = l_Lean_Meta_mkEq(x_229, x_230, x_8, x_18);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = l_Lean_Meta_rewriteCore___lambda__1___closed__17;
x_235 = l_Lean_mkApp3(x_234, x_229, x_230, x_23);
x_236 = l_Lean_Expr_eq_x3f___closed__2;
x_237 = lean_unsigned_to_nat(3u);
x_238 = l_Lean_Expr_isAppOfArity___main(x_232, x_236, x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_235);
lean_dec(x_232);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_239 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_240 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_239, x_8, x_233);
lean_dec(x_8);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = l_Lean_Expr_appFn_x21(x_232);
x_242 = l_Lean_Expr_appFn_x21(x_241);
x_243 = l_Lean_Expr_appArg_x21(x_242);
lean_dec(x_242);
x_244 = l_Lean_Expr_appArg_x21(x_241);
lean_dec(x_241);
x_245 = l_Lean_Expr_appArg_x21(x_232);
lean_dec(x_232);
if (x_4 == 0)
{
lean_object* x_246; uint8_t x_247; 
x_246 = l_Lean_Expr_getAppFn___main(x_244);
x_247 = l_Lean_Expr_isMVar(x_246);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_233);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_8);
lean_inc(x_249);
x_251 = l_Lean_Meta_kabstract(x_249, x_244, x_6, x_8, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_317; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_317 = l_Lean_Expr_hasLooseBVars(x_252);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; 
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_235);
lean_dec(x_20);
lean_dec(x_19);
x_318 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_319 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_318, x_8, x_253);
lean_dec(x_8);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
return x_319;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_319, 0);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_319);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
else
{
x_254 = x_253;
goto block_316;
}
block_316:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_expr_instantiate1(x_252, x_245);
lean_dec(x_245);
x_256 = l_Lean_Meta_instantiateMVars(x_255, x_8, x_254);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_8);
lean_inc_n(x_249, 2);
x_259 = l_Lean_Meta_mkEq(x_249, x_249, x_8, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_Expr_appFn_x21(x_260);
lean_dec(x_260);
x_263 = l_Lean_mkApp(x_262, x_252);
x_264 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_265 = 0;
x_266 = l_Lean_mkLambda(x_264, x_265, x_243, x_263);
lean_inc(x_8);
lean_inc(x_266);
x_301 = l_Lean_Meta_isTypeCorrect(x_266, x_8, x_261);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_unbox(x_302);
lean_dec(x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
lean_dec(x_266);
lean_dec(x_257);
lean_dec(x_249);
lean_dec(x_235);
lean_dec(x_20);
lean_dec(x_19);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
lean_dec(x_301);
x_305 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_306 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_305, x_8, x_304);
lean_dec(x_8);
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
return x_306;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_306, 0);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_306);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
else
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_301, 1);
lean_inc(x_311);
lean_dec(x_301);
x_267 = x_311;
goto block_300;
}
block_300:
{
lean_object* x_268; 
lean_inc(x_8);
x_268 = l_Lean_Meta_mkEqRefl(x_249, x_8, x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
lean_inc(x_8);
x_271 = l_Lean_Meta_mkEqNDRec(x_266, x_269, x_235, x_8, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_8);
x_274 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_273);
lean_dec(x_20);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_276 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_275);
lean_dec(x_8);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = l_Array_toList___rarg(x_278);
lean_dec(x_278);
x_280 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_279);
x_281 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_281, 0, x_257);
lean_ctor_set(x_281, 1, x_272);
lean_ctor_set(x_281, 2, x_280);
lean_ctor_set(x_276, 0, x_281);
return x_276;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_276, 0);
x_283 = lean_ctor_get(x_276, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_276);
x_284 = l_Array_toList___rarg(x_282);
lean_dec(x_282);
x_285 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_284);
x_286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_286, 0, x_257);
lean_ctor_set(x_286, 1, x_272);
lean_ctor_set(x_286, 2, x_285);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_283);
return x_287;
}
}
else
{
uint8_t x_288; 
lean_dec(x_272);
lean_dec(x_257);
lean_dec(x_19);
lean_dec(x_8);
x_288 = !lean_is_exclusive(x_274);
if (x_288 == 0)
{
return x_274;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_274, 0);
x_290 = lean_ctor_get(x_274, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_274);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_257);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_292 = !lean_is_exclusive(x_271);
if (x_292 == 0)
{
return x_271;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_271, 0);
x_294 = lean_ctor_get(x_271, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_271);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_266);
lean_dec(x_257);
lean_dec(x_235);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_296 = !lean_is_exclusive(x_268);
if (x_296 == 0)
{
return x_268;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_268, 0);
x_298 = lean_ctor_get(x_268, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_268);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_257);
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_243);
lean_dec(x_235);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_312 = !lean_is_exclusive(x_259);
if (x_312 == 0)
{
return x_259;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_259, 0);
x_314 = lean_ctor_get(x_259, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_259);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_249);
lean_dec(x_245);
lean_dec(x_243);
lean_dec(x_235);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_324 = !lean_is_exclusive(x_251);
if (x_324 == 0)
{
return x_251;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_251, 0);
x_326 = lean_ctor_get(x_251, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_251);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_235);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_328 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_329 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_328, x_8, x_233);
lean_dec(x_8);
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
return x_329;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_329, 0);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_329);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
lean_object* x_334; 
lean_inc(x_8);
x_334 = l_Lean_Meta_mkEqSymm(x_235, x_8, x_233);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_419; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
lean_inc(x_8);
lean_inc(x_244);
lean_inc(x_245);
x_419 = l_Lean_Meta_mkEq(x_245, x_244, x_8, x_336);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = l_Lean_Expr_getAppFn___main(x_245);
x_422 = l_Lean_Expr_isMVar(x_421);
lean_dec(x_421);
if (x_422 == 0)
{
x_337 = x_420;
goto block_418;
}
else
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; 
lean_dec(x_335);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_423 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_424 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_423, x_8, x_420);
lean_dec(x_8);
x_425 = !lean_is_exclusive(x_424);
if (x_425 == 0)
{
return x_424;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_424, 0);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_424);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
else
{
uint8_t x_429; 
lean_dec(x_335);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_429 = !lean_is_exclusive(x_419);
if (x_429 == 0)
{
return x_419;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_419, 0);
x_431 = lean_ctor_get(x_419, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_419);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
block_418:
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_337);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
lean_inc(x_8);
lean_inc(x_339);
x_341 = l_Lean_Meta_kabstract(x_339, x_245, x_6, x_8, x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_407; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_407 = l_Lean_Expr_hasLooseBVars(x_342);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; 
lean_dec(x_342);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_20);
lean_dec(x_19);
x_408 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_409 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_408, x_8, x_343);
lean_dec(x_8);
x_410 = !lean_is_exclusive(x_409);
if (x_410 == 0)
{
return x_409;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_409, 0);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_409);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
else
{
x_344 = x_343;
goto block_406;
}
block_406:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_345 = lean_expr_instantiate1(x_342, x_244);
lean_dec(x_244);
x_346 = l_Lean_Meta_instantiateMVars(x_345, x_8, x_344);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_8);
lean_inc_n(x_339, 2);
x_349 = l_Lean_Meta_mkEq(x_339, x_339, x_8, x_348);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = l_Lean_Expr_appFn_x21(x_350);
lean_dec(x_350);
x_353 = l_Lean_mkApp(x_352, x_342);
x_354 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_355 = 0;
x_356 = l_Lean_mkLambda(x_354, x_355, x_243, x_353);
lean_inc(x_8);
lean_inc(x_356);
x_391 = l_Lean_Meta_isTypeCorrect(x_356, x_8, x_351);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_unbox(x_392);
lean_dec(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
lean_dec(x_356);
lean_dec(x_347);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_20);
lean_dec(x_19);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_dec(x_391);
x_395 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_396 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_395, x_8, x_394);
lean_dec(x_8);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
return x_396;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_396, 0);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_396);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
else
{
lean_object* x_401; 
x_401 = lean_ctor_get(x_391, 1);
lean_inc(x_401);
lean_dec(x_391);
x_357 = x_401;
goto block_390;
}
block_390:
{
lean_object* x_358; 
lean_inc(x_8);
x_358 = l_Lean_Meta_mkEqRefl(x_339, x_8, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_8);
x_361 = l_Lean_Meta_mkEqNDRec(x_356, x_359, x_335, x_8, x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
lean_inc(x_8);
x_364 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_363);
lean_dec(x_20);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_365);
lean_dec(x_8);
x_367 = !lean_is_exclusive(x_366);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = lean_ctor_get(x_366, 0);
x_369 = l_Array_toList___rarg(x_368);
lean_dec(x_368);
x_370 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_369);
x_371 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_371, 0, x_347);
lean_ctor_set(x_371, 1, x_362);
lean_ctor_set(x_371, 2, x_370);
lean_ctor_set(x_366, 0, x_371);
return x_366;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_372 = lean_ctor_get(x_366, 0);
x_373 = lean_ctor_get(x_366, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_366);
x_374 = l_Array_toList___rarg(x_372);
lean_dec(x_372);
x_375 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_374);
x_376 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_376, 0, x_347);
lean_ctor_set(x_376, 1, x_362);
lean_ctor_set(x_376, 2, x_375);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_373);
return x_377;
}
}
else
{
uint8_t x_378; 
lean_dec(x_362);
lean_dec(x_347);
lean_dec(x_19);
lean_dec(x_8);
x_378 = !lean_is_exclusive(x_364);
if (x_378 == 0)
{
return x_364;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_364, 0);
x_380 = lean_ctor_get(x_364, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_364);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_347);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_382 = !lean_is_exclusive(x_361);
if (x_382 == 0)
{
return x_361;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_361, 0);
x_384 = lean_ctor_get(x_361, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_361);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_356);
lean_dec(x_347);
lean_dec(x_335);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_386 = !lean_is_exclusive(x_358);
if (x_386 == 0)
{
return x_358;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_358, 0);
x_388 = lean_ctor_get(x_358, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_358);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
}
else
{
uint8_t x_402; 
lean_dec(x_347);
lean_dec(x_342);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_243);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_402 = !lean_is_exclusive(x_349);
if (x_402 == 0)
{
return x_349;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_349, 0);
x_404 = lean_ctor_get(x_349, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_349);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_414 = !lean_is_exclusive(x_341);
if (x_414 == 0)
{
return x_341;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_341, 0);
x_416 = lean_ctor_get(x_341, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_341);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_433 = !lean_is_exclusive(x_334);
if (x_433 == 0)
{
return x_334;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_334, 0);
x_435 = lean_ctor_get(x_334, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_334);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_437 = !lean_is_exclusive(x_231);
if (x_437 == 0)
{
return x_231;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_231, 0);
x_439 = lean_ctor_get(x_231, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_231);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
}
else
{
uint8_t x_441; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_441 = !lean_is_exclusive(x_15);
if (x_441 == 0)
{
return x_15;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_15, 0);
x_443 = lean_ctor_get(x_15, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_15);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
return x_444;
}
}
}
else
{
uint8_t x_445; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_445 = !lean_is_exclusive(x_10);
if (x_445 == 0)
{
return x_10;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_10, 0);
x_447 = lean_ctor_get(x_10, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_10);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rewrite");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_rewriteCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_rewriteCore___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_box(x_4);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_rewriteCore___lambda__1___boxed), 9, 6);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_2);
lean_closure_set(x_11, 5, x_5);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 4);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_withLocalContext___rarg(x_16, x_17, x_12, x_6, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_rewriteCore___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Lean_Meta_rewriteCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_rewriteCore(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_6);
return x_9;
}
}
lean_object* initialize_Init_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Init_Lean_Meta_KAbstract(lean_object*);
lean_object* initialize_Init_Lean_Meta_Check(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Apply(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Rewrite(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_KAbstract(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Apply(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_rewriteCore___lambda__1___closed__1 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__1);
l_Lean_Meta_rewriteCore___lambda__1___closed__2 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__2);
l_Lean_Meta_rewriteCore___lambda__1___closed__3 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__3);
l_Lean_Meta_rewriteCore___lambda__1___closed__4 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__4);
l_Lean_Meta_rewriteCore___lambda__1___closed__5 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__5);
l_Lean_Meta_rewriteCore___lambda__1___closed__6 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__6);
l_Lean_Meta_rewriteCore___lambda__1___closed__7 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__7);
l_Lean_Meta_rewriteCore___lambda__1___closed__8 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__8);
l_Lean_Meta_rewriteCore___lambda__1___closed__9 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__9);
l_Lean_Meta_rewriteCore___lambda__1___closed__10 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__10);
l_Lean_Meta_rewriteCore___lambda__1___closed__11 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__11);
l_Lean_Meta_rewriteCore___lambda__1___closed__12 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__12);
l_Lean_Meta_rewriteCore___lambda__1___closed__13 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__13);
l_Lean_Meta_rewriteCore___lambda__1___closed__14 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__14);
l_Lean_Meta_rewriteCore___lambda__1___closed__15 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__15);
l_Lean_Meta_rewriteCore___lambda__1___closed__16 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__16);
l_Lean_Meta_rewriteCore___lambda__1___closed__17 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__17);
l_Lean_Meta_rewriteCore___closed__1 = _init_l_Lean_Meta_rewriteCore___closed__1();
lean_mark_persistent(l_Lean_Meta_rewriteCore___closed__1);
l_Lean_Meta_rewriteCore___closed__2 = _init_l_Lean_Meta_rewriteCore___closed__2();
lean_mark_persistent(l_Lean_Meta_rewriteCore___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
