// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.KAbstract Lean.Meta.Check Lean.Meta.Tactic.Apply
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
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__11;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__8;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__17;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__9;
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__6;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___closed__1;
lean_object* l_Lean_Meta_rewriteCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_iff_x3f___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__7;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__16;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__13;
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__3;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__14;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__15;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_inferType(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_forallMetaTelescopeReducing(x_14, x_16, x_17, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_25, x_1);
x_27 = l_Lean_Expr_iff_x3f___closed__2;
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Expr_isAppOfArity___main(x_24, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_eq_x3f___closed__2;
x_31 = lean_unsigned_to_nat(3u);
x_32 = l_Lean_Expr_isAppOfArity___main(x_24, x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_33 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_34 = lean_box(0);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_33, x_34, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lean_Expr_appFn_x21(x_24);
x_37 = l_Lean_Expr_appFn_x21(x_36);
x_38 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_39 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_40 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
if (x_4 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Expr_getAppFn___main(x_39);
x_42 = l_Lean_Expr_isMVar(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_9, x_10, x_11, x_21);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_44);
x_46 = l_Lean_Meta_kabstract(x_44, x_39, x_6, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_113; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_113 = l_Lean_Expr_hasLooseBVars(x_47);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_114 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_115 = lean_box(0);
x_116 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_114, x_115, x_8, x_9, x_10, x_11, x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
return x_116;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_116);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
else
{
x_49 = x_48;
goto block_112;
}
block_112:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_expr_instantiate1(x_47, x_40);
lean_dec(x_40);
x_51 = l_Lean_Meta_instantiateMVars(x_50, x_8, x_9, x_10, x_11, x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_44, 2);
x_54 = l_Lean_Meta_mkEq(x_44, x_44, x_8, x_9, x_10, x_11, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Expr_appFn_x21(x_55);
lean_dec(x_55);
x_58 = l_Lean_mkApp(x_57, x_47);
x_59 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_60 = 0;
x_61 = l_Lean_mkLambda(x_59, x_60, x_38, x_58);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_61);
x_96 = l_Lean_Meta_isTypeCorrect(x_61, x_8, x_9, x_10, x_11, x_56);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_61);
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_101 = lean_box(0);
x_102 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_100, x_101, x_8, x_9, x_10, x_11, x_99);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_dec(x_96);
x_62 = x_107;
goto block_95;
}
block_95:
{
lean_object* x_63; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_63 = l_Lean_Meta_mkEqRefl(x_44, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_66 = l_Lean_Meta_mkEqNDRec(x_61, x_64, x_26, x_8, x_9, x_10, x_11, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_23);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = l_Array_toList___rarg(x_73);
lean_dec(x_73);
x_75 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_52);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_71, 0, x_76);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = l_Array_toList___rarg(x_77);
lean_dec(x_77);
x_80 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_79);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_52);
lean_ctor_set(x_81, 1, x_67);
lean_ctor_set(x_81, 2, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_67);
lean_dec(x_52);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_83 = !lean_is_exclusive(x_69);
if (x_83 == 0)
{
return x_69;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_69, 0);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_69);
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
lean_dec(x_52);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_66);
if (x_87 == 0)
{
return x_66;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_66, 0);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_66);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_61);
lean_dec(x_52);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_63);
if (x_91 == 0)
{
return x_63;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_63, 0);
x_93 = lean_ctor_get(x_63, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_63);
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
uint8_t x_108; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_54);
if (x_108 == 0)
{
return x_54;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_54, 0);
x_110 = lean_ctor_get(x_54, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_54);
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
uint8_t x_121; 
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_46);
if (x_121 == 0)
{
return x_46;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_46, 0);
x_123 = lean_ctor_get(x_46, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_46);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_125 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_126 = lean_box(0);
x_127 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_125, x_126, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
return x_127;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_132 = l_Lean_Meta_mkEqSymm(x_26, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_219; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_39);
lean_inc(x_40);
x_219 = l_Lean_Meta_mkEq(x_40, x_39, x_8, x_9, x_10, x_11, x_134);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = l_Lean_Expr_getAppFn___main(x_40);
x_222 = l_Lean_Expr_isMVar(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
x_135 = x_220;
goto block_218;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_dec(x_133);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_223 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_224 = lean_box(0);
x_225 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_223, x_224, x_8, x_9, x_10, x_11, x_220);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
return x_225;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_225);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_133);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_230 = !lean_is_exclusive(x_219);
if (x_230 == 0)
{
return x_219;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_219, 0);
x_232 = lean_ctor_get(x_219, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_219);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
block_218:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_9, x_10, x_11, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_137);
x_139 = l_Lean_Meta_kabstract(x_137, x_40, x_6, x_8, x_9, x_10, x_11, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_206; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_206 = l_Lean_Expr_hasLooseBVars(x_140);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_133);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
x_207 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_208 = lean_box(0);
x_209 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_207, x_208, x_8, x_9, x_10, x_11, x_141);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
return x_209;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_209);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
x_142 = x_141;
goto block_205;
}
block_205:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_expr_instantiate1(x_140, x_39);
lean_dec(x_39);
x_144 = l_Lean_Meta_instantiateMVars(x_143, x_8, x_9, x_10, x_11, x_142);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_137, 2);
x_147 = l_Lean_Meta_mkEq(x_137, x_137, x_8, x_9, x_10, x_11, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Expr_appFn_x21(x_148);
lean_dec(x_148);
x_151 = l_Lean_mkApp(x_150, x_140);
x_152 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_153 = 0;
x_154 = l_Lean_mkLambda(x_152, x_153, x_38, x_151);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_154);
x_189 = l_Lean_Meta_isTypeCorrect(x_154, x_8, x_9, x_10, x_11, x_149);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_154);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_133);
lean_dec(x_23);
lean_dec(x_22);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_194 = lean_box(0);
x_195 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_193, x_194, x_8, x_9, x_10, x_11, x_192);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
return x_195;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_195, 0);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_195);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
else
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_189, 1);
lean_inc(x_200);
lean_dec(x_189);
x_155 = x_200;
goto block_188;
}
block_188:
{
lean_object* x_156; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_156 = l_Lean_Meta_mkEqRefl(x_137, x_8, x_9, x_10, x_11, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_159 = l_Lean_Meta_mkEqNDRec(x_154, x_157, x_133, x_8, x_9, x_10, x_11, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_162 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_161);
lean_dec(x_23);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_163);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = l_Array_toList___rarg(x_166);
lean_dec(x_166);
x_168 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_167);
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_145);
lean_ctor_set(x_169, 1, x_160);
lean_ctor_set(x_169, 2, x_168);
lean_ctor_set(x_164, 0, x_169);
return x_164;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = lean_ctor_get(x_164, 0);
x_171 = lean_ctor_get(x_164, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_164);
x_172 = l_Array_toList___rarg(x_170);
lean_dec(x_170);
x_173 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_172);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_145);
lean_ctor_set(x_174, 1, x_160);
lean_ctor_set(x_174, 2, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
return x_175;
}
}
else
{
uint8_t x_176; 
lean_dec(x_160);
lean_dec(x_145);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_176 = !lean_is_exclusive(x_162);
if (x_176 == 0)
{
return x_162;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_162, 0);
x_178 = lean_ctor_get(x_162, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_162);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_145);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_159);
if (x_180 == 0)
{
return x_159;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_159, 0);
x_182 = lean_ctor_get(x_159, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_159);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_154);
lean_dec(x_145);
lean_dec(x_133);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_156);
if (x_184 == 0)
{
return x_156;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_156, 0);
x_186 = lean_ctor_get(x_156, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_156);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_145);
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_201 = !lean_is_exclusive(x_147);
if (x_201 == 0)
{
return x_147;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_147, 0);
x_203 = lean_ctor_get(x_147, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_147);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_137);
lean_dec(x_133);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_214 = !lean_is_exclusive(x_139);
if (x_214 == 0)
{
return x_139;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_139, 0);
x_216 = lean_ctor_get(x_139, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_139);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_234 = !lean_is_exclusive(x_132);
if (x_234 == 0)
{
return x_132;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_132, 0);
x_236 = lean_ctor_get(x_132, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_132);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = l_Lean_Expr_appFn_x21(x_24);
x_239 = l_Lean_Expr_appArg_x21(x_238);
lean_dec(x_238);
x_240 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_240);
lean_inc(x_239);
x_241 = l_Lean_Meta_mkEq(x_239, x_240, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Meta_rewriteCore___lambda__1___closed__17;
x_245 = l_Lean_mkApp3(x_244, x_239, x_240, x_26);
x_246 = l_Lean_Expr_eq_x3f___closed__2;
x_247 = lean_unsigned_to_nat(3u);
x_248 = l_Lean_Expr_isAppOfArity___main(x_242, x_246, x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_245);
lean_dec(x_242);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_249 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_250 = lean_box(0);
x_251 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_249, x_250, x_8, x_9, x_10, x_11, x_243);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = l_Lean_Expr_appFn_x21(x_242);
x_253 = l_Lean_Expr_appFn_x21(x_252);
x_254 = l_Lean_Expr_appArg_x21(x_253);
lean_dec(x_253);
x_255 = l_Lean_Expr_appArg_x21(x_252);
lean_dec(x_252);
x_256 = l_Lean_Expr_appArg_x21(x_242);
lean_dec(x_242);
if (x_4 == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = l_Lean_Expr_getAppFn___main(x_255);
x_258 = l_Lean_Expr_isMVar(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_9, x_10, x_11, x_243);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_260);
x_262 = l_Lean_Meta_kabstract(x_260, x_255, x_6, x_8, x_9, x_10, x_11, x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_329; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_329 = l_Lean_Expr_hasLooseBVars(x_263);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
lean_dec(x_263);
lean_dec(x_260);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_245);
lean_dec(x_23);
lean_dec(x_22);
x_330 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_331 = lean_box(0);
x_332 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_330, x_331, x_8, x_9, x_10, x_11, x_264);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_333 = !lean_is_exclusive(x_332);
if (x_333 == 0)
{
return x_332;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_332, 0);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_332);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
else
{
x_265 = x_264;
goto block_328;
}
block_328:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_expr_instantiate1(x_263, x_256);
lean_dec(x_256);
x_267 = l_Lean_Meta_instantiateMVars(x_266, x_8, x_9, x_10, x_11, x_265);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_260, 2);
x_270 = l_Lean_Meta_mkEq(x_260, x_260, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_Lean_Expr_appFn_x21(x_271);
lean_dec(x_271);
x_274 = l_Lean_mkApp(x_273, x_263);
x_275 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_276 = 0;
x_277 = l_Lean_mkLambda(x_275, x_276, x_254, x_274);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_277);
x_312 = l_Lean_Meta_isTypeCorrect(x_277, x_8, x_9, x_10, x_11, x_272);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_unbox(x_313);
lean_dec(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
lean_dec(x_277);
lean_dec(x_268);
lean_dec(x_260);
lean_dec(x_245);
lean_dec(x_23);
lean_dec(x_22);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
lean_dec(x_312);
x_316 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_317 = lean_box(0);
x_318 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_316, x_317, x_8, x_9, x_10, x_11, x_315);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
return x_318;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_318, 0);
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_318);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
else
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_312, 1);
lean_inc(x_323);
lean_dec(x_312);
x_278 = x_323;
goto block_311;
}
block_311:
{
lean_object* x_279; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_279 = l_Lean_Meta_mkEqRefl(x_260, x_8, x_9, x_10, x_11, x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_282 = l_Lean_Meta_mkEqNDRec(x_277, x_280, x_245, x_8, x_9, x_10, x_11, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_285 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_284);
lean_dec(x_23);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_287 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_286);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_287, 0);
x_290 = l_Array_toList___rarg(x_289);
lean_dec(x_289);
x_291 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_290);
x_292 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_292, 0, x_268);
lean_ctor_set(x_292, 1, x_283);
lean_ctor_set(x_292, 2, x_291);
lean_ctor_set(x_287, 0, x_292);
return x_287;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_293 = lean_ctor_get(x_287, 0);
x_294 = lean_ctor_get(x_287, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_287);
x_295 = l_Array_toList___rarg(x_293);
lean_dec(x_293);
x_296 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_295);
x_297 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_297, 0, x_268);
lean_ctor_set(x_297, 1, x_283);
lean_ctor_set(x_297, 2, x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_294);
return x_298;
}
}
else
{
uint8_t x_299; 
lean_dec(x_283);
lean_dec(x_268);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_299 = !lean_is_exclusive(x_285);
if (x_299 == 0)
{
return x_285;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_285, 0);
x_301 = lean_ctor_get(x_285, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_285);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
else
{
uint8_t x_303; 
lean_dec(x_268);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_303 = !lean_is_exclusive(x_282);
if (x_303 == 0)
{
return x_282;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_282, 0);
x_305 = lean_ctor_get(x_282, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_282);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_277);
lean_dec(x_268);
lean_dec(x_245);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_307 = !lean_is_exclusive(x_279);
if (x_307 == 0)
{
return x_279;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_279, 0);
x_309 = lean_ctor_get(x_279, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_279);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_268);
lean_dec(x_263);
lean_dec(x_260);
lean_dec(x_254);
lean_dec(x_245);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_324 = !lean_is_exclusive(x_270);
if (x_324 == 0)
{
return x_270;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_270, 0);
x_326 = lean_ctor_get(x_270, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_270);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_260);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_245);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_337 = !lean_is_exclusive(x_262);
if (x_337 == 0)
{
return x_262;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_262, 0);
x_339 = lean_ctor_get(x_262, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_262);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_245);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_341 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_342 = lean_box(0);
x_343 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_341, x_342, x_8, x_9, x_10, x_11, x_243);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_344 = !lean_is_exclusive(x_343);
if (x_344 == 0)
{
return x_343;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_343, 0);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_343);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
else
{
lean_object* x_348; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_348 = l_Lean_Meta_mkEqSymm(x_245, x_8, x_9, x_10, x_11, x_243);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_435; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_255);
lean_inc(x_256);
x_435 = l_Lean_Meta_mkEq(x_256, x_255, x_8, x_9, x_10, x_11, x_350);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = l_Lean_Expr_getAppFn___main(x_256);
x_438 = l_Lean_Expr_isMVar(x_437);
lean_dec(x_437);
if (x_438 == 0)
{
x_351 = x_436;
goto block_434;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
lean_dec(x_349);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_439 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_440 = lean_box(0);
x_441 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_439, x_440, x_8, x_9, x_10, x_11, x_436);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_442 = !lean_is_exclusive(x_441);
if (x_442 == 0)
{
return x_441;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_441, 0);
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_441);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
else
{
uint8_t x_446; 
lean_dec(x_349);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_446 = !lean_is_exclusive(x_435);
if (x_446 == 0)
{
return x_435;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_435, 0);
x_448 = lean_ctor_get(x_435, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_435);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
block_434:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_9, x_10, x_11, x_351);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_353);
x_355 = l_Lean_Meta_kabstract(x_353, x_256, x_6, x_8, x_9, x_10, x_11, x_354);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_422; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_422 = l_Lean_Expr_hasLooseBVars(x_356);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_349);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_23);
lean_dec(x_22);
x_423 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_424 = lean_box(0);
x_425 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_423, x_424, x_8, x_9, x_10, x_11, x_357);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_426 = !lean_is_exclusive(x_425);
if (x_426 == 0)
{
return x_425;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_425, 0);
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_425);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
else
{
x_358 = x_357;
goto block_421;
}
block_421:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_359 = lean_expr_instantiate1(x_356, x_255);
lean_dec(x_255);
x_360 = l_Lean_Meta_instantiateMVars(x_359, x_8, x_9, x_10, x_11, x_358);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_353, 2);
x_363 = l_Lean_Meta_mkEq(x_353, x_353, x_8, x_9, x_10, x_11, x_362);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = l_Lean_Expr_appFn_x21(x_364);
lean_dec(x_364);
x_367 = l_Lean_mkApp(x_366, x_356);
x_368 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_369 = 0;
x_370 = l_Lean_mkLambda(x_368, x_369, x_254, x_367);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_370);
x_405 = l_Lean_Meta_isTypeCorrect(x_370, x_8, x_9, x_10, x_11, x_365);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_unbox(x_406);
lean_dec(x_406);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
lean_dec(x_370);
lean_dec(x_361);
lean_dec(x_353);
lean_dec(x_349);
lean_dec(x_23);
lean_dec(x_22);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_409 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_410 = lean_box(0);
x_411 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_409, x_410, x_8, x_9, x_10, x_11, x_408);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
return x_411;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_411, 0);
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_411);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
else
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_405, 1);
lean_inc(x_416);
lean_dec(x_405);
x_371 = x_416;
goto block_404;
}
block_404:
{
lean_object* x_372; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_372 = l_Lean_Meta_mkEqRefl(x_353, x_8, x_9, x_10, x_11, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_375 = l_Lean_Meta_mkEqNDRec(x_370, x_373, x_349, x_8, x_9, x_10, x_11, x_374);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_378 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_377);
lean_dec(x_23);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
x_380 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_379);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_381 = !lean_is_exclusive(x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_380, 0);
x_383 = l_Array_toList___rarg(x_382);
lean_dec(x_382);
x_384 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_383);
x_385 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_385, 0, x_361);
lean_ctor_set(x_385, 1, x_376);
lean_ctor_set(x_385, 2, x_384);
lean_ctor_set(x_380, 0, x_385);
return x_380;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_386 = lean_ctor_get(x_380, 0);
x_387 = lean_ctor_get(x_380, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_380);
x_388 = l_Array_toList___rarg(x_386);
lean_dec(x_386);
x_389 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_388);
x_390 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_390, 0, x_361);
lean_ctor_set(x_390, 1, x_376);
lean_ctor_set(x_390, 2, x_389);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_387);
return x_391;
}
}
else
{
uint8_t x_392; 
lean_dec(x_376);
lean_dec(x_361);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_392 = !lean_is_exclusive(x_378);
if (x_392 == 0)
{
return x_378;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_378, 0);
x_394 = lean_ctor_get(x_378, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_378);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_361);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_396 = !lean_is_exclusive(x_375);
if (x_396 == 0)
{
return x_375;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_375, 0);
x_398 = lean_ctor_get(x_375, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_375);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_370);
lean_dec(x_361);
lean_dec(x_349);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_400 = !lean_is_exclusive(x_372);
if (x_400 == 0)
{
return x_372;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_372, 0);
x_402 = lean_ctor_get(x_372, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_372);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
}
else
{
uint8_t x_417; 
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_349);
lean_dec(x_254);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_417 = !lean_is_exclusive(x_363);
if (x_417 == 0)
{
return x_363;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_363, 0);
x_419 = lean_ctor_get(x_363, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_363);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_353);
lean_dec(x_349);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_430 = !lean_is_exclusive(x_355);
if (x_430 == 0)
{
return x_355;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_355, 0);
x_432 = lean_ctor_get(x_355, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_355);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_450 = !lean_is_exclusive(x_348);
if (x_450 == 0)
{
return x_348;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_348, 0);
x_452 = lean_ctor_get(x_348, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_348);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_454 = !lean_is_exclusive(x_241);
if (x_454 == 0)
{
return x_241;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_241, 0);
x_456 = lean_ctor_get(x_241, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_241);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_458 = !lean_is_exclusive(x_18);
if (x_458 == 0)
{
return x_18;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_18, 0);
x_460 = lean_ctor_get(x_18, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_18);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
else
{
uint8_t x_462; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_462 = !lean_is_exclusive(x_13);
if (x_462 == 0)
{
return x_13;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_13, 0);
x_464 = lean_ctor_get(x_13, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_13);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
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
lean_object* l_Lean_Meta_rewriteCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Meta_rewriteCore___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_box(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_rewriteCore___lambda__1___boxed), 12, 6);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_2);
lean_closure_set(x_14, 5, x_5);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 4);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_withLocalContext___rarg(x_19, x_20, x_15, x_6, x_7, x_8, x_9, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_rewriteCore___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_Meta_rewriteCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_rewriteCore(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_12;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Rewrite(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(lean_io_mk_world());
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
