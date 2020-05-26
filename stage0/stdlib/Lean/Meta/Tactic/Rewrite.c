// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Lean.Meta.AppBuilder Lean.Meta.KAbstract Lean.Meta.Check Lean.Meta.Tactic.Apply
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
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__3;
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_3);
x_11 = l_Lean_Meta_inferType(x_3, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = 0;
lean_inc(x_7);
x_16 = l_Lean_Meta_forallMetaTelescopeReducing(x_12, x_14, x_15, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_20, x_20, x_23, x_3);
x_25 = l_Lean_Expr_iff_x3f___closed__2;
x_26 = lean_unsigned_to_nat(2u);
x_27 = l_Lean_Expr_isAppOfArity___main(x_22, x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Expr_eq_x3f___closed__2;
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Expr_isAppOfArity___main(x_22, x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_31 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_32 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_31, x_7, x_19);
lean_dec(x_7);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = l_Lean_Expr_appFn_x21(x_22);
x_34 = l_Lean_Expr_appFn_x21(x_33);
x_35 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_36 = l_Lean_Expr_appArg_x21(x_33);
lean_dec(x_33);
x_37 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
if (x_4 == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_38 = l_Lean_Expr_getAppFn___main(x_36);
x_39 = l_Lean_Expr_isMVar(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_130; 
x_130 = 0;
x_40 = x_130;
goto block_129;
}
else
{
uint8_t x_131; 
x_131 = 1;
x_40 = x_131;
goto block_129;
}
block_129:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_19;
goto block_122;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_123 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_124 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_123, x_7, x_19);
lean_dec(x_7);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_124);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
block_122:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_43);
x_45 = l_Lean_Meta_kabstract(x_43, x_36, x_6, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Expr_hasLooseBVars(x_46);
x_49 = lean_expr_instantiate1(x_46, x_37);
lean_dec(x_37);
if (x_48 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_112 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_113 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_112, x_7, x_47);
lean_dec(x_7);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
return x_113;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
x_50 = x_47;
goto block_111;
}
block_111:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_Lean_Meta_instantiateMVars(x_49, x_7, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_7);
lean_inc_n(x_43, 2);
x_54 = l_Lean_Meta_mkEq(x_43, x_43, x_7, x_53);
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
x_58 = l_Lean_mkApp(x_57, x_46);
x_59 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_60 = 0;
x_61 = l_Lean_mkLambda(x_59, x_60, x_35, x_58);
lean_inc(x_7);
lean_inc(x_61);
x_96 = l_Lean_Meta_isTypeCorrect(x_61, x_7, x_56);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_61);
lean_dec(x_52);
lean_dec(x_43);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_101 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_100, x_7, x_99);
lean_dec(x_7);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_101;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_101);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
lean_dec(x_96);
x_62 = x_106;
goto block_95;
}
block_95:
{
lean_object* x_63; 
lean_inc(x_7);
x_63 = l_Lean_Meta_mkEqRefl(x_43, x_7, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_7);
x_66 = l_Lean_Meta_mkEqNDRec(x_61, x_64, x_24, x_7, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_7);
x_69 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_68);
lean_dec(x_21);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_70);
lean_dec(x_7);
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
lean_dec(x_20);
lean_dec(x_7);
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
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_107; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_54);
if (x_107 == 0)
{
return x_54;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_54, 0);
x_109 = lean_ctor_get(x_54, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_54);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_43);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_45);
if (x_118 == 0)
{
return x_45;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_45, 0);
x_120 = lean_ctor_get(x_45, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_45);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
else
{
lean_object* x_132; 
lean_inc(x_7);
x_132 = l_Lean_Meta_mkEqSymm(x_24, x_7, x_19);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_37);
x_135 = l_Lean_Meta_mkEq(x_37, x_36, x_7, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = l_Lean_Expr_getAppFn___main(x_37);
x_138 = l_Lean_Expr_isMVar(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
x_139 = x_136;
goto block_220;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_133);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_221 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_222 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_221, x_7, x_136);
lean_dec(x_7);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
return x_222;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_222);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
block_220:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_7);
lean_inc(x_141);
x_143 = l_Lean_Meta_kabstract(x_141, x_37, x_6, x_7, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Expr_hasLooseBVars(x_144);
x_147 = lean_expr_instantiate1(x_144, x_36);
lean_dec(x_36);
if (x_146 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_133);
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
x_210 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_211 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_210, x_7, x_145);
lean_dec(x_7);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
return x_211;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_211);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
else
{
x_148 = x_145;
goto block_209;
}
block_209:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = l_Lean_Meta_instantiateMVars(x_147, x_7, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_7);
lean_inc_n(x_141, 2);
x_152 = l_Lean_Meta_mkEq(x_141, x_141, x_7, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Expr_appFn_x21(x_153);
lean_dec(x_153);
x_156 = l_Lean_mkApp(x_155, x_144);
x_157 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_158 = 0;
x_159 = l_Lean_mkLambda(x_157, x_158, x_35, x_156);
lean_inc(x_7);
lean_inc(x_159);
x_194 = l_Lean_Meta_isTypeCorrect(x_159, x_7, x_154);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_141);
lean_dec(x_133);
lean_dec(x_21);
lean_dec(x_20);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_198 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_199 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_198, x_7, x_197);
lean_dec(x_7);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
return x_199;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_199);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_194, 1);
lean_inc(x_204);
lean_dec(x_194);
x_160 = x_204;
goto block_193;
}
block_193:
{
lean_object* x_161; 
lean_inc(x_7);
x_161 = l_Lean_Meta_mkEqRefl(x_141, x_7, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_7);
x_164 = l_Lean_Meta_mkEqNDRec(x_159, x_162, x_133, x_7, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_7);
x_167 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_166);
lean_dec(x_21);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_168);
lean_dec(x_7);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = l_Array_toList___rarg(x_171);
lean_dec(x_171);
x_173 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_172);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_150);
lean_ctor_set(x_174, 1, x_165);
lean_ctor_set(x_174, 2, x_173);
lean_ctor_set(x_169, 0, x_174);
return x_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_169, 0);
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_169);
x_177 = l_Array_toList___rarg(x_175);
lean_dec(x_175);
x_178 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_177);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_150);
lean_ctor_set(x_179, 1, x_165);
lean_ctor_set(x_179, 2, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_176);
return x_180;
}
}
else
{
uint8_t x_181; 
lean_dec(x_165);
lean_dec(x_150);
lean_dec(x_20);
lean_dec(x_7);
x_181 = !lean_is_exclusive(x_167);
if (x_181 == 0)
{
return x_167;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_167, 0);
x_183 = lean_ctor_get(x_167, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_167);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_150);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_164);
if (x_185 == 0)
{
return x_164;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_164, 0);
x_187 = lean_ctor_get(x_164, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_164);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_133);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_161);
if (x_189 == 0)
{
return x_161;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_161, 0);
x_191 = lean_ctor_get(x_161, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_161);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_133);
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_152);
if (x_205 == 0)
{
return x_152;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_152, 0);
x_207 = lean_ctor_get(x_152, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_152);
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
uint8_t x_216; 
lean_dec(x_141);
lean_dec(x_133);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_143);
if (x_216 == 0)
{
return x_143;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_143, 0);
x_218 = lean_ctor_get(x_143, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_143);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_133);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_135);
if (x_227 == 0)
{
return x_135;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_135, 0);
x_229 = lean_ctor_get(x_135, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_135);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_132);
if (x_231 == 0)
{
return x_132;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_132, 0);
x_233 = lean_ctor_get(x_132, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_132);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = l_Lean_Expr_appFn_x21(x_22);
x_236 = l_Lean_Expr_appArg_x21(x_235);
lean_dec(x_235);
x_237 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
lean_inc(x_7);
lean_inc(x_237);
lean_inc(x_236);
x_238 = l_Lean_Meta_mkEq(x_236, x_237, x_7, x_19);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Meta_rewriteCore___lambda__1___closed__17;
x_242 = l_Lean_mkApp3(x_241, x_236, x_237, x_24);
x_243 = l_Lean_Expr_eq_x3f___closed__2;
x_244 = lean_unsigned_to_nat(3u);
x_245 = l_Lean_Expr_isAppOfArity___main(x_239, x_243, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_246 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_247 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_246, x_7, x_240);
lean_dec(x_7);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = l_Lean_Expr_appFn_x21(x_239);
x_249 = l_Lean_Expr_appFn_x21(x_248);
x_250 = l_Lean_Expr_appArg_x21(x_249);
lean_dec(x_249);
x_251 = l_Lean_Expr_appArg_x21(x_248);
lean_dec(x_248);
x_252 = l_Lean_Expr_appArg_x21(x_239);
lean_dec(x_239);
if (x_4 == 0)
{
lean_object* x_253; uint8_t x_254; uint8_t x_255; 
x_253 = l_Lean_Expr_getAppFn___main(x_251);
x_254 = l_Lean_Expr_isMVar(x_253);
lean_dec(x_253);
if (x_254 == 0)
{
uint8_t x_345; 
x_345 = 0;
x_255 = x_345;
goto block_344;
}
else
{
uint8_t x_346; 
x_346 = 1;
x_255 = x_346;
goto block_344;
}
block_344:
{
lean_object* x_256; 
if (x_255 == 0)
{
x_256 = x_240;
goto block_337;
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_338 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_339 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_338, x_7, x_240);
lean_dec(x_7);
x_340 = !lean_is_exclusive(x_339);
if (x_340 == 0)
{
return x_339;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_339, 0);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_339);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
block_337:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_256);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
lean_inc(x_7);
lean_inc(x_258);
x_260 = l_Lean_Meta_kabstract(x_258, x_251, x_6, x_7, x_259);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = l_Lean_Expr_hasLooseBVars(x_261);
x_264 = lean_expr_instantiate1(x_261, x_252);
lean_dec(x_252);
if (x_263 == 0)
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; 
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_21);
lean_dec(x_20);
x_327 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_328 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_327, x_7, x_262);
lean_dec(x_7);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
return x_328;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_328, 0);
x_331 = lean_ctor_get(x_328, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_328);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
else
{
x_265 = x_262;
goto block_326;
}
block_326:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = l_Lean_Meta_instantiateMVars(x_264, x_7, x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
lean_inc(x_7);
lean_inc_n(x_258, 2);
x_269 = l_Lean_Meta_mkEq(x_258, x_258, x_7, x_268);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_Expr_appFn_x21(x_270);
lean_dec(x_270);
x_273 = l_Lean_mkApp(x_272, x_261);
x_274 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_275 = 0;
x_276 = l_Lean_mkLambda(x_274, x_275, x_250, x_273);
lean_inc(x_7);
lean_inc(x_276);
x_311 = l_Lean_Meta_isTypeCorrect(x_276, x_7, x_271);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_unbox(x_312);
lean_dec(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_dec(x_276);
lean_dec(x_267);
lean_dec(x_258);
lean_dec(x_242);
lean_dec(x_21);
lean_dec(x_20);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_316 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_315, x_7, x_314);
lean_dec(x_7);
x_317 = !lean_is_exclusive(x_316);
if (x_317 == 0)
{
return x_316;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_316, 0);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_316);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
else
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_311, 1);
lean_inc(x_321);
lean_dec(x_311);
x_277 = x_321;
goto block_310;
}
block_310:
{
lean_object* x_278; 
lean_inc(x_7);
x_278 = l_Lean_Meta_mkEqRefl(x_258, x_7, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
lean_inc(x_7);
x_281 = l_Lean_Meta_mkEqNDRec(x_276, x_279, x_242, x_7, x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
lean_inc(x_7);
x_284 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_283);
lean_dec(x_21);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
lean_dec(x_284);
x_286 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_285);
lean_dec(x_7);
x_287 = !lean_is_exclusive(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_286, 0);
x_289 = l_Array_toList___rarg(x_288);
lean_dec(x_288);
x_290 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_289);
x_291 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_291, 0, x_267);
lean_ctor_set(x_291, 1, x_282);
lean_ctor_set(x_291, 2, x_290);
lean_ctor_set(x_286, 0, x_291);
return x_286;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_292 = lean_ctor_get(x_286, 0);
x_293 = lean_ctor_get(x_286, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_286);
x_294 = l_Array_toList___rarg(x_292);
lean_dec(x_292);
x_295 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_294);
x_296 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_296, 0, x_267);
lean_ctor_set(x_296, 1, x_282);
lean_ctor_set(x_296, 2, x_295);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_293);
return x_297;
}
}
else
{
uint8_t x_298; 
lean_dec(x_282);
lean_dec(x_267);
lean_dec(x_20);
lean_dec(x_7);
x_298 = !lean_is_exclusive(x_284);
if (x_298 == 0)
{
return x_284;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_284, 0);
x_300 = lean_ctor_get(x_284, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_284);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_267);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_281);
if (x_302 == 0)
{
return x_281;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_281, 0);
x_304 = lean_ctor_get(x_281, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_281);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_276);
lean_dec(x_267);
lean_dec(x_242);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_278);
if (x_306 == 0)
{
return x_278;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_278, 0);
x_308 = lean_ctor_get(x_278, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_278);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_267);
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_269);
if (x_322 == 0)
{
return x_269;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_269, 0);
x_324 = lean_ctor_get(x_269, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_269);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_258);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_333 = !lean_is_exclusive(x_260);
if (x_333 == 0)
{
return x_260;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_260, 0);
x_335 = lean_ctor_get(x_260, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_260);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
}
}
else
{
lean_object* x_347; 
lean_inc(x_7);
x_347 = l_Lean_Meta_mkEqSymm(x_242, x_7, x_240);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
lean_inc(x_7);
lean_inc(x_251);
lean_inc(x_252);
x_350 = l_Lean_Meta_mkEq(x_252, x_251, x_7, x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
lean_dec(x_350);
x_352 = l_Lean_Expr_getAppFn___main(x_252);
x_353 = l_Lean_Expr_isMVar(x_352);
lean_dec(x_352);
if (x_353 == 0)
{
x_354 = x_351;
goto block_435;
}
else
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
lean_dec(x_348);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_436 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_437 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_436, x_7, x_351);
lean_dec(x_7);
x_438 = !lean_is_exclusive(x_437);
if (x_438 == 0)
{
return x_437;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_437, 0);
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_437);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
block_435:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_354);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
lean_inc(x_7);
lean_inc(x_356);
x_358 = l_Lean_Meta_kabstract(x_356, x_252, x_6, x_7, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = l_Lean_Expr_hasLooseBVars(x_359);
x_362 = lean_expr_instantiate1(x_359, x_251);
lean_dec(x_251);
if (x_361 == 0)
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_356);
lean_dec(x_348);
lean_dec(x_250);
lean_dec(x_21);
lean_dec(x_20);
x_425 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_426 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_425, x_7, x_360);
lean_dec(x_7);
x_427 = !lean_is_exclusive(x_426);
if (x_427 == 0)
{
return x_426;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_426, 0);
x_429 = lean_ctor_get(x_426, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_426);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
else
{
x_363 = x_360;
goto block_424;
}
block_424:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = l_Lean_Meta_instantiateMVars(x_362, x_7, x_363);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
lean_inc(x_7);
lean_inc_n(x_356, 2);
x_367 = l_Lean_Meta_mkEq(x_356, x_356, x_7, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_409; lean_object* x_410; uint8_t x_411; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l_Lean_Expr_appFn_x21(x_368);
lean_dec(x_368);
x_371 = l_Lean_mkApp(x_370, x_359);
x_372 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_373 = 0;
x_374 = l_Lean_mkLambda(x_372, x_373, x_250, x_371);
lean_inc(x_7);
lean_inc(x_374);
x_409 = l_Lean_Meta_isTypeCorrect(x_374, x_7, x_369);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_unbox(x_410);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
lean_dec(x_374);
lean_dec(x_365);
lean_dec(x_356);
lean_dec(x_348);
lean_dec(x_21);
lean_dec(x_20);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec(x_409);
x_413 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_414 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_413, x_7, x_412);
lean_dec(x_7);
x_415 = !lean_is_exclusive(x_414);
if (x_415 == 0)
{
return x_414;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_414, 0);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_414);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
else
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_409, 1);
lean_inc(x_419);
lean_dec(x_409);
x_375 = x_419;
goto block_408;
}
block_408:
{
lean_object* x_376; 
lean_inc(x_7);
x_376 = l_Lean_Meta_mkEqRefl(x_356, x_7, x_375);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
lean_inc(x_7);
x_379 = l_Lean_Meta_mkEqNDRec(x_374, x_377, x_348, x_7, x_378);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
lean_inc(x_7);
x_382 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_381);
lean_dec(x_21);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_383);
lean_dec(x_7);
x_385 = !lean_is_exclusive(x_384);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_386 = lean_ctor_get(x_384, 0);
x_387 = l_Array_toList___rarg(x_386);
lean_dec(x_386);
x_388 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_387);
x_389 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_389, 0, x_365);
lean_ctor_set(x_389, 1, x_380);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_384, 0, x_389);
return x_384;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_390 = lean_ctor_get(x_384, 0);
x_391 = lean_ctor_get(x_384, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_384);
x_392 = l_Array_toList___rarg(x_390);
lean_dec(x_390);
x_393 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_392);
x_394 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_394, 0, x_365);
lean_ctor_set(x_394, 1, x_380);
lean_ctor_set(x_394, 2, x_393);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_391);
return x_395;
}
}
else
{
uint8_t x_396; 
lean_dec(x_380);
lean_dec(x_365);
lean_dec(x_20);
lean_dec(x_7);
x_396 = !lean_is_exclusive(x_382);
if (x_396 == 0)
{
return x_382;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_382, 0);
x_398 = lean_ctor_get(x_382, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_382);
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
lean_dec(x_365);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_400 = !lean_is_exclusive(x_379);
if (x_400 == 0)
{
return x_379;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_379, 0);
x_402 = lean_ctor_get(x_379, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_379);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
else
{
uint8_t x_404; 
lean_dec(x_374);
lean_dec(x_365);
lean_dec(x_348);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_404 = !lean_is_exclusive(x_376);
if (x_404 == 0)
{
return x_376;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_376, 0);
x_406 = lean_ctor_get(x_376, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_376);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
}
else
{
uint8_t x_420; 
lean_dec(x_365);
lean_dec(x_359);
lean_dec(x_356);
lean_dec(x_348);
lean_dec(x_250);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_420 = !lean_is_exclusive(x_367);
if (x_420 == 0)
{
return x_367;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_367, 0);
x_422 = lean_ctor_get(x_367, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_367);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
}
else
{
uint8_t x_431; 
lean_dec(x_356);
lean_dec(x_348);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_431 = !lean_is_exclusive(x_358);
if (x_431 == 0)
{
return x_358;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_358, 0);
x_433 = lean_ctor_get(x_358, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_358);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
}
else
{
uint8_t x_442; 
lean_dec(x_348);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_442 = !lean_is_exclusive(x_350);
if (x_442 == 0)
{
return x_350;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_350, 0);
x_444 = lean_ctor_get(x_350, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_350);
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
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_446 = !lean_is_exclusive(x_347);
if (x_446 == 0)
{
return x_347;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_347, 0);
x_448 = lean_ctor_get(x_347, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_347);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_450 = !lean_is_exclusive(x_238);
if (x_450 == 0)
{
return x_238;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_238, 0);
x_452 = lean_ctor_get(x_238, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_238);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_454 = !lean_is_exclusive(x_16);
if (x_454 == 0)
{
return x_16;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_16, 0);
x_456 = lean_ctor_get(x_16, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_16);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_458 = !lean_is_exclusive(x_11);
if (x_458 == 0)
{
return x_11;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_11, 0);
x_460 = lean_ctor_get(x_11, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_11);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_462 = !lean_is_exclusive(x_9);
if (x_462 == 0)
{
return x_9;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_9, 0);
x_464 = lean_ctor_get(x_9, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_9);
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
lean_object* l_Lean_Meta_rewriteCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_rewriteCore___closed__2;
x_9 = lean_box(x_4);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_rewriteCore___lambda__1___boxed), 8, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_2);
lean_closure_set(x_10, 5, x_5);
x_11 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 4);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Meta_withLocalContext___rarg(x_14, x_15, x_10, x_6, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Meta_rewriteCore___lambda__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_10;
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
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Rewrite(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
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
