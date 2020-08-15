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
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_30 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_31 = lean_box(0);
x_32 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_30, x_31, x_8, x_18);
lean_dec(x_8);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = l_Lean_Expr_appFn_x21(x_21);
x_34 = l_Lean_Expr_appFn_x21(x_33);
x_35 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_36 = l_Lean_Expr_appArg_x21(x_33);
lean_dec(x_33);
x_37 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
if (x_4 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Expr_getAppFn___main(x_36);
x_39 = l_Lean_Expr_isMVar(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_18);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_41);
x_43 = l_Lean_Meta_kabstract(x_41, x_36, x_6, x_8, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_110; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_110 = l_Lean_Expr_hasLooseBVars(x_44);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_111 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_112 = lean_box(0);
x_113 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_111, x_112, x_8, x_45);
lean_dec(x_8);
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
x_46 = x_45;
goto block_109;
}
block_109:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_expr_instantiate1(x_44, x_37);
lean_dec(x_37);
x_48 = l_Lean_Meta_instantiateMVars(x_47, x_8, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_8);
lean_inc_n(x_41, 2);
x_51 = l_Lean_Meta_mkEq(x_41, x_41, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Expr_appFn_x21(x_52);
lean_dec(x_52);
x_55 = l_Lean_mkApp(x_54, x_44);
x_56 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_57 = 0;
x_58 = l_Lean_mkLambda(x_56, x_57, x_35, x_55);
lean_inc(x_8);
lean_inc(x_58);
x_93 = l_Lean_Meta_isTypeCorrect(x_58, x_8, x_53);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_58);
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_98 = lean_box(0);
x_99 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_97, x_98, x_8, x_96);
lean_dec(x_8);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
lean_dec(x_93);
x_59 = x_104;
goto block_92;
}
block_92:
{
lean_object* x_60; 
lean_inc(x_8);
x_60 = l_Lean_Meta_mkEqRefl(x_41, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_8);
x_63 = l_Lean_Meta_mkEqNDRec(x_58, x_61, x_23, x_8, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_8);
x_66 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_65);
lean_dec(x_20);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_67);
lean_dec(x_8);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = l_Array_toList___rarg(x_70);
lean_dec(x_70);
x_72 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_71);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_49);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_68, 0, x_73);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_68, 0);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_68);
x_76 = l_Array_toList___rarg(x_74);
lean_dec(x_74);
x_77 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_76);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_49);
lean_ctor_set(x_78, 1, x_64);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_64);
lean_dec(x_49);
lean_dec(x_19);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_66);
if (x_80 == 0)
{
return x_66;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_66, 0);
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_66);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_49);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_63);
if (x_84 == 0)
{
return x_63;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_63, 0);
x_86 = lean_ctor_get(x_63, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_63);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_58);
lean_dec(x_49);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_60);
if (x_88 == 0)
{
return x_60;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_60, 0);
x_90 = lean_ctor_get(x_60, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_60);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_51);
if (x_105 == 0)
{
return x_51;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_51, 0);
x_107 = lean_ctor_get(x_51, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_51);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_43);
if (x_118 == 0)
{
return x_43;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_43, 0);
x_120 = lean_ctor_get(x_43, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_43);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_122 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_123 = lean_box(0);
x_124 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_122, x_123, x_8, x_18);
lean_dec(x_8);
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
}
else
{
lean_object* x_129; 
lean_inc(x_8);
x_129 = l_Lean_Meta_mkEqSymm(x_23, x_8, x_18);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_216; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_8);
lean_inc(x_36);
lean_inc(x_37);
x_216 = l_Lean_Meta_mkEq(x_37, x_36, x_8, x_131);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = l_Lean_Expr_getAppFn___main(x_37);
x_219 = l_Lean_Expr_isMVar(x_218);
lean_dec(x_218);
if (x_219 == 0)
{
x_132 = x_217;
goto block_215;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_130);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_220 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_221 = lean_box(0);
x_222 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_220, x_221, x_8, x_217);
lean_dec(x_8);
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
}
else
{
uint8_t x_227; 
lean_dec(x_130);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_227 = !lean_is_exclusive(x_216);
if (x_227 == 0)
{
return x_216;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_216, 0);
x_229 = lean_ctor_get(x_216, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_216);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
block_215:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_8);
lean_inc(x_134);
x_136 = l_Lean_Meta_kabstract(x_134, x_37, x_6, x_8, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_203; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_203 = l_Lean_Expr_hasLooseBVars(x_137);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_130);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_19);
x_204 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_205 = lean_box(0);
x_206 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_204, x_205, x_8, x_138);
lean_dec(x_8);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_206);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
else
{
x_139 = x_138;
goto block_202;
}
block_202:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_expr_instantiate1(x_137, x_36);
lean_dec(x_36);
x_141 = l_Lean_Meta_instantiateMVars(x_140, x_8, x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_8);
lean_inc_n(x_134, 2);
x_144 = l_Lean_Meta_mkEq(x_134, x_134, x_8, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Expr_appFn_x21(x_145);
lean_dec(x_145);
x_148 = l_Lean_mkApp(x_147, x_137);
x_149 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_150 = 0;
x_151 = l_Lean_mkLambda(x_149, x_150, x_35, x_148);
lean_inc(x_8);
lean_inc(x_151);
x_186 = l_Lean_Meta_isTypeCorrect(x_151, x_8, x_146);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_unbox(x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_151);
lean_dec(x_142);
lean_dec(x_134);
lean_dec(x_130);
lean_dec(x_20);
lean_dec(x_19);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_191 = lean_box(0);
x_192 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_190, x_191, x_8, x_189);
lean_dec(x_8);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
return x_192;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_192);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
else
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_186, 1);
lean_inc(x_197);
lean_dec(x_186);
x_152 = x_197;
goto block_185;
}
block_185:
{
lean_object* x_153; 
lean_inc(x_8);
x_153 = l_Lean_Meta_mkEqRefl(x_134, x_8, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_8);
x_156 = l_Lean_Meta_mkEqNDRec(x_151, x_154, x_130, x_8, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_8);
x_159 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_158);
lean_dec(x_20);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_160);
lean_dec(x_8);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = l_Array_toList___rarg(x_163);
lean_dec(x_163);
x_165 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_164);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_142);
lean_ctor_set(x_166, 1, x_157);
lean_ctor_set(x_166, 2, x_165);
lean_ctor_set(x_161, 0, x_166);
return x_161;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_161, 0);
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_161);
x_169 = l_Array_toList___rarg(x_167);
lean_dec(x_167);
x_170 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_169);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_142);
lean_ctor_set(x_171, 1, x_157);
lean_ctor_set(x_171, 2, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
}
else
{
uint8_t x_173; 
lean_dec(x_157);
lean_dec(x_142);
lean_dec(x_19);
lean_dec(x_8);
x_173 = !lean_is_exclusive(x_159);
if (x_173 == 0)
{
return x_159;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_159, 0);
x_175 = lean_ctor_get(x_159, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_159);
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
lean_dec(x_142);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_156);
if (x_177 == 0)
{
return x_156;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_156, 0);
x_179 = lean_ctor_get(x_156, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_156);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_151);
lean_dec(x_142);
lean_dec(x_130);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_181 = !lean_is_exclusive(x_153);
if (x_181 == 0)
{
return x_153;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_153, 0);
x_183 = lean_ctor_get(x_153, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_153);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_142);
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_130);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_144);
if (x_198 == 0)
{
return x_144;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_144, 0);
x_200 = lean_ctor_get(x_144, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_144);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_134);
lean_dec(x_130);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_211 = !lean_is_exclusive(x_136);
if (x_211 == 0)
{
return x_136;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_136, 0);
x_213 = lean_ctor_get(x_136, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_136);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_231 = !lean_is_exclusive(x_129);
if (x_231 == 0)
{
return x_129;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_129, 0);
x_233 = lean_ctor_get(x_129, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_129);
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
x_235 = l_Lean_Expr_appFn_x21(x_21);
x_236 = l_Lean_Expr_appArg_x21(x_235);
lean_dec(x_235);
x_237 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_237);
lean_inc(x_236);
x_238 = l_Lean_Meta_mkEq(x_236, x_237, x_8, x_18);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Meta_rewriteCore___lambda__1___closed__17;
x_242 = l_Lean_mkApp3(x_241, x_236, x_237, x_23);
x_243 = l_Lean_Expr_eq_x3f___closed__2;
x_244 = lean_unsigned_to_nat(3u);
x_245 = l_Lean_Expr_isAppOfArity___main(x_239, x_243, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_246 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_247 = lean_box(0);
x_248 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_246, x_247, x_8, x_240);
lean_dec(x_8);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_249 = l_Lean_Expr_appFn_x21(x_239);
x_250 = l_Lean_Expr_appFn_x21(x_249);
x_251 = l_Lean_Expr_appArg_x21(x_250);
lean_dec(x_250);
x_252 = l_Lean_Expr_appArg_x21(x_249);
lean_dec(x_249);
x_253 = l_Lean_Expr_appArg_x21(x_239);
lean_dec(x_239);
if (x_4 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = l_Lean_Expr_getAppFn___main(x_252);
x_255 = l_Lean_Expr_isMVar(x_254);
lean_dec(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_240);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_8);
lean_inc(x_257);
x_259 = l_Lean_Meta_kabstract(x_257, x_252, x_6, x_8, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_326; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_326 = l_Lean_Expr_hasLooseBVars(x_260);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_dec(x_260);
lean_dec(x_257);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_242);
lean_dec(x_20);
lean_dec(x_19);
x_327 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_328 = lean_box(0);
x_329 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_327, x_328, x_8, x_261);
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
else
{
x_262 = x_261;
goto block_325;
}
block_325:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_expr_instantiate1(x_260, x_253);
lean_dec(x_253);
x_264 = l_Lean_Meta_instantiateMVars(x_263, x_8, x_262);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
lean_inc(x_8);
lean_inc_n(x_257, 2);
x_267 = l_Lean_Meta_mkEq(x_257, x_257, x_8, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_Expr_appFn_x21(x_268);
lean_dec(x_268);
x_271 = l_Lean_mkApp(x_270, x_260);
x_272 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_273 = 0;
x_274 = l_Lean_mkLambda(x_272, x_273, x_251, x_271);
lean_inc(x_8);
lean_inc(x_274);
x_309 = l_Lean_Meta_isTypeCorrect(x_274, x_8, x_269);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_unbox(x_310);
lean_dec(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
lean_dec(x_274);
lean_dec(x_265);
lean_dec(x_257);
lean_dec(x_242);
lean_dec(x_20);
lean_dec(x_19);
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
lean_dec(x_309);
x_313 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_314 = lean_box(0);
x_315 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_313, x_314, x_8, x_312);
lean_dec(x_8);
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
return x_315;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_315, 0);
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_315);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
else
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_309, 1);
lean_inc(x_320);
lean_dec(x_309);
x_275 = x_320;
goto block_308;
}
block_308:
{
lean_object* x_276; 
lean_inc(x_8);
x_276 = l_Lean_Meta_mkEqRefl(x_257, x_8, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_8);
x_279 = l_Lean_Meta_mkEqNDRec(x_274, x_277, x_242, x_8, x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_8);
x_282 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_281);
lean_dec(x_20);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_283);
lean_dec(x_8);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = l_Array_toList___rarg(x_286);
lean_dec(x_286);
x_288 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_287);
x_289 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_289, 0, x_265);
lean_ctor_set(x_289, 1, x_280);
lean_ctor_set(x_289, 2, x_288);
lean_ctor_set(x_284, 0, x_289);
return x_284;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_290 = lean_ctor_get(x_284, 0);
x_291 = lean_ctor_get(x_284, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_284);
x_292 = l_Array_toList___rarg(x_290);
lean_dec(x_290);
x_293 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_292);
x_294 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_294, 0, x_265);
lean_ctor_set(x_294, 1, x_280);
lean_ctor_set(x_294, 2, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_291);
return x_295;
}
}
else
{
uint8_t x_296; 
lean_dec(x_280);
lean_dec(x_265);
lean_dec(x_19);
lean_dec(x_8);
x_296 = !lean_is_exclusive(x_282);
if (x_296 == 0)
{
return x_282;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_282, 0);
x_298 = lean_ctor_get(x_282, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_282);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_265);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_300 = !lean_is_exclusive(x_279);
if (x_300 == 0)
{
return x_279;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_279, 0);
x_302 = lean_ctor_get(x_279, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_279);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_274);
lean_dec(x_265);
lean_dec(x_242);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_304 = !lean_is_exclusive(x_276);
if (x_304 == 0)
{
return x_276;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_276, 0);
x_306 = lean_ctor_get(x_276, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_276);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_265);
lean_dec(x_260);
lean_dec(x_257);
lean_dec(x_251);
lean_dec(x_242);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_321 = !lean_is_exclusive(x_267);
if (x_321 == 0)
{
return x_267;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_267, 0);
x_323 = lean_ctor_get(x_267, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_267);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
}
else
{
uint8_t x_334; 
lean_dec(x_257);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_242);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_334 = !lean_is_exclusive(x_259);
if (x_334 == 0)
{
return x_259;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_259, 0);
x_336 = lean_ctor_get(x_259, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_259);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_242);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_338 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_339 = lean_box(0);
x_340 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_338, x_339, x_8, x_240);
lean_dec(x_8);
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
return x_340;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_340, 0);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_340);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
else
{
lean_object* x_345; 
lean_inc(x_8);
x_345 = l_Lean_Meta_mkEqSymm(x_242, x_8, x_240);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_432; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
lean_inc(x_8);
lean_inc(x_252);
lean_inc(x_253);
x_432 = l_Lean_Meta_mkEq(x_253, x_252, x_8, x_347);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_434 = l_Lean_Expr_getAppFn___main(x_253);
x_435 = l_Lean_Expr_isMVar(x_434);
lean_dec(x_434);
if (x_435 == 0)
{
x_348 = x_433;
goto block_431;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
lean_dec(x_346);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_436 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_437 = lean_box(0);
x_438 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_436, x_437, x_8, x_433);
lean_dec(x_8);
x_439 = !lean_is_exclusive(x_438);
if (x_439 == 0)
{
return x_438;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_438, 0);
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_438);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
uint8_t x_443; 
lean_dec(x_346);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_443 = !lean_is_exclusive(x_432);
if (x_443 == 0)
{
return x_432;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_432, 0);
x_445 = lean_ctor_get(x_432, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_432);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
block_431:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_348);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
lean_inc(x_8);
lean_inc(x_350);
x_352 = l_Lean_Meta_kabstract(x_350, x_253, x_6, x_8, x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_419; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_419 = l_Lean_Expr_hasLooseBVars(x_353);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
lean_dec(x_353);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_20);
lean_dec(x_19);
x_420 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_421 = lean_box(0);
x_422 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_420, x_421, x_8, x_354);
lean_dec(x_8);
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
return x_422;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_422, 0);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_422);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
else
{
x_355 = x_354;
goto block_418;
}
block_418:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_356 = lean_expr_instantiate1(x_353, x_252);
lean_dec(x_252);
x_357 = l_Lean_Meta_instantiateMVars(x_356, x_8, x_355);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
lean_inc(x_8);
lean_inc_n(x_350, 2);
x_360 = l_Lean_Meta_mkEq(x_350, x_350, x_8, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = l_Lean_Expr_appFn_x21(x_361);
lean_dec(x_361);
x_364 = l_Lean_mkApp(x_363, x_353);
x_365 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_366 = 0;
x_367 = l_Lean_mkLambda(x_365, x_366, x_251, x_364);
lean_inc(x_8);
lean_inc(x_367);
x_402 = l_Lean_Meta_isTypeCorrect(x_367, x_8, x_362);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_unbox(x_403);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
lean_dec(x_367);
lean_dec(x_358);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_20);
lean_dec(x_19);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_dec(x_402);
x_406 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_407 = lean_box(0);
x_408 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_406, x_407, x_8, x_405);
lean_dec(x_8);
x_409 = !lean_is_exclusive(x_408);
if (x_409 == 0)
{
return x_408;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_408, 0);
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_408);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
else
{
lean_object* x_413; 
x_413 = lean_ctor_get(x_402, 1);
lean_inc(x_413);
lean_dec(x_402);
x_368 = x_413;
goto block_401;
}
block_401:
{
lean_object* x_369; 
lean_inc(x_8);
x_369 = l_Lean_Meta_mkEqRefl(x_350, x_8, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
lean_inc(x_8);
x_372 = l_Lean_Meta_mkEqNDRec(x_367, x_370, x_346, x_8, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
lean_inc(x_8);
x_375 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_374);
lean_dec(x_20);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_377 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_376);
lean_dec(x_8);
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_379 = lean_ctor_get(x_377, 0);
x_380 = l_Array_toList___rarg(x_379);
lean_dec(x_379);
x_381 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_380);
x_382 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_382, 0, x_358);
lean_ctor_set(x_382, 1, x_373);
lean_ctor_set(x_382, 2, x_381);
lean_ctor_set(x_377, 0, x_382);
return x_377;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_383 = lean_ctor_get(x_377, 0);
x_384 = lean_ctor_get(x_377, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_377);
x_385 = l_Array_toList___rarg(x_383);
lean_dec(x_383);
x_386 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_385);
x_387 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_387, 0, x_358);
lean_ctor_set(x_387, 1, x_373);
lean_ctor_set(x_387, 2, x_386);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_384);
return x_388;
}
}
else
{
uint8_t x_389; 
lean_dec(x_373);
lean_dec(x_358);
lean_dec(x_19);
lean_dec(x_8);
x_389 = !lean_is_exclusive(x_375);
if (x_389 == 0)
{
return x_375;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_375, 0);
x_391 = lean_ctor_get(x_375, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_375);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_358);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_393 = !lean_is_exclusive(x_372);
if (x_393 == 0)
{
return x_372;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_372, 0);
x_395 = lean_ctor_get(x_372, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_372);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_367);
lean_dec(x_358);
lean_dec(x_346);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_397 = !lean_is_exclusive(x_369);
if (x_397 == 0)
{
return x_369;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_369, 0);
x_399 = lean_ctor_get(x_369, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_369);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_358);
lean_dec(x_353);
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_251);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_414 = !lean_is_exclusive(x_360);
if (x_414 == 0)
{
return x_360;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_360, 0);
x_416 = lean_ctor_get(x_360, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_360);
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
uint8_t x_427; 
lean_dec(x_350);
lean_dec(x_346);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_427 = !lean_is_exclusive(x_352);
if (x_427 == 0)
{
return x_352;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_352, 0);
x_429 = lean_ctor_get(x_352, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_352);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_447 = !lean_is_exclusive(x_345);
if (x_447 == 0)
{
return x_345;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_345, 0);
x_449 = lean_ctor_get(x_345, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_345);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
}
}
else
{
uint8_t x_451; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_451 = !lean_is_exclusive(x_238);
if (x_451 == 0)
{
return x_238;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_238, 0);
x_453 = lean_ctor_get(x_238, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_238);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
}
else
{
uint8_t x_455; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_455 = !lean_is_exclusive(x_15);
if (x_455 == 0)
{
return x_15;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_15, 0);
x_457 = lean_ctor_get(x_15, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_15);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
else
{
uint8_t x_459; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_459 = !lean_is_exclusive(x_10);
if (x_459 == 0)
{
return x_10;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_10, 0);
x_461 = lean_ctor_get(x_10, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_10);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
return x_462;
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
