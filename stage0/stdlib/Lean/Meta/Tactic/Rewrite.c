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
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_31 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_32 = lean_box(0);
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_31, x_32, x_7, x_19);
lean_dec(x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = l_Lean_Expr_appFn_x21(x_22);
x_35 = l_Lean_Expr_appFn_x21(x_34);
x_36 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_37 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_38 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
if (x_4 == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_39 = l_Lean_Expr_getAppFn___main(x_37);
x_40 = l_Lean_Expr_isMVar(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_134; 
x_134 = 0;
x_41 = x_134;
goto block_133;
}
else
{
uint8_t x_135; 
x_135 = 1;
x_41 = x_135;
goto block_133;
}
block_133:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_19;
goto block_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_126 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_127 = lean_box(0);
x_128 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_126, x_127, x_7, x_19);
lean_dec(x_7);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
return x_128;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_128);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
block_125:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_7);
lean_inc(x_44);
x_46 = l_Lean_Meta_kabstract(x_44, x_37, x_6, x_7, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_hasLooseBVars(x_47);
x_50 = lean_expr_instantiate1(x_47, x_38);
lean_dec(x_38);
if (x_49 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_114 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_115 = lean_box(0);
x_116 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_114, x_115, x_7, x_48);
lean_dec(x_7);
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
x_51 = x_48;
goto block_113;
}
block_113:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Lean_Meta_instantiateMVars(x_50, x_7, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_7);
lean_inc_n(x_44, 2);
x_55 = l_Lean_Meta_mkEq(x_44, x_44, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_appFn_x21(x_56);
lean_dec(x_56);
x_59 = l_Lean_mkApp(x_58, x_47);
x_60 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_61 = 0;
x_62 = l_Lean_mkLambda(x_60, x_61, x_36, x_59);
lean_inc(x_7);
lean_inc(x_62);
x_97 = l_Lean_Meta_isTypeCorrect(x_62, x_7, x_57);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_62);
lean_dec(x_53);
lean_dec(x_44);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_102 = lean_box(0);
x_103 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_101, x_102, x_7, x_100);
lean_dec(x_7);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_97, 1);
lean_inc(x_108);
lean_dec(x_97);
x_63 = x_108;
goto block_96;
}
block_96:
{
lean_object* x_64; 
lean_inc(x_7);
x_64 = l_Lean_Meta_mkEqRefl(x_44, x_7, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_7);
x_67 = l_Lean_Meta_mkEqNDRec(x_62, x_65, x_24, x_7, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_7);
x_70 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_69);
lean_dec(x_21);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_71);
lean_dec(x_7);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = l_Array_toList___rarg(x_74);
lean_dec(x_74);
x_76 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_75);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_53);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_72, 0);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_80 = l_Array_toList___rarg(x_78);
lean_dec(x_78);
x_81 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_53);
lean_ctor_set(x_82, 1, x_68);
lean_ctor_set(x_82, 2, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_68);
lean_dec(x_53);
lean_dec(x_20);
lean_dec(x_7);
x_84 = !lean_is_exclusive(x_70);
if (x_84 == 0)
{
return x_70;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_70, 0);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_70);
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
lean_dec(x_53);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_67);
if (x_88 == 0)
{
return x_67;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_67, 0);
x_90 = lean_ctor_get(x_67, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_67);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_62);
lean_dec(x_53);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_64);
if (x_92 == 0)
{
return x_64;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_64, 0);
x_94 = lean_ctor_get(x_64, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_64);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_55);
if (x_109 == 0)
{
return x_55;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_55, 0);
x_111 = lean_ctor_get(x_55, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_55);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
else
{
lean_object* x_136; 
lean_inc(x_7);
x_136 = l_Lean_Meta_mkEqSymm(x_24, x_7, x_19);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_7);
lean_inc(x_37);
lean_inc(x_38);
x_139 = l_Lean_Meta_mkEq(x_38, x_37, x_7, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_Expr_getAppFn___main(x_38);
x_142 = l_Lean_Expr_isMVar(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
x_143 = x_140;
goto block_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_137);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_227 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_228 = lean_box(0);
x_229 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_227, x_228, x_7, x_140);
lean_dec(x_7);
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
return x_229;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_229);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
block_226:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_7);
lean_inc(x_145);
x_147 = l_Lean_Meta_kabstract(x_145, x_38, x_6, x_7, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Expr_hasLooseBVars(x_148);
x_151 = lean_expr_instantiate1(x_148, x_37);
lean_dec(x_37);
if (x_150 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
x_215 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_216 = lean_box(0);
x_217 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_215, x_216, x_7, x_149);
lean_dec(x_7);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
return x_217;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_217);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
else
{
x_152 = x_149;
goto block_214;
}
block_214:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = l_Lean_Meta_instantiateMVars(x_151, x_7, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_7);
lean_inc_n(x_145, 2);
x_156 = l_Lean_Meta_mkEq(x_145, x_145, x_7, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_Expr_appFn_x21(x_157);
lean_dec(x_157);
x_160 = l_Lean_mkApp(x_159, x_148);
x_161 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_162 = 0;
x_163 = l_Lean_mkLambda(x_161, x_162, x_36, x_160);
lean_inc(x_7);
lean_inc(x_163);
x_198 = l_Lean_Meta_isTypeCorrect(x_163, x_7, x_158);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_163);
lean_dec(x_154);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_21);
lean_dec(x_20);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_203 = lean_box(0);
x_204 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_202, x_203, x_7, x_201);
lean_dec(x_7);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
return x_204;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_204);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
else
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_198, 1);
lean_inc(x_209);
lean_dec(x_198);
x_164 = x_209;
goto block_197;
}
block_197:
{
lean_object* x_165; 
lean_inc(x_7);
x_165 = l_Lean_Meta_mkEqRefl(x_145, x_7, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_7);
x_168 = l_Lean_Meta_mkEqNDRec(x_163, x_166, x_137, x_7, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_7);
x_171 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_170);
lean_dec(x_21);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_172);
lean_dec(x_7);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = l_Array_toList___rarg(x_175);
lean_dec(x_175);
x_177 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_176);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_154);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_173, 0, x_178);
return x_173;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_173, 0);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_173);
x_181 = l_Array_toList___rarg(x_179);
lean_dec(x_179);
x_182 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_181);
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_154);
lean_ctor_set(x_183, 1, x_169);
lean_ctor_set(x_183, 2, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_180);
return x_184;
}
}
else
{
uint8_t x_185; 
lean_dec(x_169);
lean_dec(x_154);
lean_dec(x_20);
lean_dec(x_7);
x_185 = !lean_is_exclusive(x_171);
if (x_185 == 0)
{
return x_171;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_171, 0);
x_187 = lean_ctor_get(x_171, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_171);
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
lean_dec(x_154);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_168);
if (x_189 == 0)
{
return x_168;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_168, 0);
x_191 = lean_ctor_get(x_168, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_168);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_163);
lean_dec(x_154);
lean_dec(x_137);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_165);
if (x_193 == 0)
{
return x_165;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_165, 0);
x_195 = lean_ctor_get(x_165, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_165);
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
uint8_t x_210; 
lean_dec(x_154);
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_156);
if (x_210 == 0)
{
return x_156;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_156, 0);
x_212 = lean_ctor_get(x_156, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_156);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_147);
if (x_222 == 0)
{
return x_147;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_147, 0);
x_224 = lean_ctor_get(x_147, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_147);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_137);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_139);
if (x_234 == 0)
{
return x_139;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_139, 0);
x_236 = lean_ctor_get(x_139, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_139);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_136);
if (x_238 == 0)
{
return x_136;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_136, 0);
x_240 = lean_ctor_get(x_136, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_136);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_242 = l_Lean_Expr_appFn_x21(x_22);
x_243 = l_Lean_Expr_appArg_x21(x_242);
lean_dec(x_242);
x_244 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
lean_inc(x_7);
lean_inc(x_244);
lean_inc(x_243);
x_245 = l_Lean_Meta_mkEq(x_243, x_244, x_7, x_19);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_Meta_rewriteCore___lambda__1___closed__17;
x_249 = l_Lean_mkApp3(x_248, x_243, x_244, x_24);
x_250 = l_Lean_Expr_eq_x3f___closed__2;
x_251 = lean_unsigned_to_nat(3u);
x_252 = l_Lean_Expr_isAppOfArity___main(x_246, x_250, x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_249);
lean_dec(x_246);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_253 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_254 = lean_box(0);
x_255 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_253, x_254, x_7, x_247);
lean_dec(x_7);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_256 = l_Lean_Expr_appFn_x21(x_246);
x_257 = l_Lean_Expr_appFn_x21(x_256);
x_258 = l_Lean_Expr_appArg_x21(x_257);
lean_dec(x_257);
x_259 = l_Lean_Expr_appArg_x21(x_256);
lean_dec(x_256);
x_260 = l_Lean_Expr_appArg_x21(x_246);
lean_dec(x_246);
if (x_4 == 0)
{
lean_object* x_261; uint8_t x_262; uint8_t x_263; 
x_261 = l_Lean_Expr_getAppFn___main(x_259);
x_262 = l_Lean_Expr_isMVar(x_261);
lean_dec(x_261);
if (x_262 == 0)
{
uint8_t x_356; 
x_356 = 0;
x_263 = x_356;
goto block_355;
}
else
{
uint8_t x_357; 
x_357 = 1;
x_263 = x_357;
goto block_355;
}
block_355:
{
lean_object* x_264; 
if (x_263 == 0)
{
x_264 = x_247;
goto block_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_249);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_348 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_349 = lean_box(0);
x_350 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_348, x_349, x_7, x_247);
lean_dec(x_7);
x_351 = !lean_is_exclusive(x_350);
if (x_351 == 0)
{
return x_350;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_350, 0);
x_353 = lean_ctor_get(x_350, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_350);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
block_347:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_7);
lean_inc(x_266);
x_268 = l_Lean_Meta_kabstract(x_266, x_259, x_6, x_7, x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lean_Expr_hasLooseBVars(x_269);
x_272 = lean_expr_instantiate1(x_269, x_260);
lean_dec(x_260);
if (x_271 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_258);
lean_dec(x_249);
lean_dec(x_21);
lean_dec(x_20);
x_336 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_337 = lean_box(0);
x_338 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_336, x_337, x_7, x_270);
lean_dec(x_7);
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
return x_338;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_338, 0);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_338);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
else
{
x_273 = x_270;
goto block_335;
}
block_335:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = l_Lean_Meta_instantiateMVars(x_272, x_7, x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
lean_inc(x_7);
lean_inc_n(x_266, 2);
x_277 = l_Lean_Meta_mkEq(x_266, x_266, x_7, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Lean_Expr_appFn_x21(x_278);
lean_dec(x_278);
x_281 = l_Lean_mkApp(x_280, x_269);
x_282 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_283 = 0;
x_284 = l_Lean_mkLambda(x_282, x_283, x_258, x_281);
lean_inc(x_7);
lean_inc(x_284);
x_319 = l_Lean_Meta_isTypeCorrect(x_284, x_7, x_279);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_unbox(x_320);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
lean_dec(x_284);
lean_dec(x_275);
lean_dec(x_266);
lean_dec(x_249);
lean_dec(x_21);
lean_dec(x_20);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_323 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_324 = lean_box(0);
x_325 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_323, x_324, x_7, x_322);
lean_dec(x_7);
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
return x_325;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_325, 0);
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_325);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
else
{
lean_object* x_330; 
x_330 = lean_ctor_get(x_319, 1);
lean_inc(x_330);
lean_dec(x_319);
x_285 = x_330;
goto block_318;
}
block_318:
{
lean_object* x_286; 
lean_inc(x_7);
x_286 = l_Lean_Meta_mkEqRefl(x_266, x_7, x_285);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_7);
x_289 = l_Lean_Meta_mkEqNDRec(x_284, x_287, x_249, x_7, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
lean_inc(x_7);
x_292 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_291);
lean_dec(x_21);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_294 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_293);
lean_dec(x_7);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_294, 0);
x_297 = l_Array_toList___rarg(x_296);
lean_dec(x_296);
x_298 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_297);
x_299 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_290);
lean_ctor_set(x_299, 2, x_298);
lean_ctor_set(x_294, 0, x_299);
return x_294;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_ctor_get(x_294, 0);
x_301 = lean_ctor_get(x_294, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_294);
x_302 = l_Array_toList___rarg(x_300);
lean_dec(x_300);
x_303 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_302);
x_304 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_304, 0, x_275);
lean_ctor_set(x_304, 1, x_290);
lean_ctor_set(x_304, 2, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_301);
return x_305;
}
}
else
{
uint8_t x_306; 
lean_dec(x_290);
lean_dec(x_275);
lean_dec(x_20);
lean_dec(x_7);
x_306 = !lean_is_exclusive(x_292);
if (x_306 == 0)
{
return x_292;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_292, 0);
x_308 = lean_ctor_get(x_292, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_292);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_275);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_289);
if (x_310 == 0)
{
return x_289;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_289, 0);
x_312 = lean_ctor_get(x_289, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_289);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_284);
lean_dec(x_275);
lean_dec(x_249);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_286);
if (x_314 == 0)
{
return x_286;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_286, 0);
x_316 = lean_ctor_get(x_286, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_286);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
else
{
uint8_t x_331; 
lean_dec(x_275);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_258);
lean_dec(x_249);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_277);
if (x_331 == 0)
{
return x_277;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_277, 0);
x_333 = lean_ctor_get(x_277, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_277);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
else
{
uint8_t x_343; 
lean_dec(x_266);
lean_dec(x_260);
lean_dec(x_258);
lean_dec(x_249);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_343 = !lean_is_exclusive(x_268);
if (x_343 == 0)
{
return x_268;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_268, 0);
x_345 = lean_ctor_get(x_268, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_268);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
}
}
else
{
lean_object* x_358; 
lean_inc(x_7);
x_358 = l_Lean_Meta_mkEqSymm(x_249, x_7, x_247);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_7);
lean_inc(x_259);
lean_inc(x_260);
x_361 = l_Lean_Meta_mkEq(x_260, x_259, x_7, x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; 
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_363 = l_Lean_Expr_getAppFn___main(x_260);
x_364 = l_Lean_Expr_isMVar(x_363);
lean_dec(x_363);
if (x_364 == 0)
{
x_365 = x_362;
goto block_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
lean_dec(x_359);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_449 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_450 = lean_box(0);
x_451 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_449, x_450, x_7, x_362);
lean_dec(x_7);
x_452 = !lean_is_exclusive(x_451);
if (x_452 == 0)
{
return x_451;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_451, 0);
x_454 = lean_ctor_get(x_451, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_451);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
block_448:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = l_Lean_Meta_instantiateMVars(x_5, x_7, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
lean_inc(x_7);
lean_inc(x_367);
x_369 = l_Lean_Meta_kabstract(x_367, x_260, x_6, x_7, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = l_Lean_Expr_hasLooseBVars(x_370);
x_373 = lean_expr_instantiate1(x_370, x_259);
lean_dec(x_259);
if (x_372 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
lean_dec(x_373);
lean_dec(x_370);
lean_dec(x_367);
lean_dec(x_359);
lean_dec(x_258);
lean_dec(x_21);
lean_dec(x_20);
x_437 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_438 = lean_box(0);
x_439 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_437, x_438, x_7, x_371);
lean_dec(x_7);
x_440 = !lean_is_exclusive(x_439);
if (x_440 == 0)
{
return x_439;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_439, 0);
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_439);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
else
{
x_374 = x_371;
goto block_436;
}
block_436:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = l_Lean_Meta_instantiateMVars(x_373, x_7, x_374);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
lean_inc(x_7);
lean_inc_n(x_367, 2);
x_378 = l_Lean_Meta_mkEq(x_367, x_367, x_7, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = l_Lean_Expr_appFn_x21(x_379);
lean_dec(x_379);
x_382 = l_Lean_mkApp(x_381, x_370);
x_383 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_384 = 0;
x_385 = l_Lean_mkLambda(x_383, x_384, x_258, x_382);
lean_inc(x_7);
lean_inc(x_385);
x_420 = l_Lean_Meta_isTypeCorrect(x_385, x_7, x_380);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_unbox(x_421);
lean_dec(x_421);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_385);
lean_dec(x_376);
lean_dec(x_367);
lean_dec(x_359);
lean_dec(x_21);
lean_dec(x_20);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_425 = lean_box(0);
x_426 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_424, x_425, x_7, x_423);
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
lean_object* x_431; 
x_431 = lean_ctor_get(x_420, 1);
lean_inc(x_431);
lean_dec(x_420);
x_386 = x_431;
goto block_419;
}
block_419:
{
lean_object* x_387; 
lean_inc(x_7);
x_387 = l_Lean_Meta_mkEqRefl(x_367, x_7, x_386);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
lean_inc(x_7);
x_390 = l_Lean_Meta_mkEqNDRec(x_385, x_388, x_359, x_7, x_389);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
lean_inc(x_7);
x_393 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_20, x_21, x_7, x_392);
lean_dec(x_21);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
x_395 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_20, x_23, x_23, x_7, x_394);
lean_dec(x_7);
x_396 = !lean_is_exclusive(x_395);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_395, 0);
x_398 = l_Array_toList___rarg(x_397);
lean_dec(x_397);
x_399 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_398);
x_400 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_400, 0, x_376);
lean_ctor_set(x_400, 1, x_391);
lean_ctor_set(x_400, 2, x_399);
lean_ctor_set(x_395, 0, x_400);
return x_395;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_401 = lean_ctor_get(x_395, 0);
x_402 = lean_ctor_get(x_395, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_395);
x_403 = l_Array_toList___rarg(x_401);
lean_dec(x_401);
x_404 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_403);
x_405 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_405, 0, x_376);
lean_ctor_set(x_405, 1, x_391);
lean_ctor_set(x_405, 2, x_404);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_402);
return x_406;
}
}
else
{
uint8_t x_407; 
lean_dec(x_391);
lean_dec(x_376);
lean_dec(x_20);
lean_dec(x_7);
x_407 = !lean_is_exclusive(x_393);
if (x_407 == 0)
{
return x_393;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_393, 0);
x_409 = lean_ctor_get(x_393, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_393);
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
lean_dec(x_376);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_411 = !lean_is_exclusive(x_390);
if (x_411 == 0)
{
return x_390;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_390, 0);
x_413 = lean_ctor_get(x_390, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_390);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_385);
lean_dec(x_376);
lean_dec(x_359);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_415 = !lean_is_exclusive(x_387);
if (x_415 == 0)
{
return x_387;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_387, 0);
x_417 = lean_ctor_get(x_387, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_387);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
}
else
{
uint8_t x_432; 
lean_dec(x_376);
lean_dec(x_370);
lean_dec(x_367);
lean_dec(x_359);
lean_dec(x_258);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_432 = !lean_is_exclusive(x_378);
if (x_432 == 0)
{
return x_378;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_378, 0);
x_434 = lean_ctor_get(x_378, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_378);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_367);
lean_dec(x_359);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_369);
if (x_444 == 0)
{
return x_369;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_369, 0);
x_446 = lean_ctor_get(x_369, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_369);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
else
{
uint8_t x_456; 
lean_dec(x_359);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_361);
if (x_456 == 0)
{
return x_361;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_361, 0);
x_458 = lean_ctor_get(x_361, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_361);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
else
{
uint8_t x_460; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_460 = !lean_is_exclusive(x_358);
if (x_460 == 0)
{
return x_358;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_358, 0);
x_462 = lean_ctor_get(x_358, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_358);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
}
}
}
else
{
uint8_t x_464; 
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_464 = !lean_is_exclusive(x_245);
if (x_464 == 0)
{
return x_245;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_245, 0);
x_466 = lean_ctor_get(x_245, 1);
lean_inc(x_466);
lean_inc(x_465);
lean_dec(x_245);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
return x_467;
}
}
}
}
else
{
uint8_t x_468; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_468 = !lean_is_exclusive(x_16);
if (x_468 == 0)
{
return x_16;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_16, 0);
x_470 = lean_ctor_get(x_16, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_16);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
else
{
uint8_t x_472; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_472 = !lean_is_exclusive(x_11);
if (x_472 == 0)
{
return x_11;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_11, 0);
x_474 = lean_ctor_get(x_11, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_11);
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
return x_475;
}
}
}
else
{
uint8_t x_476; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_476 = !lean_is_exclusive(x_9);
if (x_476 == 0)
{
return x_9;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_9, 0);
x_478 = lean_ctor_get(x_9, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_9);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
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
