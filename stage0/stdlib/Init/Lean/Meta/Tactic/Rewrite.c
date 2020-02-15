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
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__17;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__9;
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__6;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___closed__1;
lean_object* l_Lean_Meta_rewriteCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = l_Lean_Expr_getAppNumArgsAux___main(x_21, x_22);
x_33 = lean_nat_sub(x_32, x_22);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_33, x_34);
lean_dec(x_33);
x_36 = l_Lean_Expr_getRevArg_x21___main(x_21, x_35);
x_37 = lean_nat_sub(x_32, x_34);
x_38 = lean_nat_sub(x_37, x_34);
lean_dec(x_37);
x_39 = l_Lean_Expr_getRevArg_x21___main(x_21, x_38);
x_40 = lean_nat_sub(x_32, x_25);
lean_dec(x_32);
x_41 = lean_nat_sub(x_40, x_34);
lean_dec(x_40);
x_42 = l_Lean_Expr_getRevArg_x21___main(x_21, x_41);
lean_dec(x_21);
if (x_4 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_getAppFn___main(x_39);
x_44 = l_Lean_Expr_isMVar(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_18);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_8);
lean_inc(x_46);
x_48 = l_Lean_Meta_kabstract(x_46, x_39, x_6, x_8, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_114; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_114 = l_Lean_Expr_hasLooseBVars(x_49);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_115 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_116 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_115, x_8, x_50);
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
x_51 = x_50;
goto block_113;
}
block_113:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_expr_instantiate1(x_49, x_42);
lean_dec(x_42);
x_53 = l_Lean_Meta_instantiateMVars(x_52, x_8, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_8);
lean_inc_n(x_46, 2);
x_56 = l_Lean_Meta_mkEq(x_46, x_46, x_8, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Expr_appFn_x21(x_57);
lean_dec(x_57);
x_60 = l_Lean_mkApp(x_59, x_49);
x_61 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_62 = 0;
x_63 = l_Lean_mkLambda(x_61, x_62, x_36, x_60);
lean_inc(x_8);
lean_inc(x_63);
x_98 = l_Lean_Meta_isTypeCorrect(x_63, x_8, x_58);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_63);
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_103 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_102, x_8, x_101);
lean_dec(x_8);
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
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_dec(x_98);
x_64 = x_108;
goto block_97;
}
block_97:
{
lean_object* x_65; 
lean_inc(x_8);
x_65 = l_Lean_Meta_mkEqRefl(x_46, x_8, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_8);
x_68 = l_Lean_Meta_mkEqNDRec(x_63, x_66, x_23, x_8, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_8);
x_71 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_70);
lean_dec(x_20);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_72);
lean_dec(x_8);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_Array_toList___rarg(x_75);
lean_dec(x_75);
x_77 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_76);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_54);
lean_ctor_set(x_78, 1, x_69);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_73, 0, x_78);
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_73, 0);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_73);
x_81 = l_Array_toList___rarg(x_79);
lean_dec(x_79);
x_82 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_81);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_54);
lean_ctor_set(x_83, 1, x_69);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_69);
lean_dec(x_54);
lean_dec(x_19);
lean_dec(x_8);
x_85 = !lean_is_exclusive(x_71);
if (x_85 == 0)
{
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_71, 0);
x_87 = lean_ctor_get(x_71, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_71);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_54);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_68);
if (x_89 == 0)
{
return x_68;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_68, 0);
x_91 = lean_ctor_get(x_68, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_68);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_63);
lean_dec(x_54);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_65);
if (x_93 == 0)
{
return x_65;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_65, 0);
x_95 = lean_ctor_get(x_65, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_65);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_54);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_56);
if (x_109 == 0)
{
return x_56;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_56, 0);
x_111 = lean_ctor_get(x_56, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_56);
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
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_48);
if (x_121 == 0)
{
return x_48;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_48, 0);
x_123 = lean_ctor_get(x_48, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_48);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_125 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_126 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_125, x_8, x_18);
lean_dec(x_8);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_126);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; 
lean_inc(x_8);
x_131 = l_Lean_Meta_mkEqSymm(x_23, x_8, x_18);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_216; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_8);
lean_inc(x_39);
lean_inc(x_42);
x_216 = l_Lean_Meta_mkEq(x_42, x_39, x_8, x_133);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = l_Lean_Expr_getAppFn___main(x_42);
x_219 = l_Lean_Expr_isMVar(x_218);
lean_dec(x_218);
if (x_219 == 0)
{
x_134 = x_217;
goto block_215;
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_132);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_220 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_221 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_220, x_8, x_217);
lean_dec(x_8);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
return x_221;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_221);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_132);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_226 = !lean_is_exclusive(x_216);
if (x_226 == 0)
{
return x_216;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_216, 0);
x_228 = lean_ctor_get(x_216, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_216);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
block_215:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_8);
lean_inc(x_136);
x_138 = l_Lean_Meta_kabstract(x_136, x_42, x_6, x_8, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_204; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_204 = l_Lean_Expr_hasLooseBVars(x_139);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_dec(x_139);
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_19);
x_205 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_206 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_205, x_8, x_140);
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
x_141 = x_140;
goto block_203;
}
block_203:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_expr_instantiate1(x_139, x_39);
lean_dec(x_39);
x_143 = l_Lean_Meta_instantiateMVars(x_142, x_8, x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_8);
lean_inc_n(x_136, 2);
x_146 = l_Lean_Meta_mkEq(x_136, x_136, x_8, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Expr_appFn_x21(x_147);
lean_dec(x_147);
x_150 = l_Lean_mkApp(x_149, x_139);
x_151 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_152 = 0;
x_153 = l_Lean_mkLambda(x_151, x_152, x_36, x_150);
lean_inc(x_8);
lean_inc(x_153);
x_188 = l_Lean_Meta_isTypeCorrect(x_153, x_8, x_148);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
lean_dec(x_153);
lean_dec(x_144);
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_20);
lean_dec(x_19);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_193 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_192, x_8, x_191);
lean_dec(x_8);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
return x_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_193);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
else
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_188, 1);
lean_inc(x_198);
lean_dec(x_188);
x_154 = x_198;
goto block_187;
}
block_187:
{
lean_object* x_155; 
lean_inc(x_8);
x_155 = l_Lean_Meta_mkEqRefl(x_136, x_8, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_8);
x_158 = l_Lean_Meta_mkEqNDRec(x_153, x_156, x_132, x_8, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_8);
x_161 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_160);
lean_dec(x_20);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_162);
lean_dec(x_8);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = l_Array_toList___rarg(x_165);
lean_dec(x_165);
x_167 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_166);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_144);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_167);
lean_ctor_set(x_163, 0, x_168);
return x_163;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_163, 0);
x_170 = lean_ctor_get(x_163, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_163);
x_171 = l_Array_toList___rarg(x_169);
lean_dec(x_169);
x_172 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_171);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_144);
lean_ctor_set(x_173, 1, x_159);
lean_ctor_set(x_173, 2, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
}
else
{
uint8_t x_175; 
lean_dec(x_159);
lean_dec(x_144);
lean_dec(x_19);
lean_dec(x_8);
x_175 = !lean_is_exclusive(x_161);
if (x_175 == 0)
{
return x_161;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_161, 0);
x_177 = lean_ctor_get(x_161, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_161);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_179 = !lean_is_exclusive(x_158);
if (x_179 == 0)
{
return x_158;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_158, 0);
x_181 = lean_ctor_get(x_158, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_158);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_153);
lean_dec(x_144);
lean_dec(x_132);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_183 = !lean_is_exclusive(x_155);
if (x_183 == 0)
{
return x_155;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_155, 0);
x_185 = lean_ctor_get(x_155, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_155);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_144);
lean_dec(x_139);
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_146);
if (x_199 == 0)
{
return x_146;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_146, 0);
x_201 = lean_ctor_get(x_146, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_146);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_211 = !lean_is_exclusive(x_138);
if (x_211 == 0)
{
return x_138;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_138, 0);
x_213 = lean_ctor_get(x_138, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_138);
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
uint8_t x_230; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_230 = !lean_is_exclusive(x_131);
if (x_230 == 0)
{
return x_131;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_131, 0);
x_232 = lean_ctor_get(x_131, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_131);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_234 = l_Lean_Expr_getAppNumArgsAux___main(x_21, x_22);
x_235 = lean_nat_sub(x_234, x_22);
x_236 = lean_unsigned_to_nat(1u);
x_237 = lean_nat_sub(x_235, x_236);
lean_dec(x_235);
x_238 = l_Lean_Expr_getRevArg_x21___main(x_21, x_237);
x_239 = lean_nat_sub(x_234, x_236);
lean_dec(x_234);
x_240 = lean_nat_sub(x_239, x_236);
lean_dec(x_239);
x_241 = l_Lean_Expr_getRevArg_x21___main(x_21, x_240);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_241);
lean_inc(x_238);
x_242 = l_Lean_Meta_mkEq(x_238, x_241, x_8, x_18);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = l_Lean_Meta_rewriteCore___lambda__1___closed__17;
x_246 = l_Lean_mkApp3(x_245, x_238, x_241, x_23);
x_247 = l_Lean_Expr_eq_x3f___closed__2;
x_248 = lean_unsigned_to_nat(3u);
x_249 = l_Lean_Expr_isAppOfArity___main(x_243, x_247, x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_246);
lean_dec(x_243);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_250 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_251 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_250, x_8, x_244);
lean_dec(x_8);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_252 = l_Lean_Expr_getAppNumArgsAux___main(x_243, x_22);
x_253 = lean_nat_sub(x_252, x_22);
x_254 = lean_nat_sub(x_253, x_236);
lean_dec(x_253);
x_255 = l_Lean_Expr_getRevArg_x21___main(x_243, x_254);
x_256 = lean_nat_sub(x_252, x_236);
x_257 = lean_nat_sub(x_256, x_236);
lean_dec(x_256);
x_258 = l_Lean_Expr_getRevArg_x21___main(x_243, x_257);
x_259 = lean_nat_sub(x_252, x_25);
lean_dec(x_252);
x_260 = lean_nat_sub(x_259, x_236);
lean_dec(x_259);
x_261 = l_Lean_Expr_getRevArg_x21___main(x_243, x_260);
lean_dec(x_243);
if (x_4 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = l_Lean_Expr_getAppFn___main(x_258);
x_263 = l_Lean_Expr_isMVar(x_262);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_244);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
lean_inc(x_8);
lean_inc(x_265);
x_267 = l_Lean_Meta_kabstract(x_265, x_258, x_6, x_8, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_333; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_333 = l_Lean_Expr_hasLooseBVars(x_268);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_261);
lean_dec(x_255);
lean_dec(x_246);
lean_dec(x_20);
lean_dec(x_19);
x_334 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_335 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_334, x_8, x_269);
lean_dec(x_8);
x_336 = !lean_is_exclusive(x_335);
if (x_336 == 0)
{
return x_335;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_335, 0);
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_335);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
else
{
x_270 = x_269;
goto block_332;
}
block_332:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_271 = lean_expr_instantiate1(x_268, x_261);
lean_dec(x_261);
x_272 = l_Lean_Meta_instantiateMVars(x_271, x_8, x_270);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_8);
lean_inc_n(x_265, 2);
x_275 = l_Lean_Meta_mkEq(x_265, x_265, x_8, x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l_Lean_Expr_appFn_x21(x_276);
lean_dec(x_276);
x_279 = l_Lean_mkApp(x_278, x_268);
x_280 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_281 = 0;
x_282 = l_Lean_mkLambda(x_280, x_281, x_255, x_279);
lean_inc(x_8);
lean_inc(x_282);
x_317 = l_Lean_Meta_isTypeCorrect(x_282, x_8, x_277);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_unbox(x_318);
lean_dec(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
lean_dec(x_282);
lean_dec(x_273);
lean_dec(x_265);
lean_dec(x_246);
lean_dec(x_20);
lean_dec(x_19);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_322 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_321, x_8, x_320);
lean_dec(x_8);
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
return x_322;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_322, 0);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_322);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
else
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_317, 1);
lean_inc(x_327);
lean_dec(x_317);
x_283 = x_327;
goto block_316;
}
block_316:
{
lean_object* x_284; 
lean_inc(x_8);
x_284 = l_Lean_Meta_mkEqRefl(x_265, x_8, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_8);
x_287 = l_Lean_Meta_mkEqNDRec(x_282, x_285, x_246, x_8, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
lean_inc(x_8);
x_290 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_289);
lean_dec(x_20);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_292 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_291);
lean_dec(x_8);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_ctor_get(x_292, 0);
x_295 = l_Array_toList___rarg(x_294);
lean_dec(x_294);
x_296 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_295);
x_297 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_297, 0, x_273);
lean_ctor_set(x_297, 1, x_288);
lean_ctor_set(x_297, 2, x_296);
lean_ctor_set(x_292, 0, x_297);
return x_292;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_292, 0);
x_299 = lean_ctor_get(x_292, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_292);
x_300 = l_Array_toList___rarg(x_298);
lean_dec(x_298);
x_301 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_300);
x_302 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_302, 0, x_273);
lean_ctor_set(x_302, 1, x_288);
lean_ctor_set(x_302, 2, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_299);
return x_303;
}
}
else
{
uint8_t x_304; 
lean_dec(x_288);
lean_dec(x_273);
lean_dec(x_19);
lean_dec(x_8);
x_304 = !lean_is_exclusive(x_290);
if (x_304 == 0)
{
return x_290;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_290, 0);
x_306 = lean_ctor_get(x_290, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_290);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_273);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_308 = !lean_is_exclusive(x_287);
if (x_308 == 0)
{
return x_287;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_287, 0);
x_310 = lean_ctor_get(x_287, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_287);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_282);
lean_dec(x_273);
lean_dec(x_246);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_312 = !lean_is_exclusive(x_284);
if (x_312 == 0)
{
return x_284;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_284, 0);
x_314 = lean_ctor_get(x_284, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_284);
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
uint8_t x_328; 
lean_dec(x_273);
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_255);
lean_dec(x_246);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_328 = !lean_is_exclusive(x_275);
if (x_328 == 0)
{
return x_275;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_275, 0);
x_330 = lean_ctor_get(x_275, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_275);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_265);
lean_dec(x_261);
lean_dec(x_255);
lean_dec(x_246);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_340 = !lean_is_exclusive(x_267);
if (x_340 == 0)
{
return x_267;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_267, 0);
x_342 = lean_ctor_get(x_267, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_267);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; 
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_246);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_344 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_345 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_344, x_8, x_244);
lean_dec(x_8);
x_346 = !lean_is_exclusive(x_345);
if (x_346 == 0)
{
return x_345;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_345, 0);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_345);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
else
{
lean_object* x_350; 
lean_inc(x_8);
x_350 = l_Lean_Meta_mkEqSymm(x_246, x_8, x_244);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_435; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
lean_inc(x_8);
lean_inc(x_258);
lean_inc(x_261);
x_435 = l_Lean_Meta_mkEq(x_261, x_258, x_8, x_352);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = l_Lean_Expr_getAppFn___main(x_261);
x_438 = l_Lean_Expr_isMVar(x_437);
lean_dec(x_437);
if (x_438 == 0)
{
x_353 = x_436;
goto block_434;
}
else
{
lean_object* x_439; lean_object* x_440; uint8_t x_441; 
lean_dec(x_351);
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_439 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_440 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_439, x_8, x_436);
lean_dec(x_8);
x_441 = !lean_is_exclusive(x_440);
if (x_441 == 0)
{
return x_440;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_440, 0);
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_440);
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
lean_dec(x_351);
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_445 = !lean_is_exclusive(x_435);
if (x_445 == 0)
{
return x_435;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_435, 0);
x_447 = lean_ctor_get(x_435, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_435);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
block_434:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = l_Lean_Meta_instantiateMVars(x_5, x_8, x_353);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
lean_inc(x_8);
lean_inc(x_355);
x_357 = l_Lean_Meta_kabstract(x_355, x_261, x_6, x_8, x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_423; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_423 = l_Lean_Expr_hasLooseBVars(x_358);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; 
lean_dec(x_358);
lean_dec(x_355);
lean_dec(x_351);
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_20);
lean_dec(x_19);
x_424 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_425 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_424, x_8, x_359);
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
x_360 = x_359;
goto block_422;
}
block_422:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_361 = lean_expr_instantiate1(x_358, x_258);
lean_dec(x_258);
x_362 = l_Lean_Meta_instantiateMVars(x_361, x_8, x_360);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
lean_inc(x_8);
lean_inc_n(x_355, 2);
x_365 = l_Lean_Meta_mkEq(x_355, x_355, x_8, x_364);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Expr_appFn_x21(x_366);
lean_dec(x_366);
x_369 = l_Lean_mkApp(x_368, x_358);
x_370 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_371 = 0;
x_372 = l_Lean_mkLambda(x_370, x_371, x_255, x_369);
lean_inc(x_8);
lean_inc(x_372);
x_407 = l_Lean_Meta_isTypeCorrect(x_372, x_8, x_367);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_unbox(x_408);
lean_dec(x_408);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_372);
lean_dec(x_363);
lean_dec(x_355);
lean_dec(x_351);
lean_dec(x_20);
lean_dec(x_19);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_411 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_412 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_411, x_8, x_410);
lean_dec(x_8);
x_413 = !lean_is_exclusive(x_412);
if (x_413 == 0)
{
return x_412;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_412, 0);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_412);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_407, 1);
lean_inc(x_417);
lean_dec(x_407);
x_373 = x_417;
goto block_406;
}
block_406:
{
lean_object* x_374; 
lean_inc(x_8);
x_374 = l_Lean_Meta_mkEqRefl(x_355, x_8, x_373);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
lean_inc(x_8);
x_377 = l_Lean_Meta_mkEqNDRec(x_372, x_375, x_351, x_8, x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
lean_inc(x_8);
x_380 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_19, x_20, x_8, x_379);
lean_dec(x_20);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_382 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_19, x_22, x_22, x_8, x_381);
lean_dec(x_8);
x_383 = !lean_is_exclusive(x_382);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_384 = lean_ctor_get(x_382, 0);
x_385 = l_Array_toList___rarg(x_384);
lean_dec(x_384);
x_386 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_385);
x_387 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_387, 0, x_363);
lean_ctor_set(x_387, 1, x_378);
lean_ctor_set(x_387, 2, x_386);
lean_ctor_set(x_382, 0, x_387);
return x_382;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_388 = lean_ctor_get(x_382, 0);
x_389 = lean_ctor_get(x_382, 1);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_382);
x_390 = l_Array_toList___rarg(x_388);
lean_dec(x_388);
x_391 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__1(x_390);
x_392 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_392, 0, x_363);
lean_ctor_set(x_392, 1, x_378);
lean_ctor_set(x_392, 2, x_391);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_389);
return x_393;
}
}
else
{
uint8_t x_394; 
lean_dec(x_378);
lean_dec(x_363);
lean_dec(x_19);
lean_dec(x_8);
x_394 = !lean_is_exclusive(x_380);
if (x_394 == 0)
{
return x_380;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_380, 0);
x_396 = lean_ctor_get(x_380, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_380);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
}
}
else
{
uint8_t x_398; 
lean_dec(x_363);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_398 = !lean_is_exclusive(x_377);
if (x_398 == 0)
{
return x_377;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_377, 0);
x_400 = lean_ctor_get(x_377, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_377);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
lean_dec(x_372);
lean_dec(x_363);
lean_dec(x_351);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_402 = !lean_is_exclusive(x_374);
if (x_402 == 0)
{
return x_374;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_374, 0);
x_404 = lean_ctor_get(x_374, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_374);
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
uint8_t x_418; 
lean_dec(x_363);
lean_dec(x_358);
lean_dec(x_355);
lean_dec(x_351);
lean_dec(x_255);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_418 = !lean_is_exclusive(x_365);
if (x_418 == 0)
{
return x_365;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_365, 0);
x_420 = lean_ctor_get(x_365, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_365);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_355);
lean_dec(x_351);
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_430 = !lean_is_exclusive(x_357);
if (x_430 == 0)
{
return x_357;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_357, 0);
x_432 = lean_ctor_get(x_357, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_357);
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
uint8_t x_449; 
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_449 = !lean_is_exclusive(x_350);
if (x_449 == 0)
{
return x_350;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_350, 0);
x_451 = lean_ctor_get(x_350, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_350);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
return x_452;
}
}
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_241);
lean_dec(x_238);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_453 = !lean_is_exclusive(x_242);
if (x_453 == 0)
{
return x_242;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_242, 0);
x_455 = lean_ctor_get(x_242, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_242);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
}
else
{
uint8_t x_457; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_457 = !lean_is_exclusive(x_15);
if (x_457 == 0)
{
return x_15;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_15, 0);
x_459 = lean_ctor_get(x_15, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_15);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_461 = !lean_is_exclusive(x_10);
if (x_461 == 0)
{
return x_10;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_10, 0);
x_463 = lean_ctor_get(x_10, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_10);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
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
