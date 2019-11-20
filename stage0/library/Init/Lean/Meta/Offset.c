// Lean compiler output
// Module: Init.Lean.Meta.Offset
// Imports: Init.Lean.LBool Init.Lean.Meta.InferType
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
lean_object* l_Lean_mkCAppB(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqOffset___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__10;
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffset___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffset(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__11;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main(lean_object*);
lean_object* l_Lean_Meta_isDefEqOffset(lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__12;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__1;
lean_object* l_Lean_Meta_evalNat___main___closed__6;
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l_Lean_Meta_evalNat___main___closed__13;
lean_object* l_Lean_Meta_evalNat___main___closed__4;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__9;
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_Meta_evalNat___main___closed__8;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__7;
lean_object* l_Lean_Meta_evalNat___boxed(lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__3;
lean_object* l_Lean_Meta_evalNat___main___closed__5;
lean_object* l_Lean_Meta_evalNat___main___closed__14;
lean_object* l_Lean_Meta_evalNat___main___closed__1;
lean_object* l_Lean_Meta_evalNat___main___boxed(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_2__isOffset(lean_object*);
extern lean_object* l___private_Init_Lean_Syntax_9__decodeNatLitVal___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Meta_evalNat___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasAdd");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_evalNat___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mul");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat___main___closed__3;
x_2 = l_Lean_Meta_evalNat___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sub");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat___main___closed__3;
x_2 = l_Lean_Meta_evalNat___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat___main___closed__3;
x_2 = l_Lean_Meta_evalNat___main___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_evalNat___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Literal_type___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_evalNat___main___closed__1;
x_11 = lean_string_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l___private_Init_Lean_Syntax_9__decodeNatLitVal___closed__1;
return x_13;
}
}
}
else
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
}
case 5:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_106; lean_object* x_132; lean_object* x_158; lean_object* x_184; uint8_t x_185; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_20);
x_184 = l_Lean_Meta_evalNat___main___closed__14;
x_185 = lean_name_eq(x_19, x_184);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_box(0);
x_158 = x_186;
goto block_183;
}
else
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_nat_dec_eq(x_21, x_187);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_box(0);
x_158 = x_189;
goto block_183;
}
else
{
lean_object* x_190; 
lean_dec(x_21);
lean_dec(x_19);
x_190 = l_Lean_Meta_evalNat___main(x_17);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
x_191 = lean_box(0);
return x_191;
}
else
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_190);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_190, 0);
x_194 = lean_nat_add(x_193, x_187);
lean_dec(x_193);
lean_ctor_set(x_190, 0, x_194);
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_190, 0);
lean_inc(x_195);
lean_dec(x_190);
x_196 = lean_nat_add(x_195, x_187);
lean_dec(x_195);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
}
}
block_105:
{
lean_object* x_23; lean_object* x_51; lean_object* x_79; uint8_t x_80; 
lean_dec(x_22);
x_79 = l_Lean_Meta_evalNat___main___closed__9;
x_80 = lean_name_eq(x_19, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_box(0);
x_51 = x_81;
goto block_78;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_nat_dec_eq(x_21, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_box(0);
x_51 = x_84;
goto block_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_19);
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_sub(x_21, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_86, x_87);
lean_dec(x_86);
x_89 = l_Lean_Expr_getRevArg_x21___main(x_1, x_88);
x_90 = l_Lean_Meta_evalNat___main(x_89);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec(x_21);
x_91 = lean_box(0);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_sub(x_21, x_93);
lean_dec(x_21);
x_95 = lean_nat_sub(x_94, x_87);
lean_dec(x_94);
x_96 = l_Lean_Expr_getRevArg_x21___main(x_1, x_95);
x_97 = l_Lean_Meta_evalNat___main(x_96);
lean_dec(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_box(0);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = lean_nat_add(x_92, x_100);
lean_dec(x_100);
lean_dec(x_92);
lean_ctor_set(x_97, 0, x_101);
return x_97;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
lean_dec(x_97);
x_103 = lean_nat_add(x_92, x_102);
lean_dec(x_102);
lean_dec(x_92);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
}
block_50:
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_23);
x_24 = l_Lean_Meta_evalNat___main___closed__5;
x_25 = lean_name_eq(x_19, x_24);
lean_dec(x_19);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_dec_eq(x_21, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_21);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_21, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_31, x_32);
lean_dec(x_31);
x_34 = l_Lean_Expr_getRevArg_x21___main(x_1, x_33);
x_35 = l_Lean_Meta_evalNat___main(x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_21);
x_36 = lean_box(0);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_sub(x_21, x_38);
lean_dec(x_21);
x_40 = lean_nat_sub(x_39, x_32);
lean_dec(x_39);
x_41 = l_Lean_Expr_getRevArg_x21___main(x_1, x_40);
x_42 = l_Lean_Meta_evalNat___main(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_box(0);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_nat_mul(x_37, x_45);
lean_dec(x_45);
lean_dec(x_37);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_nat_mul(x_37, x_47);
lean_dec(x_47);
lean_dec(x_37);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
}
}
block_78:
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_51);
x_52 = l_Lean_Meta_evalNat___main___closed__7;
x_53 = lean_name_eq(x_19, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_23 = x_54;
goto block_50;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_nat_dec_eq(x_21, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_23 = x_57;
goto block_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_19);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_nat_sub(x_21, x_58);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_59, x_60);
lean_dec(x_59);
x_62 = l_Lean_Expr_getRevArg_x21___main(x_1, x_61);
x_63 = l_Lean_Meta_evalNat___main(x_62);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec(x_21);
x_64 = lean_box(0);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_sub(x_21, x_66);
lean_dec(x_21);
x_68 = lean_nat_sub(x_67, x_60);
lean_dec(x_67);
x_69 = l_Lean_Expr_getRevArg_x21___main(x_1, x_68);
x_70 = l_Lean_Meta_evalNat___main(x_69);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_dec(x_65);
x_71 = lean_box(0);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_nat_sub(x_65, x_73);
lean_dec(x_73);
lean_dec(x_65);
lean_ctor_set(x_70, 0, x_74);
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_nat_sub(x_65, x_75);
lean_dec(x_75);
lean_dec(x_65);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
}
}
}
block_131:
{
lean_object* x_107; uint8_t x_108; 
lean_dec(x_106);
x_107 = l_Lean_Meta_evalNat___main___closed__10;
x_108 = lean_name_eq(x_19, x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_box(0);
x_22 = x_109;
goto block_105;
}
else
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_unsigned_to_nat(2u);
x_111 = lean_nat_dec_eq(x_21, x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_box(0);
x_22 = x_112;
goto block_105;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_19);
x_113 = lean_nat_sub(x_21, x_20);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_sub(x_113, x_114);
lean_dec(x_113);
x_116 = l_Lean_Expr_getRevArg_x21___main(x_1, x_115);
x_117 = l_Lean_Meta_evalNat___main(x_116);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
lean_dec(x_21);
x_118 = lean_box(0);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_nat_sub(x_21, x_114);
lean_dec(x_21);
x_121 = lean_nat_sub(x_120, x_114);
lean_dec(x_120);
x_122 = l_Lean_Expr_getRevArg_x21___main(x_1, x_121);
x_123 = l_Lean_Meta_evalNat___main(x_122);
lean_dec(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
lean_dec(x_119);
x_124 = lean_box(0);
return x_124;
}
else
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_123);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_123, 0);
x_127 = lean_nat_mul(x_119, x_126);
lean_dec(x_126);
lean_dec(x_119);
lean_ctor_set(x_123, 0, x_127);
return x_123;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_123, 0);
lean_inc(x_128);
lean_dec(x_123);
x_129 = lean_nat_mul(x_119, x_128);
lean_dec(x_128);
lean_dec(x_119);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
}
}
block_157:
{
lean_object* x_133; uint8_t x_134; 
lean_dec(x_132);
x_133 = l_Lean_Meta_evalNat___main___closed__11;
x_134 = lean_name_eq(x_19, x_133);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_box(0);
x_106 = x_135;
goto block_131;
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_unsigned_to_nat(2u);
x_137 = lean_nat_dec_eq(x_21, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_box(0);
x_106 = x_138;
goto block_131;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_19);
x_139 = lean_nat_sub(x_21, x_20);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_139, x_140);
lean_dec(x_139);
x_142 = l_Lean_Expr_getRevArg_x21___main(x_1, x_141);
x_143 = l_Lean_Meta_evalNat___main(x_142);
lean_dec(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_dec(x_21);
x_144 = lean_box(0);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_nat_sub(x_21, x_140);
lean_dec(x_21);
x_147 = lean_nat_sub(x_146, x_140);
lean_dec(x_146);
x_148 = l_Lean_Expr_getRevArg_x21___main(x_1, x_147);
x_149 = l_Lean_Meta_evalNat___main(x_148);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
lean_dec(x_145);
x_150 = lean_box(0);
return x_150;
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_149, 0);
x_153 = lean_nat_sub(x_145, x_152);
lean_dec(x_152);
lean_dec(x_145);
lean_ctor_set(x_149, 0, x_153);
return x_149;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_149, 0);
lean_inc(x_154);
lean_dec(x_149);
x_155 = lean_nat_sub(x_145, x_154);
lean_dec(x_154);
lean_dec(x_145);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
}
}
}
block_183:
{
lean_object* x_159; uint8_t x_160; 
lean_dec(x_158);
x_159 = l_Lean_Meta_evalNat___main___closed__12;
x_160 = lean_name_eq(x_19, x_159);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_box(0);
x_132 = x_161;
goto block_157;
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_unsigned_to_nat(2u);
x_163 = lean_nat_dec_eq(x_21, x_162);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_box(0);
x_132 = x_164;
goto block_157;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_19);
x_165 = lean_nat_sub(x_21, x_20);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
lean_dec(x_165);
x_168 = l_Lean_Expr_getRevArg_x21___main(x_1, x_167);
x_169 = l_Lean_Meta_evalNat___main(x_168);
lean_dec(x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
lean_dec(x_21);
x_170 = lean_box(0);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_nat_sub(x_21, x_166);
lean_dec(x_21);
x_173 = lean_nat_sub(x_172, x_166);
lean_dec(x_172);
x_174 = l_Lean_Expr_getRevArg_x21___main(x_1, x_173);
x_175 = l_Lean_Meta_evalNat___main(x_174);
lean_dec(x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
lean_dec(x_171);
x_176 = lean_box(0);
return x_176;
}
else
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_175);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_175, 0);
x_179 = lean_nat_add(x_171, x_178);
lean_dec(x_178);
lean_dec(x_171);
lean_ctor_set(x_175, 0, x_179);
return x_175;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_175, 0);
lean_inc(x_180);
lean_dec(x_175);
x_181 = lean_nat_add(x_171, x_180);
lean_dec(x_180);
lean_dec(x_171);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
}
}
}
}
}
else
{
lean_object* x_198; 
lean_dec(x_18);
x_198 = lean_box(0);
return x_198;
}
}
case 9:
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
else
{
lean_object* x_202; 
x_202 = lean_box(0);
return x_202;
}
}
case 10:
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_1, 1);
x_1 = x_203;
goto _start;
}
default: 
{
lean_object* x_205; 
x_205 = lean_box(0);
return x_205;
}
}
}
}
lean_object* l_Lean_Meta_evalNat___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_evalNat___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_evalNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_evalNat___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_evalNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_evalNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffset___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_34; lean_object* x_60; uint8_t x_61; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_5);
x_60 = l_Lean_Meta_evalNat___main___closed__14;
x_61 = lean_name_eq(x_4, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_2);
x_62 = lean_box(0);
x_34 = x_62;
goto block_59;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_dec_eq(x_6, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_2);
x_65 = lean_box(0);
x_34 = x_65;
goto block_59;
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_66 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_2);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 1);
x_69 = lean_nat_add(x_68, x_63);
lean_dec(x_68);
lean_ctor_set(x_66, 1, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_nat_add(x_71, x_63);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
block_33:
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = l_Lean_Meta_evalNat___main___closed__9;
x_9 = lean_name_eq(x_4, x_8);
lean_dec(x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(4u);
x_12 = lean_nat_dec_eq(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_sub(x_6, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = l_Lean_Expr_getRevArg_x21___main(x_1, x_17);
x_19 = l_Lean_Meta_evalNat___main(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_sub(x_6, x_5);
lean_dec(x_6);
x_23 = lean_nat_sub(x_22, x_16);
lean_dec(x_22);
x_24 = l_Lean_Expr_getRevArg_x21___main(x_1, x_23);
lean_dec(x_1);
x_25 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_nat_add(x_27, x_21);
lean_dec(x_21);
lean_dec(x_27);
lean_ctor_set(x_25, 1, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_nat_add(x_30, x_21);
lean_dec(x_21);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
block_59:
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_34);
x_35 = l_Lean_Meta_evalNat___main___closed__12;
x_36 = lean_name_eq(x_4, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_7 = x_37;
goto block_33;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_dec_eq(x_6, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_7 = x_40;
goto block_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_6, x_41);
x_43 = lean_nat_sub(x_42, x_41);
lean_dec(x_42);
x_44 = l_Lean_Expr_getRevArg_x21___main(x_1, x_43);
x_45 = l_Lean_Meta_evalNat___main(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
lean_dec(x_6);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_nat_sub(x_6, x_5);
lean_dec(x_6);
x_49 = lean_nat_sub(x_48, x_41);
lean_dec(x_48);
x_50 = l_Lean_Expr_getRevArg_x21___main(x_1, x_49);
lean_dec(x_1);
x_51 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_50);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
x_54 = lean_nat_add(x_53, x_47);
lean_dec(x_47);
lean_dec(x_53);
lean_ctor_set(x_51, 1, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_nat_add(x_56, x_47);
lean_dec(x_47);
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_2__isOffset(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_18; uint8_t x_19; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_4);
x_18 = l_Lean_Meta_evalNat___main___closed__14;
x_19 = lean_name_eq(x_3, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_evalNat___main___closed__12;
x_21 = lean_name_eq(x_3, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = 0;
x_6 = x_22;
goto block_17;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_dec_eq(x_5, x_23);
if (x_24 == 0)
{
x_6 = x_24;
goto block_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
lean_dec(x_3);
x_25 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_dec_eq(x_5, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Meta_evalNat___main___closed__12;
x_30 = lean_name_eq(x_3, x_29);
if (x_30 == 0)
{
x_6 = x_28;
goto block_17;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_dec_eq(x_5, x_31);
if (x_32 == 0)
{
x_6 = x_32;
goto block_17;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
lean_dec(x_3);
x_33 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_3);
x_35 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
block_17:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_evalNat___main___closed__9;
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_3);
if (x_8 == 0)
{
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = lean_nat_dec_eq(x_5, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_1);
x_38 = lean_box(0);
return x_38;
}
}
}
lean_object* l_Lean_Meta_isDefEqOffset___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l___private_Init_Lean_Meta_Offset_2__isOffset(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat___main(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 2;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_3);
x_12 = l___private_Init_Lean_Meta_Offset_2__isOffset(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Meta_evalNat___main(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_14 = 2;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_nat_dec_eq(x_11, x_17);
lean_dec(x_17);
lean_dec(x_11);
x_19 = l_Bool_toLBool(x_18);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_nat_dec_le(x_23, x_11);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_nat_sub(x_11, x_23);
lean_dec(x_23);
lean_dec(x_11);
x_29 = l_Lean_mkNatLit(x_28);
x_30 = lean_apply_4(x_1, x_2, x_29, x_4, x_5);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_Bool_toLBool(x_33);
x_35 = lean_box(x_34);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_39 = l_Bool_toLBool(x_38);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_6, 0);
lean_inc(x_46);
lean_dec(x_6);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_3);
x_49 = l___private_Init_Lean_Meta_Offset_2__isOffset(x_3);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = l_Lean_Meta_evalNat___main(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_4);
lean_dec(x_1);
x_51 = 2;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_5);
return x_53;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_nat_dec_le(x_48, x_54);
if (x_55 == 0)
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_4);
lean_dec(x_1);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_nat_sub(x_54, x_48);
lean_dec(x_48);
lean_dec(x_54);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = lean_apply_4(x_1, x_47, x_60, x_4, x_5);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
x_65 = l_Bool_toLBool(x_64);
x_66 = lean_box(x_65);
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_70 = l_Bool_toLBool(x_69);
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
return x_61;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_61);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_3);
x_77 = lean_ctor_get(x_49, 0);
lean_inc(x_77);
lean_dec(x_49);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_nat_dec_eq(x_48, x_79);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = lean_nat_dec_lt(x_48, x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_nat_sub(x_48, x_79);
lean_dec(x_79);
lean_dec(x_48);
x_83 = l_Lean_mkNatLit(x_82);
x_84 = l_Lean_Meta_evalNat___main___closed__12;
x_85 = l_Lean_mkCAppB(x_84, x_47, x_83);
x_86 = lean_apply_4(x_1, x_85, x_78, x_4, x_5);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
x_90 = l_Bool_toLBool(x_89);
x_91 = lean_box(x_90);
lean_ctor_set(x_86, 0, x_91);
return x_86;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_86, 0);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_86);
x_94 = lean_unbox(x_92);
lean_dec(x_92);
x_95 = l_Bool_toLBool(x_94);
x_96 = lean_box(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_86);
if (x_98 == 0)
{
return x_86;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_86, 0);
x_100 = lean_ctor_get(x_86, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_86);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_nat_sub(x_79, x_48);
lean_dec(x_48);
lean_dec(x_79);
x_103 = l_Lean_mkNatLit(x_102);
x_104 = l_Lean_Meta_evalNat___main___closed__12;
x_105 = l_Lean_mkCAppB(x_104, x_78, x_103);
x_106 = lean_apply_4(x_1, x_47, x_105, x_4, x_5);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
x_110 = l_Bool_toLBool(x_109);
x_111 = lean_box(x_110);
lean_ctor_set(x_106, 0, x_111);
return x_106;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_106, 0);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_106);
x_114 = lean_unbox(x_112);
lean_dec(x_112);
x_115 = l_Bool_toLBool(x_114);
x_116 = lean_box(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_113);
return x_117;
}
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_106);
if (x_118 == 0)
{
return x_106;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_106, 0);
x_120 = lean_ctor_get(x_106, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_106);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_79);
lean_dec(x_48);
x_122 = lean_apply_4(x_1, x_47, x_78, x_4, x_5);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
x_126 = l_Bool_toLBool(x_125);
x_127 = lean_box(x_126);
lean_ctor_set(x_122, 0, x_127);
return x_122;
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_122, 0);
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_122);
x_130 = lean_unbox(x_128);
lean_dec(x_128);
x_131 = l_Bool_toLBool(x_130);
x_132 = lean_box(x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_129);
return x_133;
}
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_122);
if (x_134 == 0)
{
return x_122;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_122, 0);
x_136 = lean_ctor_get(x_122, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_122);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_isDefEqOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isDefEqOffset___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_isDefEqOffset(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_LBool(lean_object*);
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Offset(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_LBool(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_evalNat___main___closed__1 = _init_l_Lean_Meta_evalNat___main___closed__1();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__1);
l_Lean_Meta_evalNat___main___closed__2 = _init_l_Lean_Meta_evalNat___main___closed__2();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__2);
l_Lean_Meta_evalNat___main___closed__3 = _init_l_Lean_Meta_evalNat___main___closed__3();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__3);
l_Lean_Meta_evalNat___main___closed__4 = _init_l_Lean_Meta_evalNat___main___closed__4();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__4);
l_Lean_Meta_evalNat___main___closed__5 = _init_l_Lean_Meta_evalNat___main___closed__5();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__5);
l_Lean_Meta_evalNat___main___closed__6 = _init_l_Lean_Meta_evalNat___main___closed__6();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__6);
l_Lean_Meta_evalNat___main___closed__7 = _init_l_Lean_Meta_evalNat___main___closed__7();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__7);
l_Lean_Meta_evalNat___main___closed__8 = _init_l_Lean_Meta_evalNat___main___closed__8();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__8);
l_Lean_Meta_evalNat___main___closed__9 = _init_l_Lean_Meta_evalNat___main___closed__9();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__9);
l_Lean_Meta_evalNat___main___closed__10 = _init_l_Lean_Meta_evalNat___main___closed__10();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__10);
l_Lean_Meta_evalNat___main___closed__11 = _init_l_Lean_Meta_evalNat___main___closed__11();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__11);
l_Lean_Meta_evalNat___main___closed__12 = _init_l_Lean_Meta_evalNat___main___closed__12();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__12);
l_Lean_Meta_evalNat___main___closed__13 = _init_l_Lean_Meta_evalNat___main___closed__13();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__13);
l_Lean_Meta_evalNat___main___closed__14 = _init_l_Lean_Meta_evalNat___main___closed__14();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__14);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
