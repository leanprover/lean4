// Lean compiler output
// Module: Init.Lean.Meta.Offset
// Imports: Init.Lean.Data.LBool Init.Lean.Meta.InferType
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
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__10;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_3__isOffset(lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__16;
lean_object* l_Lean_Meta_evalNat(lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_2__getOffset(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_5__mkOffset(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__11;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main(lean_object*);
lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__12;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__1;
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux(lean_object*, uint8_t);
lean_object* l_Lean_Meta_evalNat___main___closed__6;
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l_Lean_Meta_evalNat___main___closed__13;
lean_object* l___private_Init_Lean_Meta_Offset_4__isNatZero___boxed(lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__4;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1;
lean_object* l_Lean_Meta_evalNat___main___closed__9;
uint8_t l_Bool_toLBool(uint8_t);
uint8_t l___private_Init_Lean_Meta_Offset_4__isNatZero(lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__17;
lean_object* l_Lean_Meta_evalNat___main___closed__8;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__7;
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(lean_object*, uint8_t);
lean_object* l_Lean_Meta_evalNat___main___closed__15;
lean_object* l_Lean_Meta_evalNat___main___closed__18;
lean_object* l_Lean_Meta_evalNat___main___closed__3;
lean_object* l_Lean_Meta_evalNat___main___closed__5;
lean_object* l_Lean_Meta_evalNat___main___closed__14;
lean_object* l_Lean_Meta_evalNat___main___closed__1;
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Syntax_decodeNatLitVal___closed__1;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
x_1 = lean_mk_string("HasOfNat");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_evalNat___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofNat");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat___main___closed__7;
x_2 = l_Lean_Meta_evalNat___main___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sub");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat___main___closed__3;
x_2 = l_Lean_Meta_evalNat___main___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat___main___closed__3;
x_2 = l_Lean_Meta_evalNat___main___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__17;
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
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Literal_type___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_evalNat___main___closed__1;
x_11 = lean_string_dec_eq(x_5, x_10);
lean_dec(x_5);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_decodeNatLitVal___closed__1;
return x_13;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
}
case 5:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_128; lean_object* x_154; lean_object* x_180; lean_object* x_206; uint8_t x_207; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_20);
x_206 = l_Lean_Meta_evalNat___main___closed__18;
x_207 = lean_name_eq(x_19, x_206);
if (x_207 == 0)
{
lean_object* x_208; 
lean_dec(x_17);
x_208 = lean_box(0);
x_180 = x_208;
goto block_205;
}
else
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_dec_eq(x_21, x_209);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_17);
x_211 = lean_box(0);
x_180 = x_211;
goto block_205;
}
else
{
lean_object* x_212; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
x_212 = l_Lean_Meta_evalNat___main(x_17);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_box(0);
return x_213;
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_212, 0);
x_216 = lean_nat_add(x_215, x_209);
lean_dec(x_215);
lean_ctor_set(x_212, 0, x_216);
return x_212;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_212, 0);
lean_inc(x_217);
lean_dec(x_212);
x_218 = lean_nat_add(x_217, x_209);
lean_dec(x_217);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
}
block_127:
{
lean_object* x_23; lean_object* x_73; lean_object* x_101; uint8_t x_102; 
lean_dec(x_22);
x_101 = l_Lean_Meta_evalNat___main___closed__13;
x_102 = lean_name_eq(x_19, x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_box(0);
x_73 = x_103;
goto block_100;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_unsigned_to_nat(4u);
x_105 = lean_nat_dec_eq(x_21, x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_box(0);
x_73 = x_106;
goto block_100;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_19);
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_nat_sub(x_21, x_107);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_sub(x_108, x_109);
lean_dec(x_108);
x_111 = l_Lean_Expr_getRevArg_x21___main(x_1, x_110);
x_112 = l_Lean_Meta_evalNat___main(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
lean_dec(x_21);
lean_dec(x_1);
x_113 = lean_box(0);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unsigned_to_nat(3u);
x_116 = lean_nat_sub(x_21, x_115);
lean_dec(x_21);
x_117 = lean_nat_sub(x_116, x_109);
lean_dec(x_116);
x_118 = l_Lean_Expr_getRevArg_x21___main(x_1, x_117);
lean_dec(x_1);
x_119 = l_Lean_Meta_evalNat___main(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
lean_dec(x_114);
x_120 = lean_box(0);
return x_120;
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 0);
x_123 = lean_nat_add(x_114, x_122);
lean_dec(x_122);
lean_dec(x_114);
lean_ctor_set(x_119, 0, x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_nat_add(x_114, x_124);
lean_dec(x_124);
lean_dec(x_114);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
}
}
block_72:
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_23);
x_24 = l_Lean_Meta_evalNat___main___closed__5;
x_25 = lean_name_eq(x_19, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_evalNat___main___closed__9;
x_27 = lean_name_eq(x_19, x_26);
lean_dec(x_19);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_1);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_dec_eq(x_21, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_1);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_sub(x_21, x_32);
lean_dec(x_21);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_33, x_34);
lean_dec(x_33);
x_36 = l_Lean_Expr_getRevArg_x21___main(x_1, x_35);
lean_dec(x_1);
x_1 = x_36;
goto _start;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_dec_eq(x_21, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_evalNat___main___closed__9;
x_41 = lean_name_eq(x_19, x_40);
lean_dec(x_19);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_21);
lean_dec(x_1);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_dec_eq(x_21, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_21);
lean_dec(x_1);
x_45 = lean_box(0);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_sub(x_21, x_46);
lean_dec(x_21);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_47, x_48);
lean_dec(x_47);
x_50 = l_Lean_Expr_getRevArg_x21___main(x_1, x_49);
lean_dec(x_1);
x_1 = x_50;
goto _start;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_19);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_sub(x_21, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_53, x_54);
lean_dec(x_53);
x_56 = l_Lean_Expr_getRevArg_x21___main(x_1, x_55);
x_57 = l_Lean_Meta_evalNat___main(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_dec(x_21);
lean_dec(x_1);
x_58 = lean_box(0);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_sub(x_21, x_60);
lean_dec(x_21);
x_62 = lean_nat_sub(x_61, x_54);
lean_dec(x_61);
x_63 = l_Lean_Expr_getRevArg_x21___main(x_1, x_62);
lean_dec(x_1);
x_64 = l_Lean_Meta_evalNat___main(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_59);
x_65 = lean_box(0);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_nat_mul(x_59, x_67);
lean_dec(x_67);
lean_dec(x_59);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_nat_mul(x_59, x_69);
lean_dec(x_69);
lean_dec(x_59);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
}
}
block_100:
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_73);
x_74 = l_Lean_Meta_evalNat___main___closed__11;
x_75 = lean_name_eq(x_19, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_23 = x_76;
goto block_72;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_nat_dec_eq(x_21, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_23 = x_79;
goto block_72;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_19);
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_nat_sub(x_21, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_81, x_82);
lean_dec(x_81);
x_84 = l_Lean_Expr_getRevArg_x21___main(x_1, x_83);
x_85 = l_Lean_Meta_evalNat___main(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec(x_21);
lean_dec(x_1);
x_86 = lean_box(0);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_sub(x_21, x_88);
lean_dec(x_21);
x_90 = lean_nat_sub(x_89, x_82);
lean_dec(x_89);
x_91 = l_Lean_Expr_getRevArg_x21___main(x_1, x_90);
lean_dec(x_1);
x_92 = l_Lean_Meta_evalNat___main(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec(x_87);
x_93 = lean_box(0);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_nat_sub(x_87, x_95);
lean_dec(x_95);
lean_dec(x_87);
lean_ctor_set(x_92, 0, x_96);
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_nat_sub(x_87, x_97);
lean_dec(x_97);
lean_dec(x_87);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
}
}
}
block_153:
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_128);
x_129 = l_Lean_Meta_evalNat___main___closed__14;
x_130 = lean_name_eq(x_19, x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_box(0);
x_22 = x_131;
goto block_127;
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_nat_dec_eq(x_21, x_132);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_22 = x_134;
goto block_127;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_19);
x_135 = lean_nat_sub(x_21, x_20);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_sub(x_135, x_136);
lean_dec(x_135);
x_138 = l_Lean_Expr_getRevArg_x21___main(x_1, x_137);
x_139 = l_Lean_Meta_evalNat___main(x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
lean_dec(x_21);
lean_dec(x_1);
x_140 = lean_box(0);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_nat_sub(x_21, x_136);
lean_dec(x_21);
x_143 = lean_nat_sub(x_142, x_136);
lean_dec(x_142);
x_144 = l_Lean_Expr_getRevArg_x21___main(x_1, x_143);
lean_dec(x_1);
x_145 = l_Lean_Meta_evalNat___main(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
lean_dec(x_141);
x_146 = lean_box(0);
return x_146;
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_145, 0);
x_149 = lean_nat_mul(x_141, x_148);
lean_dec(x_148);
lean_dec(x_141);
lean_ctor_set(x_145, 0, x_149);
return x_145;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
lean_dec(x_145);
x_151 = lean_nat_mul(x_141, x_150);
lean_dec(x_150);
lean_dec(x_141);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
}
}
}
}
block_179:
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_154);
x_155 = l_Lean_Meta_evalNat___main___closed__15;
x_156 = lean_name_eq(x_19, x_155);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_box(0);
x_128 = x_157;
goto block_153;
}
else
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_nat_dec_eq(x_21, x_158);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_box(0);
x_128 = x_160;
goto block_153;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_19);
x_161 = lean_nat_sub(x_21, x_20);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_sub(x_161, x_162);
lean_dec(x_161);
x_164 = l_Lean_Expr_getRevArg_x21___main(x_1, x_163);
x_165 = l_Lean_Meta_evalNat___main(x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
lean_dec(x_21);
lean_dec(x_1);
x_166 = lean_box(0);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_nat_sub(x_21, x_162);
lean_dec(x_21);
x_169 = lean_nat_sub(x_168, x_162);
lean_dec(x_168);
x_170 = l_Lean_Expr_getRevArg_x21___main(x_1, x_169);
lean_dec(x_1);
x_171 = l_Lean_Meta_evalNat___main(x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
lean_dec(x_167);
x_172 = lean_box(0);
return x_172;
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_171, 0);
x_175 = lean_nat_sub(x_167, x_174);
lean_dec(x_174);
lean_dec(x_167);
lean_ctor_set(x_171, 0, x_175);
return x_171;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_171, 0);
lean_inc(x_176);
lean_dec(x_171);
x_177 = lean_nat_sub(x_167, x_176);
lean_dec(x_176);
lean_dec(x_167);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
}
}
}
block_205:
{
lean_object* x_181; uint8_t x_182; 
lean_dec(x_180);
x_181 = l_Lean_Meta_evalNat___main___closed__16;
x_182 = lean_name_eq(x_19, x_181);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = lean_box(0);
x_154 = x_183;
goto block_179;
}
else
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_unsigned_to_nat(2u);
x_185 = lean_nat_dec_eq(x_21, x_184);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_box(0);
x_154 = x_186;
goto block_179;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_19);
x_187 = lean_nat_sub(x_21, x_20);
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_nat_sub(x_187, x_188);
lean_dec(x_187);
x_190 = l_Lean_Expr_getRevArg_x21___main(x_1, x_189);
x_191 = l_Lean_Meta_evalNat___main(x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
lean_dec(x_21);
lean_dec(x_1);
x_192 = lean_box(0);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_nat_sub(x_21, x_188);
lean_dec(x_21);
x_195 = lean_nat_sub(x_194, x_188);
lean_dec(x_194);
x_196 = l_Lean_Expr_getRevArg_x21___main(x_1, x_195);
lean_dec(x_1);
x_197 = l_Lean_Meta_evalNat___main(x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
lean_dec(x_193);
x_198 = lean_box(0);
return x_198;
}
else
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_197, 0);
x_201 = lean_nat_add(x_193, x_200);
lean_dec(x_200);
lean_dec(x_193);
lean_ctor_set(x_197, 0, x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_197, 0);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_nat_add(x_193, x_202);
lean_dec(x_202);
lean_dec(x_193);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
}
}
}
}
else
{
lean_object* x_220; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_220 = lean_box(0);
return x_220;
}
}
case 9:
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_1, 0);
lean_inc(x_221);
lean_dec(x_1);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
else
{
lean_object* x_224; 
lean_dec(x_221);
x_224 = lean_box(0);
return x_224;
}
}
case 10:
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_1, 1);
lean_inc(x_225);
lean_dec(x_1);
x_1 = x_225;
goto _start;
}
default: 
{
lean_object* x_227; 
lean_dec(x_1);
x_227 = lean_box(0);
return x_227;
}
}
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
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_53; lean_object* x_90; uint8_t x_91; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_12);
x_90 = l_Lean_Meta_evalNat___main___closed__18;
x_91 = lean_name_eq(x_11, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_9);
x_92 = lean_box(0);
x_53 = x_92;
goto block_89;
}
else
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_dec_eq(x_13, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_9);
x_95 = lean_box(0);
x_53 = x_95;
goto block_89;
}
else
{
uint8_t x_96; lean_object* x_97; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_96 = 0;
x_97 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_9, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_box(0);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 1);
x_103 = lean_nat_add(x_102, x_93);
lean_dec(x_102);
lean_ctor_set(x_100, 1, x_103);
return x_97;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = lean_nat_add(x_105, x_93);
lean_dec(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_97, 0, x_107);
return x_97;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_97, 0);
lean_inc(x_108);
lean_dec(x_97);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = lean_nat_add(x_110, x_93);
lean_dec(x_110);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
block_52:
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_14);
x_15 = l_Lean_Meta_evalNat___main___closed__13;
x_16 = lean_name_eq(x_11, x_15);
lean_dec(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_box(0);
x_3 = x_17;
goto block_8;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(4u);
x_19 = lean_nat_dec_eq(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_13);
x_20 = lean_box(0);
x_3 = x_20;
goto block_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_sub(x_13, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
lean_dec(x_22);
x_25 = l_Lean_Expr_getRevArg_x21___main(x_1, x_24);
x_26 = l_Lean_Meta_evalNat___main(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_nat_sub(x_13, x_29);
lean_dec(x_13);
x_31 = lean_nat_sub(x_30, x_23);
lean_dec(x_30);
x_32 = l_Lean_Expr_getRevArg_x21___main(x_1, x_31);
lean_dec(x_1);
x_33 = 0;
x_34 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_28);
x_35 = lean_box(0);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_nat_add(x_39, x_28);
lean_dec(x_28);
lean_dec(x_39);
lean_ctor_set(x_37, 1, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_nat_add(x_42, x_28);
lean_dec(x_28);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_34, 0, x_44);
return x_34;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_nat_add(x_47, x_28);
lean_dec(x_28);
lean_dec(x_47);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
}
block_89:
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_53);
x_54 = l_Lean_Meta_evalNat___main___closed__16;
x_55 = lean_name_eq(x_11, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_14 = x_56;
goto block_52;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_nat_dec_eq(x_13, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_14 = x_59;
goto block_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_13, x_60);
x_62 = lean_nat_sub(x_61, x_60);
lean_dec(x_61);
x_63 = l_Lean_Expr_getRevArg_x21___main(x_1, x_62);
x_64 = l_Lean_Meta_evalNat___main(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_13);
lean_dec(x_1);
x_65 = lean_box(0);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_nat_sub(x_13, x_12);
lean_dec(x_13);
x_68 = lean_nat_sub(x_67, x_60);
lean_dec(x_67);
x_69 = l_Lean_Expr_getRevArg_x21___main(x_1, x_68);
lean_dec(x_1);
x_70 = 0;
x_71 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_69, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec(x_66);
x_72 = lean_box(0);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 1);
x_77 = lean_nat_add(x_76, x_66);
lean_dec(x_66);
lean_dec(x_76);
lean_ctor_set(x_74, 1, x_77);
return x_71;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_nat_add(x_79, x_66);
lean_dec(x_66);
lean_dec(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_71, 0, x_81);
return x_71;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_71, 0);
lean_inc(x_82);
lean_dec(x_71);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_nat_add(x_84, x_66);
lean_dec(x_66);
lean_dec(x_84);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
}
}
}
else
{
lean_object* x_115; 
lean_dec(x_10);
lean_dec(x_9);
x_115 = lean_box(0);
x_3 = x_115;
goto block_8;
}
}
else
{
lean_object* x_116; 
x_116 = lean_box(0);
x_3 = x_116;
goto block_8;
}
block_8:
{
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffsetAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_2__getOffset(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 1;
x_3 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_3__isOffset(lean_object* x_1) {
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
x_18 = l_Lean_Meta_evalNat___main___closed__18;
x_19 = lean_name_eq(x_3, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_evalNat___main___closed__16;
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
uint8_t x_25; lean_object* x_26; 
lean_dec(x_5);
lean_dec(x_3);
x_25 = 1;
x_26 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_25);
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
x_29 = l_Lean_Meta_evalNat___main___closed__16;
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
uint8_t x_33; lean_object* x_34; 
lean_dec(x_5);
lean_dec(x_3);
x_33 = 1;
x_34 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_3);
x_35 = 1;
x_36 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_35);
return x_36;
}
}
block_17:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_evalNat___main___closed__13;
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
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_10);
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
uint8_t x_15; lean_object* x_16; 
x_15 = 1;
x_16 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_15);
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
uint8_t l___private_Init_Lean_Meta_Offset_4__isNatZero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_evalNat___main(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
lean_object* l___private_Init_Lean_Meta_Offset_4__isNatZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Meta_Offset_4__isNatZero(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_evalNat___main___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_5__mkOffset(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_Offset_4__isNatZero(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_mkNatLit(x_2);
x_7 = l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1;
x_8 = l_Lean_mkAppB(x_7, x_1, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_mkNatLit(x_2);
return x_9;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Meta_isDefEqOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_Offset_3__isOffset(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Meta_evalNat___main(x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = 2;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Meta_Offset_3__isOffset(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = l_Lean_Meta_evalNat___main(x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_13 = 2;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_nat_dec_eq(x_10, x_16);
lean_dec(x_16);
lean_dec(x_10);
x_18 = l_Bool_toLBool(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_nat_dec_le(x_23, x_10);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_3);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_nat_sub(x_10, x_23);
lean_dec(x_23);
lean_dec(x_10);
x_29 = l_Lean_mkNatLit(x_28);
x_30 = l_Lean_Meta_isExprDefEqAux(x_29, x_22, x_3, x_4);
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
lean_dec(x_1);
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_2);
x_49 = l___private_Init_Lean_Meta_Offset_3__isOffset(x_2);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = l_Lean_Meta_evalNat___main(x_2);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_3);
x_51 = 2;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
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
lean_dec(x_3);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_nat_sub(x_54, x_48);
lean_dec(x_48);
lean_dec(x_54);
x_60 = l_Lean_mkNatLit(x_59);
x_61 = l_Lean_Meta_isExprDefEqAux(x_47, x_60, x_3, x_4);
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
lean_dec(x_2);
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
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_nat_sub(x_48, x_79);
lean_dec(x_79);
lean_dec(x_48);
x_83 = l___private_Init_Lean_Meta_Offset_5__mkOffset(x_47, x_82);
x_84 = l_Lean_Meta_isExprDefEqAux(x_83, x_78, x_3, x_4);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
x_88 = l_Bool_toLBool(x_87);
x_89 = lean_box(x_88);
lean_ctor_set(x_84, 0, x_89);
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_93 = l_Bool_toLBool(x_92);
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_84);
if (x_96 == 0)
{
return x_84;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_84, 0);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_84);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_nat_sub(x_79, x_48);
lean_dec(x_48);
lean_dec(x_79);
x_101 = l___private_Init_Lean_Meta_Offset_5__mkOffset(x_78, x_100);
x_102 = l_Lean_Meta_isExprDefEqAux(x_47, x_101, x_3, x_4);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
x_106 = l_Bool_toLBool(x_105);
x_107 = lean_box(x_106);
lean_ctor_set(x_102, 0, x_107);
return x_102;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_102, 0);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_102);
x_110 = lean_unbox(x_108);
lean_dec(x_108);
x_111 = l_Bool_toLBool(x_110);
x_112 = lean_box(x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
return x_113;
}
}
else
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_102);
if (x_114 == 0)
{
return x_102;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_102, 0);
x_116 = lean_ctor_get(x_102, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_102);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
lean_object* x_118; 
lean_dec(x_79);
lean_dec(x_48);
x_118 = l_Lean_Meta_isExprDefEqAux(x_47, x_78, x_3, x_4);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; uint8_t x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
x_122 = l_Bool_toLBool(x_121);
x_123 = lean_box(x_122);
lean_ctor_set(x_118, 0, x_123);
return x_118;
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_118, 0);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_118);
x_126 = lean_unbox(x_124);
lean_dec(x_124);
x_127 = l_Bool_toLBool(x_126);
x_128 = lean_box(x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_118);
if (x_130 == 0)
{
return x_118;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_118, 0);
x_132 = lean_ctor_get(x_118, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_118);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
}
}
lean_object* initialize_Init_Lean_Data_LBool(lean_object*);
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Offset(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Data_LBool(lean_io_mk_world());
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
l_Lean_Meta_evalNat___main___closed__15 = _init_l_Lean_Meta_evalNat___main___closed__15();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__15);
l_Lean_Meta_evalNat___main___closed__16 = _init_l_Lean_Meta_evalNat___main___closed__16();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__16);
l_Lean_Meta_evalNat___main___closed__17 = _init_l_Lean_Meta_evalNat___main___closed__17();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__17);
l_Lean_Meta_evalNat___main___closed__18 = _init_l_Lean_Meta_evalNat___main___closed__18();
lean_mark_persistent(l_Lean_Meta_evalNat___main___closed__18);
l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1 = _init_l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
