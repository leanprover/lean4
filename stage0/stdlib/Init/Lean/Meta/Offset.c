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
uint8_t l_coeDecidableEq(uint8_t);
extern lean_object* l_Lean_Literal_type___closed__2;
extern uint8_t l_String_posOfAux___main___closed__2;
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Lean_Meta_evalNat___main___closed__13;
lean_object* l___private_Init_Lean_Meta_Offset_4__isNatZero___boxed(lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__4;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1;
lean_object* l_Lean_Meta_evalNat___main___closed__9;
uint8_t l_Bool_toLBool(uint8_t);
extern lean_object* l___private_Init_LeanInit_11__decodeNatLitVal___closed__1;
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
x_1 = lean_mk_string("HasOfNat");
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
x_1 = lean_mk_string("ofNat");
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
x_1 = lean_mk_string("HasAdd");
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
x_1 = lean_mk_string("mul");
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
x_1 = l_Lean_Meta_evalNat___main___closed__7;
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
x_1 = l_Lean_Meta_evalNat___main___closed__7;
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
x_2 = l_Lean_Meta_evalNat___main___closed__8;
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
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__12;
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
x_13 = l___private_Init_LeanInit_11__decodeNatLitVal___closed__1;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_65; uint8_t x_147; uint8_t x_173; lean_object* x_199; uint8_t x_200; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_20);
x_199 = l_Lean_Meta_evalNat___main___closed__17;
x_200 = lean_name_eq(x_19, x_199);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = l_String_posOfAux___main___closed__1;
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
lean_dec(x_17);
x_202 = l_Lean_Meta_evalNat___main___closed__18;
x_203 = lean_name_eq(x_19, x_202);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = 0;
x_173 = x_204;
goto block_198;
}
else
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_unsigned_to_nat(2u);
x_206 = lean_nat_dec_eq(x_21, x_205);
x_173 = x_206;
goto block_198;
}
}
else
{
lean_object* x_207; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
x_207 = l_Lean_Meta_evalNat___main(x_17);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_box(0);
return x_208;
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_207);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_207, 0);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_add(x_210, x_211);
lean_dec(x_210);
lean_ctor_set(x_207, 0, x_212);
return x_207;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_207, 0);
lean_inc(x_213);
lean_dec(x_207);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_add(x_213, x_214);
lean_dec(x_213);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
}
}
else
{
lean_object* x_217; uint8_t x_218; uint8_t x_219; 
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_dec_eq(x_21, x_217);
x_219 = l_coeDecidableEq(x_218);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
lean_dec(x_17);
x_220 = l_Lean_Meta_evalNat___main___closed__18;
x_221 = lean_name_eq(x_19, x_220);
if (x_221 == 0)
{
uint8_t x_222; 
x_222 = 0;
x_173 = x_222;
goto block_198;
}
else
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_unsigned_to_nat(2u);
x_224 = lean_nat_dec_eq(x_21, x_223);
x_173 = x_224;
goto block_198;
}
}
else
{
lean_object* x_225; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
x_225 = l_Lean_Meta_evalNat___main(x_17);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_box(0);
return x_226;
}
else
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_225);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_225, 0);
x_229 = lean_nat_add(x_228, x_217);
lean_dec(x_228);
lean_ctor_set(x_225, 0, x_229);
return x_225;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_225, 0);
lean_inc(x_230);
lean_dec(x_225);
x_231 = lean_nat_add(x_230, x_217);
lean_dec(x_230);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
}
}
}
block_64:
{
uint8_t x_23; 
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Meta_evalNat___main___closed__5;
x_25 = lean_name_eq(x_19, x_24);
lean_dec(x_19);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_String_posOfAux___main___closed__1;
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_sub(x_21, x_28);
lean_dec(x_21);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
x_32 = l_Lean_Expr_getRevArg_x21___main(x_1, x_31);
lean_dec(x_1);
x_1 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_36; 
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_nat_dec_eq(x_21, x_34);
x_36 = l_coeDecidableEq(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_21);
lean_dec(x_1);
x_37 = lean_box(0);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_sub(x_21, x_38);
lean_dec(x_21);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_39, x_40);
lean_dec(x_39);
x_42 = l_Lean_Expr_getRevArg_x21___main(x_1, x_41);
lean_dec(x_1);
x_1 = x_42;
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_19);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_sub(x_21, x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_45, x_46);
lean_dec(x_45);
x_48 = l_Lean_Expr_getRevArg_x21___main(x_1, x_47);
x_49 = l_Lean_Meta_evalNat___main(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec(x_21);
lean_dec(x_1);
x_50 = lean_box(0);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_nat_sub(x_21, x_52);
lean_dec(x_21);
x_54 = lean_nat_sub(x_53, x_46);
lean_dec(x_53);
x_55 = l_Lean_Expr_getRevArg_x21___main(x_1, x_54);
lean_dec(x_1);
x_56 = l_Lean_Meta_evalNat___main(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_51);
x_57 = lean_box(0);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_nat_mul(x_51, x_59);
lean_dec(x_59);
lean_dec(x_51);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_nat_mul(x_51, x_61);
lean_dec(x_61);
lean_dec(x_51);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
block_146:
{
uint8_t x_66; 
x_66 = l_coeDecidableEq(x_65);
if (x_66 == 0)
{
uint8_t x_67; uint8_t x_95; lean_object* x_123; uint8_t x_124; 
x_123 = l_Lean_Meta_evalNat___main___closed__13;
x_124 = lean_name_eq(x_19, x_123);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = 0;
x_95 = x_125;
goto block_122;
}
else
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_unsigned_to_nat(4u);
x_127 = lean_nat_dec_eq(x_21, x_126);
x_95 = x_127;
goto block_122;
}
block_94:
{
uint8_t x_68; 
x_68 = l_coeDecidableEq(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_Meta_evalNat___main___closed__9;
x_70 = lean_name_eq(x_19, x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = 0;
x_22 = x_71;
goto block_64;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_unsigned_to_nat(4u);
x_73 = lean_nat_dec_eq(x_21, x_72);
x_22 = x_73;
goto block_64;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_19);
x_74 = lean_unsigned_to_nat(2u);
x_75 = lean_nat_sub(x_21, x_74);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_sub(x_75, x_76);
lean_dec(x_75);
x_78 = l_Lean_Expr_getRevArg_x21___main(x_1, x_77);
x_79 = l_Lean_Meta_evalNat___main(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec(x_21);
lean_dec(x_1);
x_80 = lean_box(0);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_unsigned_to_nat(3u);
x_83 = lean_nat_sub(x_21, x_82);
lean_dec(x_21);
x_84 = lean_nat_sub(x_83, x_76);
lean_dec(x_83);
x_85 = l_Lean_Expr_getRevArg_x21___main(x_1, x_84);
lean_dec(x_1);
x_86 = l_Lean_Meta_evalNat___main(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec(x_81);
x_87 = lean_box(0);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_nat_sub(x_81, x_89);
lean_dec(x_89);
lean_dec(x_81);
lean_ctor_set(x_86, 0, x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_nat_sub(x_81, x_91);
lean_dec(x_91);
lean_dec(x_81);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
}
}
block_122:
{
uint8_t x_96; 
x_96 = l_coeDecidableEq(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = l_Lean_Meta_evalNat___main___closed__11;
x_98 = lean_name_eq(x_19, x_97);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_67 = x_99;
goto block_94;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_unsigned_to_nat(4u);
x_101 = lean_nat_dec_eq(x_21, x_100);
x_67 = x_101;
goto block_94;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_19);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_sub(x_21, x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_103, x_104);
lean_dec(x_103);
x_106 = l_Lean_Expr_getRevArg_x21___main(x_1, x_105);
x_107 = l_Lean_Meta_evalNat___main(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_21);
lean_dec(x_1);
x_108 = lean_box(0);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_unsigned_to_nat(3u);
x_111 = lean_nat_sub(x_21, x_110);
lean_dec(x_21);
x_112 = lean_nat_sub(x_111, x_104);
lean_dec(x_111);
x_113 = l_Lean_Expr_getRevArg_x21___main(x_1, x_112);
lean_dec(x_1);
x_114 = l_Lean_Meta_evalNat___main(x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
lean_dec(x_109);
x_115 = lean_box(0);
return x_115;
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_114);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_114, 0);
x_118 = lean_nat_add(x_109, x_117);
lean_dec(x_117);
lean_dec(x_109);
lean_ctor_set(x_114, 0, x_118);
return x_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
lean_dec(x_114);
x_120 = lean_nat_add(x_109, x_119);
lean_dec(x_119);
lean_dec(x_109);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_19);
x_128 = lean_nat_sub(x_21, x_20);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_sub(x_128, x_129);
lean_dec(x_128);
x_131 = l_Lean_Expr_getRevArg_x21___main(x_1, x_130);
x_132 = l_Lean_Meta_evalNat___main(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
lean_dec(x_21);
lean_dec(x_1);
x_133 = lean_box(0);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_nat_sub(x_21, x_129);
lean_dec(x_21);
x_136 = lean_nat_sub(x_135, x_129);
lean_dec(x_135);
x_137 = l_Lean_Expr_getRevArg_x21___main(x_1, x_136);
lean_dec(x_1);
x_138 = l_Lean_Meta_evalNat___main(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
lean_dec(x_134);
x_139 = lean_box(0);
return x_139;
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 0);
x_142 = lean_nat_mul(x_134, x_141);
lean_dec(x_141);
lean_dec(x_134);
lean_ctor_set(x_138, 0, x_142);
return x_138;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_138, 0);
lean_inc(x_143);
lean_dec(x_138);
x_144 = lean_nat_mul(x_134, x_143);
lean_dec(x_143);
lean_dec(x_134);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
}
}
}
block_172:
{
uint8_t x_148; 
x_148 = l_coeDecidableEq(x_147);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = l_Lean_Meta_evalNat___main___closed__14;
x_150 = lean_name_eq(x_19, x_149);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = 0;
x_65 = x_151;
goto block_146;
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_unsigned_to_nat(2u);
x_153 = lean_nat_dec_eq(x_21, x_152);
x_65 = x_153;
goto block_146;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_19);
x_154 = lean_nat_sub(x_21, x_20);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_sub(x_154, x_155);
lean_dec(x_154);
x_157 = l_Lean_Expr_getRevArg_x21___main(x_1, x_156);
x_158 = l_Lean_Meta_evalNat___main(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
lean_dec(x_21);
lean_dec(x_1);
x_159 = lean_box(0);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_nat_sub(x_21, x_155);
lean_dec(x_21);
x_162 = lean_nat_sub(x_161, x_155);
lean_dec(x_161);
x_163 = l_Lean_Expr_getRevArg_x21___main(x_1, x_162);
lean_dec(x_1);
x_164 = l_Lean_Meta_evalNat___main(x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec(x_160);
x_165 = lean_box(0);
return x_165;
}
else
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_164);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_164, 0);
x_168 = lean_nat_sub(x_160, x_167);
lean_dec(x_167);
lean_dec(x_160);
lean_ctor_set(x_164, 0, x_168);
return x_164;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
lean_dec(x_164);
x_170 = lean_nat_sub(x_160, x_169);
lean_dec(x_169);
lean_dec(x_160);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
}
}
}
}
block_198:
{
uint8_t x_174; 
x_174 = l_coeDecidableEq(x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_Lean_Meta_evalNat___main___closed__15;
x_176 = lean_name_eq(x_19, x_175);
if (x_176 == 0)
{
uint8_t x_177; 
x_177 = 0;
x_147 = x_177;
goto block_172;
}
else
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_dec_eq(x_21, x_178);
x_147 = x_179;
goto block_172;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_19);
x_180 = lean_nat_sub(x_21, x_20);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_sub(x_180, x_181);
lean_dec(x_180);
x_183 = l_Lean_Expr_getRevArg_x21___main(x_1, x_182);
x_184 = l_Lean_Meta_evalNat___main(x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
lean_dec(x_21);
lean_dec(x_1);
x_185 = lean_box(0);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_nat_sub(x_21, x_181);
lean_dec(x_21);
x_188 = lean_nat_sub(x_187, x_181);
lean_dec(x_187);
x_189 = l_Lean_Expr_getRevArg_x21___main(x_1, x_188);
lean_dec(x_1);
x_190 = l_Lean_Meta_evalNat___main(x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
lean_dec(x_186);
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
x_194 = lean_nat_add(x_186, x_193);
lean_dec(x_193);
lean_dec(x_186);
lean_ctor_set(x_190, 0, x_194);
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_190, 0);
lean_inc(x_195);
lean_dec(x_190);
x_196 = lean_nat_add(x_186, x_195);
lean_dec(x_195);
lean_dec(x_186);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
}
}
}
}
else
{
lean_object* x_233; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_233 = lean_box(0);
return x_233;
}
}
case 9:
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
lean_dec(x_1);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
else
{
lean_object* x_237; 
lean_dec(x_234);
x_237 = lean_box(0);
return x_237;
}
}
case 10:
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_1, 1);
lean_inc(x_238);
lean_dec(x_1);
x_1 = x_238;
goto _start;
}
default: 
{
lean_object* x_240; 
lean_dec(x_1);
x_240 = lean_box(0);
return x_240;
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_117; uint8_t x_118; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_13);
x_117 = l_Lean_Meta_evalNat___main___closed__17;
x_118 = lean_name_eq(x_12, x_117);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_String_posOfAux___main___closed__1;
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
lean_dec(x_10);
x_120 = l_Lean_Meta_evalNat___main___closed__18;
x_121 = lean_name_eq(x_12, x_120);
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = 0;
x_15 = x_122;
goto block_116;
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_unsigned_to_nat(2u);
x_124 = lean_nat_dec_eq(x_14, x_123);
x_15 = x_124;
goto block_116;
}
}
else
{
uint8_t x_125; lean_object* x_126; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_1);
x_125 = 0;
x_126 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_10, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_box(0);
return x_127;
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_126);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_126, 0);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_129, 1);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_add(x_131, x_132);
lean_dec(x_131);
lean_ctor_set(x_129, 1, x_133);
return x_126;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_129, 0);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_129);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_135, x_136);
lean_dec(x_135);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_126, 0, x_138);
return x_126;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_126, 0);
lean_inc(x_139);
lean_dec(x_126);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_add(x_141, x_143);
lean_dec(x_141);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_142;
}
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
}
else
{
lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_dec_eq(x_14, x_147);
x_149 = l_coeDecidableEq(x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
lean_dec(x_10);
x_150 = l_Lean_Meta_evalNat___main___closed__18;
x_151 = lean_name_eq(x_12, x_150);
if (x_151 == 0)
{
uint8_t x_152; 
x_152 = 0;
x_15 = x_152;
goto block_116;
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_unsigned_to_nat(2u);
x_154 = lean_nat_dec_eq(x_14, x_153);
x_15 = x_154;
goto block_116;
}
}
else
{
uint8_t x_155; lean_object* x_156; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_1);
x_155 = 0;
x_156 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_10, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_box(0);
return x_157;
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_156);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_156, 0);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 1);
x_162 = lean_nat_add(x_161, x_147);
lean_dec(x_161);
lean_ctor_set(x_159, 1, x_162);
return x_156;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_159, 0);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_159);
x_165 = lean_nat_add(x_164, x_147);
lean_dec(x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_156, 0, x_166);
return x_156;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_156, 0);
lean_inc(x_167);
lean_dec(x_156);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
x_171 = lean_nat_add(x_169, x_147);
lean_dec(x_169);
if (lean_is_scalar(x_170)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_170;
}
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
}
block_116:
{
uint8_t x_16; 
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_evalNat___main___closed__13;
x_18 = lean_name_eq(x_12, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_String_posOfAux___main___closed__1;
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
x_20 = lean_box(0);
x_3 = x_20;
goto block_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_sub(x_14, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
lean_dec(x_22);
x_25 = l_Lean_Expr_getRevArg_x21___main(x_1, x_24);
x_26 = l_Lean_Meta_evalNat___main(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_14);
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
x_30 = lean_nat_sub(x_14, x_29);
lean_dec(x_14);
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
else
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; 
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_dec_eq(x_14, x_52);
x_54 = l_coeDecidableEq(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_14);
x_55 = lean_box(0);
x_3 = x_55;
goto block_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_unsigned_to_nat(3u);
x_57 = lean_nat_sub(x_14, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_57, x_58);
lean_dec(x_57);
x_60 = l_Lean_Expr_getRevArg_x21___main(x_1, x_59);
x_61 = l_Lean_Meta_evalNat___main(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
lean_dec(x_14);
lean_dec(x_1);
x_62 = lean_box(0);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_nat_sub(x_14, x_64);
lean_dec(x_14);
x_66 = lean_nat_sub(x_65, x_58);
lean_dec(x_65);
x_67 = l_Lean_Expr_getRevArg_x21___main(x_1, x_66);
lean_dec(x_1);
x_68 = 0;
x_69 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_67, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
lean_dec(x_63);
x_70 = lean_box(0);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 1);
x_75 = lean_nat_add(x_74, x_63);
lean_dec(x_63);
lean_dec(x_74);
lean_ctor_set(x_72, 1, x_75);
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_nat_add(x_77, x_63);
lean_dec(x_63);
lean_dec(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_69, 0, x_79);
return x_69;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
lean_dec(x_69);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_nat_add(x_82, x_63);
lean_dec(x_63);
lean_dec(x_82);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_12);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_14, x_87);
x_89 = lean_nat_sub(x_88, x_87);
lean_dec(x_88);
x_90 = l_Lean_Expr_getRevArg_x21___main(x_1, x_89);
x_91 = l_Lean_Meta_evalNat___main(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_dec(x_14);
lean_dec(x_1);
x_92 = lean_box(0);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_nat_sub(x_14, x_13);
lean_dec(x_14);
x_95 = lean_nat_sub(x_94, x_87);
lean_dec(x_94);
x_96 = l_Lean_Expr_getRevArg_x21___main(x_1, x_95);
lean_dec(x_1);
x_97 = 0;
x_98 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_96, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
lean_dec(x_93);
x_99 = lean_box(0);
return x_99;
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 1);
x_104 = lean_nat_add(x_103, x_93);
lean_dec(x_93);
lean_dec(x_103);
lean_ctor_set(x_101, 1, x_104);
return x_98;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_nat_add(x_106, x_93);
lean_dec(x_93);
lean_dec(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_98, 0, x_108);
return x_98;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_98, 0);
lean_inc(x_109);
lean_dec(x_98);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_nat_add(x_111, x_93);
lean_dec(x_93);
lean_dec(x_111);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_11);
lean_dec(x_10);
x_174 = lean_box(0);
x_3 = x_174;
goto block_9;
}
}
else
{
lean_object* x_175; 
x_175 = lean_box(0);
x_3 = x_175;
goto block_9;
}
block_9:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_coeDecidableEq(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_20; uint8_t x_21; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_4);
x_20 = l_Lean_Meta_evalNat___main___closed__17;
x_21 = lean_name_eq(x_3, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Meta_evalNat___main___closed__18;
x_23 = lean_name_eq(x_3, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 0;
x_6 = x_24;
goto block_19;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_dec_eq(x_5, x_25);
if (x_26 == 0)
{
x_6 = x_26;
goto block_19;
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_3);
x_27 = l_String_posOfAux___main___closed__2;
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = lean_box(0);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
x_29 = 1;
x_30 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_eq(x_5, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_evalNat___main___closed__18;
x_34 = lean_name_eq(x_3, x_33);
if (x_34 == 0)
{
x_6 = x_32;
goto block_19;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_dec_eq(x_5, x_35);
if (x_36 == 0)
{
x_6 = x_36;
goto block_19;
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_3);
x_37 = l_String_posOfAux___main___closed__2;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_1);
x_38 = lean_box(0);
return x_38;
}
else
{
uint8_t x_39; lean_object* x_40; 
x_39 = 1;
x_40 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_3);
x_41 = l_String_posOfAux___main___closed__2;
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_1);
x_42 = lean_box(0);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; 
x_43 = 1;
x_44 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_43);
return x_44;
}
}
}
block_19:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_evalNat___main___closed__13;
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_3);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = l_coeDecidableEq(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_nat_dec_eq(x_5, x_13);
lean_dec(x_5);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; 
x_17 = 1;
x_18 = l___private_Init_Lean_Meta_Offset_1__getOffsetAux___main(x_1, x_17);
return x_18;
}
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_1);
x_46 = lean_box(0);
return x_46;
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
x_2 = l_Lean_Meta_evalNat___main___closed__18;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Offset_5__mkOffset(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_6 = l___private_Init_Lean_Meta_Offset_4__isNatZero(x_1);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_mkNatLit(x_2);
x_9 = l___private_Init_Lean_Meta_Offset_5__mkOffset___closed__1;
x_10 = l_Lean_mkAppB(x_9, x_1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_mkNatLit(x_2);
return x_11;
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
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; 
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
x_81 = l_coeDecidableEq(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = lean_nat_dec_lt(x_48, x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_nat_sub(x_48, x_79);
lean_dec(x_79);
lean_dec(x_48);
x_84 = l___private_Init_Lean_Meta_Offset_5__mkOffset(x_47, x_83);
x_85 = l_Lean_Meta_isExprDefEqAux(x_84, x_78, x_3, x_4);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
x_89 = l_Bool_toLBool(x_88);
x_90 = lean_box(x_89);
lean_ctor_set(x_85, 0, x_90);
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_85, 0);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_85);
x_93 = lean_unbox(x_91);
lean_dec(x_91);
x_94 = l_Bool_toLBool(x_93);
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_85);
if (x_97 == 0)
{
return x_85;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_85, 0);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_85);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_nat_sub(x_79, x_48);
lean_dec(x_48);
lean_dec(x_79);
x_102 = l___private_Init_Lean_Meta_Offset_5__mkOffset(x_78, x_101);
x_103 = l_Lean_Meta_isExprDefEqAux(x_47, x_102, x_3, x_4);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
x_107 = l_Bool_toLBool(x_106);
x_108 = lean_box(x_107);
lean_ctor_set(x_103, 0, x_108);
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_103);
x_111 = lean_unbox(x_109);
lean_dec(x_109);
x_112 = l_Bool_toLBool(x_111);
x_113 = lean_box(x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_103);
if (x_115 == 0)
{
return x_103;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_103, 0);
x_117 = lean_ctor_get(x_103, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_103);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; 
lean_dec(x_79);
lean_dec(x_48);
x_119 = l_Lean_Meta_isExprDefEqAux(x_47, x_78, x_3, x_4);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
x_123 = l_Bool_toLBool(x_122);
x_124 = lean_box(x_123);
lean_ctor_set(x_119, 0, x_124);
return x_119;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_119, 0);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_119);
x_127 = lean_unbox(x_125);
lean_dec(x_125);
x_128 = l_Bool_toLBool(x_127);
x_129 = lean_box(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
return x_130;
}
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_119);
if (x_131 == 0)
{
return x_119;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_119, 0);
x_133 = lean_ctor_get(x_119, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_119);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
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
