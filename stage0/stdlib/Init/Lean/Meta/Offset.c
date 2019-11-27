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
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCAppB(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__10;
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffset___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_Offset_1__getOffset(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main___closed__11;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main(lean_object*);
lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
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
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_evalNat___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_148; uint8_t x_175; lean_object* x_202; uint8_t x_203; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_20);
x_202 = l_Lean_Meta_evalNat___main___closed__13;
x_203 = lean_name_eq(x_19, x_202);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = l_Lean_Meta_evalNat___main___closed__14;
x_206 = lean_name_eq(x_19, x_205);
if (x_206 == 0)
{
uint8_t x_207; 
x_207 = 0;
x_175 = x_207;
goto block_201;
}
else
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_unsigned_to_nat(2u);
x_209 = lean_nat_dec_eq(x_21, x_208);
x_175 = x_209;
goto block_201;
}
}
else
{
lean_object* x_210; 
lean_dec(x_21);
lean_dec(x_19);
x_210 = l_Lean_Meta_evalNat___main(x_17);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_box(0);
return x_211;
}
else
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_210);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_210, 0);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_add(x_213, x_214);
lean_dec(x_213);
lean_ctor_set(x_210, 0, x_215);
return x_210;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_210, 0);
lean_inc(x_216);
lean_dec(x_210);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_add(x_216, x_217);
lean_dec(x_216);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
}
else
{
lean_object* x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; 
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_dec_eq(x_21, x_220);
x_222 = 1;
x_223 = l_Bool_DecidableEq(x_221, x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = l_Lean_Meta_evalNat___main___closed__14;
x_225 = lean_name_eq(x_19, x_224);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = 0;
x_175 = x_226;
goto block_201;
}
else
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_unsigned_to_nat(2u);
x_228 = lean_nat_dec_eq(x_21, x_227);
x_175 = x_228;
goto block_201;
}
}
else
{
lean_object* x_229; 
lean_dec(x_21);
lean_dec(x_19);
x_229 = l_Lean_Meta_evalNat___main(x_17);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = lean_box(0);
return x_230;
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_229);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_229, 0);
x_233 = lean_nat_add(x_232, x_220);
lean_dec(x_232);
lean_ctor_set(x_229, 0, x_233);
return x_229;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_nat_add(x_234, x_220);
lean_dec(x_234);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
}
}
}
block_147:
{
uint8_t x_23; uint8_t x_24; 
x_23 = 1;
x_24 = l_Bool_DecidableEq(x_22, x_23);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_96; lean_object* x_124; uint8_t x_125; 
x_124 = l_Lean_Meta_evalNat___main___closed__9;
x_125 = lean_name_eq(x_19, x_124);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = 0;
x_96 = x_126;
goto block_123;
}
else
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_unsigned_to_nat(4u);
x_128 = lean_nat_dec_eq(x_21, x_127);
x_96 = x_128;
goto block_123;
}
block_95:
{
uint8_t x_26; 
x_26 = l_Bool_DecidableEq(x_25, x_23);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Meta_evalNat___main___closed__5;
x_28 = lean_name_eq(x_19, x_27);
lean_dec(x_19);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_21);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_sub(x_21, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_32, x_33);
lean_dec(x_32);
x_35 = l_Lean_Expr_getRevArg_x21___main(x_1, x_34);
x_36 = l_Lean_Meta_evalNat___main(x_35);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_21);
x_37 = lean_box(0);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unsigned_to_nat(3u);
x_40 = lean_nat_sub(x_21, x_39);
lean_dec(x_21);
x_41 = lean_nat_sub(x_40, x_33);
lean_dec(x_40);
x_42 = l_Lean_Expr_getRevArg_x21___main(x_1, x_41);
x_43 = l_Lean_Meta_evalNat___main(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec(x_38);
x_44 = lean_box(0);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_nat_mul(x_38, x_46);
lean_dec(x_46);
lean_dec(x_38);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_nat_mul(x_38, x_48);
lean_dec(x_48);
lean_dec(x_38);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
else
{
lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_nat_dec_eq(x_21, x_51);
x_53 = l_Bool_DecidableEq(x_52, x_23);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_21);
x_54 = lean_box(0);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_nat_sub(x_21, x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_56, x_57);
lean_dec(x_56);
x_59 = l_Lean_Expr_getRevArg_x21___main(x_1, x_58);
x_60 = l_Lean_Meta_evalNat___main(x_59);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec(x_21);
x_61 = lean_box(0);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_sub(x_21, x_63);
lean_dec(x_21);
x_65 = lean_nat_sub(x_64, x_57);
lean_dec(x_64);
x_66 = l_Lean_Expr_getRevArg_x21___main(x_1, x_65);
x_67 = l_Lean_Meta_evalNat___main(x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_dec(x_62);
x_68 = lean_box(0);
return x_68;
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = lean_nat_mul(x_62, x_70);
lean_dec(x_70);
lean_dec(x_62);
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_nat_mul(x_62, x_72);
lean_dec(x_72);
lean_dec(x_62);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_19);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_nat_sub(x_21, x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_76, x_77);
lean_dec(x_76);
x_79 = l_Lean_Expr_getRevArg_x21___main(x_1, x_78);
x_80 = l_Lean_Meta_evalNat___main(x_79);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec(x_21);
x_81 = lean_box(0);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unsigned_to_nat(3u);
x_84 = lean_nat_sub(x_21, x_83);
lean_dec(x_21);
x_85 = lean_nat_sub(x_84, x_77);
lean_dec(x_84);
x_86 = l_Lean_Expr_getRevArg_x21___main(x_1, x_85);
x_87 = l_Lean_Meta_evalNat___main(x_86);
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_dec(x_82);
x_88 = lean_box(0);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_nat_sub(x_82, x_90);
lean_dec(x_90);
lean_dec(x_82);
lean_ctor_set(x_87, 0, x_91);
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_nat_sub(x_82, x_92);
lean_dec(x_92);
lean_dec(x_82);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
}
block_123:
{
uint8_t x_97; 
x_97 = l_Bool_DecidableEq(x_96, x_23);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = l_Lean_Meta_evalNat___main___closed__7;
x_99 = lean_name_eq(x_19, x_98);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = 0;
x_25 = x_100;
goto block_95;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_unsigned_to_nat(4u);
x_102 = lean_nat_dec_eq(x_21, x_101);
x_25 = x_102;
goto block_95;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_19);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_sub(x_21, x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
lean_dec(x_104);
x_107 = l_Lean_Expr_getRevArg_x21___main(x_1, x_106);
x_108 = l_Lean_Meta_evalNat___main(x_107);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
lean_dec(x_21);
x_109 = lean_box(0);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_unsigned_to_nat(3u);
x_112 = lean_nat_sub(x_21, x_111);
lean_dec(x_21);
x_113 = lean_nat_sub(x_112, x_105);
lean_dec(x_112);
x_114 = l_Lean_Expr_getRevArg_x21___main(x_1, x_113);
x_115 = l_Lean_Meta_evalNat___main(x_114);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
lean_dec(x_110);
x_116 = lean_box(0);
return x_116;
}
else
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 0);
x_119 = lean_nat_add(x_110, x_118);
lean_dec(x_118);
lean_dec(x_110);
lean_ctor_set(x_115, 0, x_119);
return x_115;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
lean_dec(x_115);
x_121 = lean_nat_add(x_110, x_120);
lean_dec(x_120);
lean_dec(x_110);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_19);
x_129 = lean_nat_sub(x_21, x_20);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_sub(x_129, x_130);
lean_dec(x_129);
x_132 = l_Lean_Expr_getRevArg_x21___main(x_1, x_131);
x_133 = l_Lean_Meta_evalNat___main(x_132);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
lean_dec(x_21);
x_134 = lean_box(0);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_nat_sub(x_21, x_130);
lean_dec(x_21);
x_137 = lean_nat_sub(x_136, x_130);
lean_dec(x_136);
x_138 = l_Lean_Expr_getRevArg_x21___main(x_1, x_137);
x_139 = l_Lean_Meta_evalNat___main(x_138);
lean_dec(x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
lean_dec(x_135);
x_140 = lean_box(0);
return x_140;
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_139);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_139, 0);
x_143 = lean_nat_mul(x_135, x_142);
lean_dec(x_142);
lean_dec(x_135);
lean_ctor_set(x_139, 0, x_143);
return x_139;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_139, 0);
lean_inc(x_144);
lean_dec(x_139);
x_145 = lean_nat_mul(x_135, x_144);
lean_dec(x_144);
lean_dec(x_135);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
}
}
block_174:
{
uint8_t x_149; uint8_t x_150; 
x_149 = 1;
x_150 = l_Bool_DecidableEq(x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = l_Lean_Meta_evalNat___main___closed__10;
x_152 = lean_name_eq(x_19, x_151);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = 0;
x_22 = x_153;
goto block_147;
}
else
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_unsigned_to_nat(2u);
x_155 = lean_nat_dec_eq(x_21, x_154);
x_22 = x_155;
goto block_147;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_19);
x_156 = lean_nat_sub(x_21, x_20);
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_nat_sub(x_156, x_157);
lean_dec(x_156);
x_159 = l_Lean_Expr_getRevArg_x21___main(x_1, x_158);
x_160 = l_Lean_Meta_evalNat___main(x_159);
lean_dec(x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec(x_21);
x_161 = lean_box(0);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_nat_sub(x_21, x_157);
lean_dec(x_21);
x_164 = lean_nat_sub(x_163, x_157);
lean_dec(x_163);
x_165 = l_Lean_Expr_getRevArg_x21___main(x_1, x_164);
x_166 = l_Lean_Meta_evalNat___main(x_165);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
lean_dec(x_162);
x_167 = lean_box(0);
return x_167;
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 0);
x_170 = lean_nat_sub(x_162, x_169);
lean_dec(x_169);
lean_dec(x_162);
lean_ctor_set(x_166, 0, x_170);
return x_166;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_166, 0);
lean_inc(x_171);
lean_dec(x_166);
x_172 = lean_nat_sub(x_162, x_171);
lean_dec(x_171);
lean_dec(x_162);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
}
}
block_201:
{
uint8_t x_176; uint8_t x_177; 
x_176 = 1;
x_177 = l_Bool_DecidableEq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = l_Lean_Meta_evalNat___main___closed__11;
x_179 = lean_name_eq(x_19, x_178);
if (x_179 == 0)
{
uint8_t x_180; 
x_180 = 0;
x_148 = x_180;
goto block_174;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_unsigned_to_nat(2u);
x_182 = lean_nat_dec_eq(x_21, x_181);
x_148 = x_182;
goto block_174;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_19);
x_183 = lean_nat_sub(x_21, x_20);
x_184 = lean_unsigned_to_nat(1u);
x_185 = lean_nat_sub(x_183, x_184);
lean_dec(x_183);
x_186 = l_Lean_Expr_getRevArg_x21___main(x_1, x_185);
x_187 = l_Lean_Meta_evalNat___main(x_186);
lean_dec(x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
lean_dec(x_21);
x_188 = lean_box(0);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_nat_sub(x_21, x_184);
lean_dec(x_21);
x_191 = lean_nat_sub(x_190, x_184);
lean_dec(x_190);
x_192 = l_Lean_Expr_getRevArg_x21___main(x_1, x_191);
x_193 = l_Lean_Meta_evalNat___main(x_192);
lean_dec(x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
lean_dec(x_189);
x_194 = lean_box(0);
return x_194;
}
else
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_193, 0);
x_197 = lean_nat_add(x_189, x_196);
lean_dec(x_196);
lean_dec(x_189);
lean_ctor_set(x_193, 0, x_197);
return x_193;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
lean_dec(x_193);
x_199 = lean_nat_add(x_189, x_198);
lean_dec(x_198);
lean_dec(x_189);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
}
}
}
}
}
else
{
lean_object* x_237; 
lean_dec(x_18);
x_237 = lean_box(0);
return x_237;
}
}
case 9:
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
else
{
lean_object* x_241; 
x_241 = lean_box(0);
return x_241;
}
}
case 10:
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_1, 1);
x_1 = x_242;
goto _start;
}
default: 
{
lean_object* x_244; 
x_244 = lean_box(0);
return x_244;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_75; uint8_t x_76; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_5);
x_75 = l_Lean_Meta_evalNat___main___closed__13;
x_76 = lean_name_eq(x_4, x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
lean_dec(x_2);
x_78 = l_Lean_Meta_evalNat___main___closed__14;
x_79 = lean_name_eq(x_4, x_78);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = 0;
x_7 = x_80;
goto block_74;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_unsigned_to_nat(2u);
x_82 = lean_nat_dec_eq(x_6, x_81);
x_7 = x_82;
goto block_74;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_83 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_2);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_85, x_86);
lean_dec(x_85);
lean_ctor_set(x_83, 1, x_87);
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_89, x_90);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_dec_eq(x_6, x_93);
x_95 = 1;
x_96 = l_Bool_DecidableEq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_2);
x_97 = l_Lean_Meta_evalNat___main___closed__14;
x_98 = lean_name_eq(x_4, x_97);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_7 = x_99;
goto block_74;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_nat_dec_eq(x_6, x_100);
x_7 = x_101;
goto block_74;
}
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_102 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_2);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 1);
x_105 = lean_nat_add(x_104, x_93);
lean_dec(x_104);
lean_ctor_set(x_102, 1, x_105);
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_102, 0);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_102);
x_108 = lean_nat_add(x_107, x_93);
lean_dec(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
block_74:
{
uint8_t x_8; uint8_t x_9; 
x_8 = 1;
x_9 = l_Bool_DecidableEq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_evalNat___main___closed__9;
x_11 = lean_name_eq(x_4, x_10);
lean_dec(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
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
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(4u);
x_34 = lean_nat_dec_eq(x_6, x_33);
x_35 = l_Bool_DecidableEq(x_34, x_8);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_6);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_5);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_sub(x_6, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_Expr_getRevArg_x21___main(x_1, x_40);
x_42 = l_Lean_Meta_evalNat___main(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_6);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_5);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_sub(x_6, x_5);
lean_dec(x_6);
x_46 = lean_nat_sub(x_45, x_39);
lean_dec(x_45);
x_47 = l_Lean_Expr_getRevArg_x21___main(x_1, x_46);
lean_dec(x_1);
x_48 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 1);
x_51 = lean_nat_add(x_50, x_44);
lean_dec(x_44);
lean_dec(x_50);
lean_ctor_set(x_48, 1, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_nat_add(x_53, x_44);
lean_dec(x_44);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_4);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_sub(x_6, x_56);
x_58 = lean_nat_sub(x_57, x_56);
lean_dec(x_57);
x_59 = l_Lean_Expr_getRevArg_x21___main(x_1, x_58);
x_60 = l_Lean_Meta_evalNat___main(x_59);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec(x_6);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_5);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_nat_sub(x_6, x_5);
lean_dec(x_6);
x_64 = lean_nat_sub(x_63, x_56);
lean_dec(x_63);
x_65 = l_Lean_Expr_getRevArg_x21___main(x_1, x_64);
lean_dec(x_1);
x_66 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_65);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 1);
x_69 = lean_nat_add(x_68, x_62);
lean_dec(x_62);
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
x_72 = lean_nat_add(x_71, x_62);
lean_dec(x_62);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
return x_113;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_22; uint8_t x_23; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_4);
x_22 = l_Lean_Meta_evalNat___main___closed__13;
x_23 = lean_name_eq(x_3, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Meta_evalNat___main___closed__14;
x_25 = lean_name_eq(x_3, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 0;
x_6 = x_26;
goto block_21;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_nat_dec_eq(x_5, x_27);
if (x_28 == 0)
{
x_6 = x_28;
goto block_21;
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_3);
x_29 = l_String_Iterator_extract___closed__1;
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_dec_eq(x_5, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Meta_evalNat___main___closed__14;
x_36 = lean_name_eq(x_3, x_35);
if (x_36 == 0)
{
x_6 = x_34;
goto block_21;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_dec_eq(x_5, x_37);
if (x_38 == 0)
{
x_6 = x_38;
goto block_21;
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = l_String_Iterator_extract___closed__1;
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_1);
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_3);
x_43 = l_String_Iterator_extract___closed__1;
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_1);
x_44 = lean_box(0);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
block_21:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_evalNat___main___closed__9;
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_3);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
lean_dec(x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_nat_dec_eq(x_5, x_14);
lean_dec(x_5);
x_16 = 1;
x_17 = l_Bool_DecidableEq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Init_Lean_Meta_Offset_1__getOffset___main(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_box(0);
return x_48;
}
}
}
lean_object* l_Lean_Meta_isDefEqOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_Offset_2__isOffset(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Meta_evalNat___main(x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_11 = l___private_Init_Lean_Meta_Offset_2__isOffset(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = l_Lean_Meta_evalNat___main(x_2);
lean_dec(x_2);
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
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_dec_le(x_22, x_10);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_nat_sub(x_10, x_22);
lean_dec(x_22);
lean_dec(x_10);
x_28 = l_Lean_mkNatLit(x_27);
x_29 = l_Lean_Meta_isExprDefEqAux(x_1, x_28, x_3, x_4);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = l_Bool_toLBool(x_32);
x_34 = lean_box(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_38 = l_Bool_toLBool(x_37);
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_2);
x_48 = l___private_Init_Lean_Meta_Offset_2__isOffset(x_2);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = l_Lean_Meta_evalNat___main(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_3);
x_50 = 2;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_nat_dec_le(x_47, x_53);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_3);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_nat_sub(x_53, x_47);
lean_dec(x_47);
lean_dec(x_53);
x_59 = l_Lean_mkNatLit(x_58);
x_60 = l_Lean_Meta_isExprDefEqAux(x_46, x_59, x_3, x_4);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
x_64 = l_Bool_toLBool(x_63);
x_65 = lean_box(x_64);
lean_ctor_set(x_60, 0, x_65);
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_69 = l_Bool_toLBool(x_68);
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_60);
if (x_72 == 0)
{
return x_60;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_60, 0);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; 
lean_dec(x_2);
x_76 = lean_ctor_get(x_48, 0);
lean_inc(x_76);
lean_dec(x_48);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_nat_dec_eq(x_47, x_78);
x_80 = 1;
x_81 = l_Bool_DecidableEq(x_79, x_80);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = lean_nat_dec_lt(x_47, x_78);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_nat_sub(x_47, x_78);
lean_dec(x_78);
lean_dec(x_47);
x_84 = l_Lean_mkNatLit(x_83);
x_85 = l_Lean_Meta_evalNat___main___closed__14;
x_86 = l_Lean_mkCAppB(x_85, x_46, x_84);
x_87 = l_Lean_Meta_isExprDefEqAux(x_86, x_77, x_3, x_4);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
x_91 = l_Bool_toLBool(x_90);
x_92 = lean_box(x_91);
lean_ctor_set(x_87, 0, x_92);
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_unbox(x_93);
lean_dec(x_93);
x_96 = l_Bool_toLBool(x_95);
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_nat_sub(x_78, x_47);
lean_dec(x_47);
lean_dec(x_78);
x_104 = l_Lean_mkNatLit(x_103);
x_105 = l_Lean_Meta_evalNat___main___closed__14;
x_106 = l_Lean_mkCAppB(x_105, x_77, x_104);
x_107 = l_Lean_Meta_isExprDefEqAux(x_46, x_106, x_3, x_4);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
x_111 = l_Bool_toLBool(x_110);
x_112 = lean_box(x_111);
lean_ctor_set(x_107, 0, x_112);
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_116 = l_Bool_toLBool(x_115);
x_117 = lean_box(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
return x_118;
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_107);
if (x_119 == 0)
{
return x_107;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_107, 0);
x_121 = lean_ctor_get(x_107, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_107);
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
lean_object* x_123; 
lean_dec(x_78);
lean_dec(x_47);
x_123 = l_Lean_Meta_isExprDefEqAux(x_46, x_77, x_3, x_4);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
x_127 = l_Bool_toLBool(x_126);
x_128 = lean_box(x_127);
lean_ctor_set(x_123, 0, x_128);
return x_123;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_123);
x_131 = lean_unbox(x_129);
lean_dec(x_129);
x_132 = l_Bool_toLBool(x_131);
x_133 = lean_box(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_130);
return x_134;
}
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_123);
if (x_135 == 0)
{
return x_123;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_123, 0);
x_137 = lean_ctor_get(x_123, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_123);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
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
