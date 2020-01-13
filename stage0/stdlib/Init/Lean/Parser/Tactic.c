// Lean compiler output
// Module: Init.Lean.Parser.Tactic
// Imports: Init.Lean.Parser.Term
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
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__1;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__7;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__12;
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__2;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__3;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
lean_object* l_Lean_Parser_regTacticParserAttribute___closed__1;
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr(lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinParser(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tacticParser(uint8_t, lean_object*);
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticBlock(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__2;
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___closed__9;
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_regBuiltinTermParserAttr___closed__4;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regTacticParserAttribute(lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__10;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__8;
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___closed__4;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__1;
lean_object* l_Lean_Parser_Term_tacticBlock;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__13;
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___closed__6;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
lean_object* l_Lean_Parser_mkAntiquot(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__9;
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8;
lean_object* l_Lean_Parser_Term_tacticBlock___closed__5;
lean_object* l_Lean_Parser_tacticParser___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_Level_paren___closed__1;
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTacticParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regBuiltinTacticParserAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_regTacticParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regTacticParserAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regTacticParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regTacticParserAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regTacticParserAttribute___closed__2;
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_tacticParser(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_4 = l_Lean_Parser_categoryParser(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_tacticParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_tacticParser(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticBlock");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1;
x_3 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("begin ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("end");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__9;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__12;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_56; lean_object* x_57; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
lean_inc(x_2);
x_56 = l_Lean_Parser_tokenFn(x_2, x_14);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 2)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
x_62 = lean_string_dec_eq(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_64 = l_Lean_Parser_ParserState_mkErrorsAt(x_56, x_63, x_8);
x_17 = x_64;
goto block_55;
}
else
{
x_17 = x_56;
goto block_55;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
x_65 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_66 = l_Lean_Parser_ParserState_mkErrorsAt(x_56, x_65, x_8);
x_17 = x_66;
goto block_55;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_57);
x_67 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14;
lean_inc(x_8);
x_68 = l_Lean_Parser_ParserState_mkErrorsAt(x_56, x_67, x_8);
x_17 = x_68;
goto block_55;
}
block_55:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_21 = l_Lean_Parser_categoryParserFn(x_19, x_20, x_2, x_17);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Parser_tokenFn(x_2, x_21);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 2)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8;
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
x_32 = l_Lean_Parser_ParserState_mkErrorsAt(x_24, x_31, x_23);
x_33 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_34 = l_Lean_Parser_ParserState_mkNode(x_32, x_33, x_16);
x_35 = l_Lean_Parser_mergeOrElseErrors(x_34, x_11, x_8);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_24, x_36, x_16);
x_38 = l_Lean_Parser_mergeOrElseErrors(x_37, x_11, x_8);
lean_dec(x_8);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_27);
x_39 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
x_40 = l_Lean_Parser_ParserState_mkErrorsAt(x_24, x_39, x_23);
x_41 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_16);
x_43 = l_Lean_Parser_mergeOrElseErrors(x_42, x_11, x_8);
lean_dec(x_8);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_25);
x_44 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11;
x_45 = l_Lean_Parser_ParserState_mkErrorsAt(x_24, x_44, x_23);
x_46 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_47 = l_Lean_Parser_ParserState_mkNode(x_45, x_46, x_16);
x_48 = l_Lean_Parser_mergeOrElseErrors(x_47, x_11, x_8);
lean_dec(x_8);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_22);
lean_dec(x_2);
x_49 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_50 = l_Lean_Parser_ParserState_mkNode(x_21, x_49, x_16);
x_51 = l_Lean_Parser_mergeOrElseErrors(x_50, x_11, x_8);
lean_dec(x_8);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_18);
lean_dec(x_2);
x_52 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_53 = l_Lean_Parser_ParserState_mkNode(x_17, x_52, x_16);
x_54 = l_Lean_Parser_mergeOrElseErrors(x_53, x_11, x_8);
lean_dec(x_8);
return x_54;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6;
x_2 = l_Lean_Parser_Level_paren___closed__1;
x_3 = l_Lean_Parser_symbolInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Parser_categoryParser(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_tacticBlock___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_tacticBlock___closed__3;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_2 = l_Lean_Parser_Term_tacticBlock___closed__5;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Term_tacticBlock___closed__6;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_tacticBlock___elambda__1), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_tacticBlock___closed__7;
x_2 = l_Lean_Parser_Term_tacticBlock___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Term_tacticBlock() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_tacticBlock___closed__9;
return x_1;
}
}
lean_object* l___regBuiltinParser_Lean_Parser_Term_tacticBlock(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = l_Lean_Parser_regBuiltinTermParserAttr___closed__4;
x_4 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_5 = l_Lean_Parser_Term_tacticBlock;
x_6 = l_Lean_Parser_addBuiltinParser(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Lean_Parser_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Tactic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__1();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__1);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__2();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__2);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__3();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__3);
l_Lean_Parser_regBuiltinTacticParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinTacticParserAttr___closed__4();
lean_mark_persistent(l_Lean_Parser_regBuiltinTacticParserAttr___closed__4);
res = l_Lean_Parser_regBuiltinTacticParserAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regTacticParserAttribute___closed__1 = _init_l_Lean_Parser_regTacticParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_regTacticParserAttribute___closed__1);
l_Lean_Parser_regTacticParserAttribute___closed__2 = _init_l_Lean_Parser_regTacticParserAttribute___closed__2();
lean_mark_persistent(l_Lean_Parser_regTacticParserAttribute___closed__2);
res = l_Lean_Parser_regTacticParserAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__1);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__3);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__4);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__5 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__5);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__6);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__8);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__9 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__9);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__10 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__10);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__11);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__12 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__12();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__12);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__13 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__13();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__13);
l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14 = _init_l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___elambda__1___closed__14);
l_Lean_Parser_Term_tacticBlock___closed__1 = _init_l_Lean_Parser_Term_tacticBlock___closed__1();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__1);
l_Lean_Parser_Term_tacticBlock___closed__2 = _init_l_Lean_Parser_Term_tacticBlock___closed__2();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__2);
l_Lean_Parser_Term_tacticBlock___closed__3 = _init_l_Lean_Parser_Term_tacticBlock___closed__3();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__3);
l_Lean_Parser_Term_tacticBlock___closed__4 = _init_l_Lean_Parser_Term_tacticBlock___closed__4();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__4);
l_Lean_Parser_Term_tacticBlock___closed__5 = _init_l_Lean_Parser_Term_tacticBlock___closed__5();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__5);
l_Lean_Parser_Term_tacticBlock___closed__6 = _init_l_Lean_Parser_Term_tacticBlock___closed__6();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__6);
l_Lean_Parser_Term_tacticBlock___closed__7 = _init_l_Lean_Parser_Term_tacticBlock___closed__7();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__7);
l_Lean_Parser_Term_tacticBlock___closed__8 = _init_l_Lean_Parser_Term_tacticBlock___closed__8();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__8);
l_Lean_Parser_Term_tacticBlock___closed__9 = _init_l_Lean_Parser_Term_tacticBlock___closed__9();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock___closed__9);
l_Lean_Parser_Term_tacticBlock = _init_l_Lean_Parser_Term_tacticBlock();
lean_mark_persistent(l_Lean_Parser_Term_tacticBlock);
res = l___regBuiltinParser_Lean_Parser_Term_tacticBlock(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
