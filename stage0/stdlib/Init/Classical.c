// Lean compiler output
// Module: Init.Classical
// Imports: Init.Core Init.NotationExtra
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
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_16729____closed__2;
lean_object* l_Classical_tacticByCases_____x3a_____closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__13;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962_(lean_object*, lean_object*, lean_object*);
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Classical_tacticByCases_____x3a_____closed__7;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1;
lean_object* l_Classical_typeDecidable_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
extern lean_object* l_Lean_Parser_Tactic_cases___closed__1;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13978____closed__6;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13978____closed__13;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__6;
extern lean_object* l_Lean_groupKind___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13376____closed__13;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__5;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13978____closed__11;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__3;
lean_object* l_Classical_tacticByCases_____x3a_____closed__10;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__15;
extern lean_object* l_Lean_Parser_Tactic_cases___closed__2;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__14;
lean_object* l_Classical_tacticByCases_____x3a__;
lean_object* l_Classical_typeDecidable_match__1(lean_object*, lean_object*);
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__7;
lean_object* l_Classical_tacticByCases_____x3a_____closed__3;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__9;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__10;
extern lean_object* l_termDepIfThenElse___closed__14;
extern lean_object* l_termDepIfThenElse___closed__9;
extern lean_object* l_Array_term_____x5b___x3a___x5d___closed__10;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Classical_tacticByCases_____x3a_____closed__5;
extern lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__2;
lean_object* l_Classical_tacticByCases_____x3a_____closed__4;
lean_object* l_Classical_tacticByCases_____x3a_____closed__9;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__10;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Classical_typeDecidable_match__1___rarg(uint8_t, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13978____closed__14;
lean_object* l_Classical_tacticByCases_____x3a_____closed__1;
extern lean_object* l_Lean_Parser_Tactic_casesTarget___closed__2;
lean_object* l_Classical_tacticByCases_____x3a_____closed__8;
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__11;
lean_object* l_Classical_tacticByCases_____x3a_____closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13978____closed__5;
lean_object* l_Classical_typeDecidable_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_1(x_2, lean_box(0));
return x_5;
}
}
}
lean_object* l_Classical_typeDecidable_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Classical_typeDecidable_match__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Classical_typeDecidable_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Classical_typeDecidable_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Classical");
return x_1;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Classical_tacticByCases_____x3a_____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticByCases__:_");
return x_1;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Classical_tacticByCases_____x3a_____closed__2;
x_2 = l_Classical_tacticByCases_____x3a_____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("byCases");
return x_1;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Classical_tacticByCases_____x3a_____closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Classical_tacticByCases_____x3a_____closed__6;
x_3 = l_termDepIfThenElse___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Classical_tacticByCases_____x3a_____closed__7;
x_3 = l_Array_term_____x5b___x3a___x5d___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Classical_tacticByCases_____x3a_____closed__8;
x_3 = l_termDepIfThenElse___closed__14;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Classical_tacticByCases_____x3a_____closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Classical_tacticByCases_____x3a_____closed__9;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Classical_tacticByCases_____x3a__() {
_start:
{
lean_object* x_1; 
x_1 = l_Classical_tacticByCases_____x3a_____closed__10;
return x_1;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("em");
return x_1;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Classical_tacticByCases_____x3a_____closed__2;
x_2 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inl");
return x_1;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inr");
return x_1;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__13;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Classical_myMacro____x40_Init_Classical___hyg_962_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Classical_tacticByCases_____x3a_____closed__4;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Parser_Tactic_cases___closed__1;
lean_inc(x_14);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__4;
lean_inc(x_15);
lean_inc(x_16);
x_22 = l_Lean_addMacroScope(x_16, x_21, x_15);
x_23 = lean_box(0);
x_24 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__3;
x_25 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__7;
lean_inc(x_14);
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_array_push(x_19, x_26);
x_28 = lean_array_push(x_19, x_11);
x_29 = l_Lean_nullKind___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_27, x_30);
x_32 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_myMacro____x40_Init_Notation___hyg_13978____closed__5;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_Parser_Tactic_casesTarget___closed__2;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_19, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_push(x_20, x_39);
x_41 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_42 = lean_array_push(x_40, x_41);
x_43 = l_myMacro____x40_Init_Notation___hyg_13978____closed__6;
lean_inc(x_14);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_19, x_44);
x_46 = lean_array_push(x_45, x_41);
x_47 = l_myMacro____x40_Init_Notation___hyg_13978____closed__11;
lean_inc(x_14);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_array_push(x_19, x_48);
x_50 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__11;
lean_inc(x_15);
lean_inc(x_16);
x_51 = l_Lean_addMacroScope(x_16, x_50, x_15);
x_52 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__10;
lean_inc(x_14);
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set(x_53, 3, x_23);
x_54 = lean_array_push(x_34, x_53);
x_55 = l_Lean_groupKind___closed__2;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_inc(x_49);
x_57 = lean_array_push(x_49, x_56);
x_58 = lean_array_push(x_19, x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_29);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_59);
x_60 = lean_array_push(x_57, x_59);
x_61 = l_myMacro____x40_Init_Notation___hyg_13376____closed__13;
lean_inc(x_14);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_62);
x_63 = lean_array_push(x_60, x_62);
x_64 = l_myMacro____x40_Init_Notation___hyg_13978____closed__14;
lean_inc(x_14);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_14);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_19, x_65);
x_67 = l_myMacro____x40_Init_Notation___hyg_13978____closed__13;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_inc(x_68);
x_69 = lean_array_push(x_63, x_68);
x_70 = l_Lean_Parser_Tactic_inductionAlt___closed__2;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_push(x_19, x_71);
x_73 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__15;
x_74 = l_Lean_addMacroScope(x_16, x_73, x_15);
x_75 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__14;
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_14);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_23);
x_77 = lean_array_push(x_34, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_55);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_push(x_49, x_78);
x_80 = lean_array_push(x_79, x_59);
x_81 = lean_array_push(x_80, x_62);
x_82 = lean_array_push(x_81, x_68);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_72, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_29);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_push(x_46, x_85);
x_87 = l_Lean_Parser_Tactic_inductionAlts___closed__2;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_array_push(x_19, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_29);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_push(x_42, x_90);
x_92 = l_Lean_Parser_Tactic_cases___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_19, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_29);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_19, x_95);
x_97 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_16729____closed__2;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_12, 0, x_98);
return x_12;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_99 = lean_ctor_get(x_12, 0);
x_100 = lean_ctor_get(x_12, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_12);
x_101 = lean_ctor_get(x_2, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 1);
lean_inc(x_102);
lean_dec(x_2);
x_103 = l_Lean_Parser_Tactic_cases___closed__1;
lean_inc(x_99);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Array_empty___closed__1;
x_106 = lean_array_push(x_105, x_104);
x_107 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__4;
lean_inc(x_101);
lean_inc(x_102);
x_108 = l_Lean_addMacroScope(x_102, x_107, x_101);
x_109 = lean_box(0);
x_110 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__3;
x_111 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__7;
lean_inc(x_99);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_array_push(x_105, x_112);
x_114 = lean_array_push(x_105, x_11);
x_115 = l_Lean_nullKind___closed__2;
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_array_push(x_113, x_116);
x_118 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_myMacro____x40_Init_Notation___hyg_13978____closed__5;
x_121 = lean_array_push(x_120, x_119);
x_122 = l_Lean_Parser_Tactic_casesTarget___closed__2;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_array_push(x_105, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_push(x_106, x_125);
x_127 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_128 = lean_array_push(x_126, x_127);
x_129 = l_myMacro____x40_Init_Notation___hyg_13978____closed__6;
lean_inc(x_99);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_99);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_array_push(x_105, x_130);
x_132 = lean_array_push(x_131, x_127);
x_133 = l_myMacro____x40_Init_Notation___hyg_13978____closed__11;
lean_inc(x_99);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_99);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_push(x_105, x_134);
x_136 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__11;
lean_inc(x_101);
lean_inc(x_102);
x_137 = l_Lean_addMacroScope(x_102, x_136, x_101);
x_138 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__10;
lean_inc(x_99);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_99);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_109);
x_140 = lean_array_push(x_120, x_139);
x_141 = l_Lean_groupKind___closed__2;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
lean_inc(x_135);
x_143 = lean_array_push(x_135, x_142);
x_144 = lean_array_push(x_105, x_9);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_115);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_145);
x_146 = lean_array_push(x_143, x_145);
x_147 = l_myMacro____x40_Init_Notation___hyg_13376____closed__13;
lean_inc(x_99);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_99);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_148);
x_149 = lean_array_push(x_146, x_148);
x_150 = l_myMacro____x40_Init_Notation___hyg_13978____closed__14;
lean_inc(x_99);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_99);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_push(x_105, x_151);
x_153 = l_myMacro____x40_Init_Notation___hyg_13978____closed__13;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
lean_inc(x_154);
x_155 = lean_array_push(x_149, x_154);
x_156 = l_Lean_Parser_Tactic_inductionAlt___closed__2;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_array_push(x_105, x_157);
x_159 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__15;
x_160 = l_Lean_addMacroScope(x_102, x_159, x_101);
x_161 = l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__14;
x_162 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_162, 0, x_99);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_109);
x_163 = lean_array_push(x_120, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_141);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_push(x_135, x_164);
x_166 = lean_array_push(x_165, x_145);
x_167 = lean_array_push(x_166, x_148);
x_168 = lean_array_push(x_167, x_154);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_156);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_158, x_169);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_115);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_array_push(x_132, x_171);
x_173 = l_Lean_Parser_Tactic_inductionAlts___closed__2;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_array_push(x_105, x_174);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_115);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_array_push(x_128, x_176);
x_178 = l_Lean_Parser_Tactic_cases___closed__2;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = lean_array_push(x_105, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_115);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_array_push(x_105, x_181);
x_183 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_16729____closed__2;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_100);
return x_185;
}
}
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_NotationExtra(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Classical(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Classical_tacticByCases_____x3a_____closed__1 = _init_l_Classical_tacticByCases_____x3a_____closed__1();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__1);
l_Classical_tacticByCases_____x3a_____closed__2 = _init_l_Classical_tacticByCases_____x3a_____closed__2();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__2);
l_Classical_tacticByCases_____x3a_____closed__3 = _init_l_Classical_tacticByCases_____x3a_____closed__3();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__3);
l_Classical_tacticByCases_____x3a_____closed__4 = _init_l_Classical_tacticByCases_____x3a_____closed__4();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__4);
l_Classical_tacticByCases_____x3a_____closed__5 = _init_l_Classical_tacticByCases_____x3a_____closed__5();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__5);
l_Classical_tacticByCases_____x3a_____closed__6 = _init_l_Classical_tacticByCases_____x3a_____closed__6();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__6);
l_Classical_tacticByCases_____x3a_____closed__7 = _init_l_Classical_tacticByCases_____x3a_____closed__7();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__7);
l_Classical_tacticByCases_____x3a_____closed__8 = _init_l_Classical_tacticByCases_____x3a_____closed__8();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__8);
l_Classical_tacticByCases_____x3a_____closed__9 = _init_l_Classical_tacticByCases_____x3a_____closed__9();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__9);
l_Classical_tacticByCases_____x3a_____closed__10 = _init_l_Classical_tacticByCases_____x3a_____closed__10();
lean_mark_persistent(l_Classical_tacticByCases_____x3a_____closed__10);
l_Classical_tacticByCases_____x3a__ = _init_l_Classical_tacticByCases_____x3a__();
lean_mark_persistent(l_Classical_tacticByCases_____x3a__);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__1);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__2 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__2();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__2);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__3 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__3();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__3);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__4 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__4();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__4);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__5 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__5();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__5);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__6 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__6();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__6);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__7 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__7();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__7);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__8);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__9 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__9();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__9);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__10 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__10();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__10);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__11 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__11();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__11);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__12);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__13 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__13();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__13);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__14 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__14();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__14);
l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__15 = _init_l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__15();
lean_mark_persistent(l_Classical_myMacro____x40_Init_Classical___hyg_962____closed__15);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
