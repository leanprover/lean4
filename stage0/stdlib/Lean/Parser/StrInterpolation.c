// Lean compiler output
// Module: Lean.Parser.StrInterpolation
// Imports: Init Lean.Parser.Basic
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
lean_object* l_Lean_Parser_quotedCharCoreFn___at_Lean_Parser_interpolatedStrFn_parse___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_interpolatedStrKind;
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStr___elambda__1___closed__1;
lean_object* l_Lean_Parser_interpolatedStr___elambda__1___closed__2;
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStrFn_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__1;
lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object*);
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t);
extern lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__1;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_quotedCharCoreFn___at_Lean_Parser_interpolatedStrFn_parse___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStr___closed__1;
extern lean_object* l_Lean_Parser_quotedCharCoreFn___closed__1;
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_interpolatedStr___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_interpolatedStrFn_parse___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__2;
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_interpolatedStrFn_parse___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object*);
lean_object* l_Lean_Parser_interpolatedStrFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
extern lean_object* l_Lean_interpolatedStrLitKind;
uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 123;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Parser_isQuotableCharDefault(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_isQuotableCharForStrInterpolant(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_interpolatedStrFn_parse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = 125;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_quotedCharCoreFn___at_Lean_Parser_interpolatedStrFn_parse___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = l_Lean_Parser_isQuotableCharForStrInterpolant(x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; uint8_t x_28; 
x_9 = 120;
x_28 = x_7 == x_9;
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = 0;
x_10 = x_29;
goto block_27;
}
else
{
uint8_t x_30; 
x_30 = 1;
x_10 = x_30;
goto block_27;
}
block_27:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 117;
x_12 = x_7 == x_11;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_Lean_Parser_quotedCharCoreFn___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
x_16 = l_Lean_Parser_hexDigitFn(x_1, x_15);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Parser_hexDigitFn(x_1, x_16);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Parser_hexDigitFn(x_1, x_18);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Parser_hexDigitFn(x_1, x_20);
return x_22;
}
else
{
lean_dec(x_21);
return x_20;
}
}
else
{
lean_dec(x_19);
return x_18;
}
}
else
{
lean_dec(x_17);
return x_16;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
x_24 = l_Lean_Parser_hexDigitFn(x_1, x_23);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Parser_hexDigitFn(x_1, x_24);
return x_26;
}
else
{
lean_dec(x_25);
return x_24;
}
}
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_32 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_33 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_32);
return x_33;
}
}
}
lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected '}'");
return x_1;
}
}
lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_2, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; uint8_t x_44; 
x_9 = lean_string_utf8_get(x_2, x_7);
x_10 = lean_string_utf8_next(x_2, x_7);
lean_dec(x_7);
x_11 = l_Lean_Parser_ParserState_setPos(x_6, x_10);
x_12 = 34;
x_44 = x_9 == x_12;
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = 0;
x_13 = x_45;
goto block_43;
}
else
{
uint8_t x_46; 
x_46 = 1;
x_13 = x_46;
goto block_43;
}
block_43:
{
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; uint8_t x_36; 
x_14 = 92;
x_36 = x_9 == x_14;
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 0;
x_15 = x_37;
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = 1;
x_15 = x_38;
goto block_35;
}
block_35:
{
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; uint8_t x_29; 
x_16 = 123;
x_29 = x_9 == x_16;
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = 0;
x_17 = x_30;
goto block_28;
}
else
{
uint8_t x_31; 
x_31 = 1;
x_17 = x_31;
goto block_28;
}
block_28:
{
if (x_17 == 0)
{
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_interpolatedStrLitKind;
x_20 = l_Lean_Parser_mkNodeToken(x_19, x_4, x_5, x_11);
lean_inc(x_1);
lean_inc(x_5);
x_21 = lean_apply_2(x_1, x_5, x_20);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Parser_interpolatedStrFn_parse___closed__1;
x_25 = l_Lean_Parser_satisfyFn___at_Lean_Parser_interpolatedStrFn_parse___spec__1(x_24, x_5, x_21);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
x_4 = x_23;
x_6 = x_25;
goto _start;
}
else
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_25;
}
}
else
{
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_21;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Parser_quotedCharCoreFn___at_Lean_Parser_interpolatedStrFn_parse___spec__2(x_5, x_11);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
x_6 = x_32;
goto _start;
}
else
{
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_32;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_39 = l_Lean_interpolatedStrLitKind;
x_40 = l_Lean_Parser_mkNodeToken(x_39, x_4, x_5, x_11);
lean_dec(x_5);
x_41 = l_Lean_interpolatedStrKind;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_3);
return x_42;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_48 = l_Lean_Parser_ParserState_mkUnexpectedError(x_6, x_47);
return x_48;
}
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_interpolatedStrFn_parse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_satisfyFn___at_Lean_Parser_interpolatedStrFn_parse___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_quotedCharCoreFn___at_Lean_Parser_interpolatedStrFn_parse___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_quotedCharCoreFn___at_Lean_Parser_interpolatedStrFn_parse___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_interpolatedStrFn_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_interpolatedStrFn_parse(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Parser_interpolatedStrFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_ParserState_next(x_3, x_5, x_8);
x_11 = l_Lean_Parser_interpolatedStrFn_parse(x_1, x_5, x_7, x_8, x_2, x_10);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_12);
return x_13;
}
}
}
lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("interpolatedStr");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__2;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_interpolatedStrKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
x_2 = l_Lean_Parser_interpolatedStr___elambda__1___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_interpolatedStr___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Parser_interpolatedStr___elambda__1___closed__2;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Parser_tryAnti(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_2);
x_11 = lean_apply_2(x_5, x_2, x_3);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_14, x_10);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_inc(x_10);
x_16 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean_dec(x_9);
x_17 = lean_apply_2(x_1, x_2, x_16);
x_18 = 1;
x_19 = l_Lean_Parser_mergeOrElseErrors(x_17, x_13, x_10, x_18);
lean_dec(x_10);
return x_19;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_interpolatedStr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_interpolatedStr___elambda__1___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_interpolatedStr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStr___elambda__1), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_interpolatedStr___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_StrInterpolation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_interpolatedStrFn_parse___closed__1 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__1);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__1 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__1);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__2 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__2);
l_Lean_Parser_interpolatedStr___elambda__1___closed__1 = _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___elambda__1___closed__1);
l_Lean_Parser_interpolatedStr___elambda__1___closed__2 = _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___elambda__1___closed__2);
l_Lean_Parser_interpolatedStr___closed__1 = _init_l_Lean_Parser_interpolatedStr___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
