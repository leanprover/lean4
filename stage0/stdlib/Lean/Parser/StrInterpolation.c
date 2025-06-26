// Lean compiler output
// Module: Lean.Parser.StrInterpolation
// Imports: Lean.Parser.Basic
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
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__6;
static lean_object* l_Lean_Parser_interpolatedStrFn___closed__0;
static lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
static lean_object* l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0;
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__3;
static lean_object* l_Lean_Parser_interpolatedStr___closed__0;
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__5;
static lean_object* l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3;
static lean_object* l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__0;
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__1;
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__4;
static lean_object* l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2;
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__2;
lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 123;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Parser_isQuotableCharDefault(x_1);
return x_4;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrLitKind", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_interpolatedStrFn_parse___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'}'", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_interpolatedStrFn_parse___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_isQuotableCharForStrInterpolant___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated string literal", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_2, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_9 = lean_string_utf8_get(x_2, x_7);
x_10 = lean_string_utf8_next(x_2, x_7);
lean_dec(x_7);
x_11 = l_Lean_Parser_ParserState_setPos(x_6, x_10);
x_12 = 34;
x_13 = lean_uint32_dec_eq(x_9, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 92;
x_15 = lean_uint32_dec_eq(x_9, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 123;
x_17 = lean_uint32_dec_eq(x_9, x_16);
if (x_17 == 0)
{
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_19 = l_Lean_Parser_interpolatedStrFn_parse___closed__1;
lean_inc(x_5);
x_20 = l_Lean_Parser_mkNodeToken(x_19, x_4, x_5, x_11);
lean_inc(x_1);
lean_inc(x_5);
x_21 = lean_apply_2(x_1, x_5, x_20);
x_35 = lean_ctor_get(x_21, 4);
lean_inc(x_35);
x_36 = lean_box(0);
x_37 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Parser_ParserState_mkNode_spec__0(x_35, x_36);
if (x_37 == 0)
{
x_22 = x_17;
goto block_34;
}
else
{
x_22 = x_15;
goto block_34;
}
block_34:
{
if (x_22 == 0)
{
lean_object* x_23; uint32_t x_24; uint32_t x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
x_24 = lean_string_utf8_get(x_2, x_23);
x_25 = 125;
x_26 = lean_uint32_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Parser_interpolatedStrFn_parse___closed__2;
x_28 = l_Lean_Parser_ParserState_mkError(x_21, x_27);
x_29 = l_Lean_Parser_interpolatedStrFn_parse___closed__4;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
lean_dec(x_3);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_string_utf8_next(x_2, x_23);
x_32 = l_Lean_Parser_ParserState_setPos(x_21, x_31);
x_4 = x_23;
x_6 = x_32;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = l_Lean_Parser_interpolatedStrFn_parse___closed__5;
x_39 = lean_box(x_15);
x_40 = lean_alloc_closure((void*)(l_Lean_Parser_quotedCharCoreFn___boxed), 4, 2);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn_parse), 6, 4);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_2);
lean_closure_set(x_41, 2, x_3);
lean_closure_set(x_41, 3, x_4);
x_42 = l_Lean_Parser_andthenFn(x_40, x_41, x_5, x_11);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Parser_interpolatedStrFn_parse___closed__1;
x_44 = l_Lean_Parser_mkNodeToken(x_43, x_4, x_5, x_11);
x_45 = l_Lean_Parser_interpolatedStrFn_parse___closed__4;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_3);
lean_dec(x_3);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_47 = l_Lean_Parser_interpolatedStrFn_parse___closed__6;
x_48 = l_Lean_Parser_ParserState_mkError(x_6, x_47);
x_49 = l_Lean_Parser_interpolatedStrFn_parse___closed__4;
x_50 = l_Lean_Parser_ParserState_mkNode(x_48, x_49, x_3);
lean_dec(x_3);
return x_50;
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolated string", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_string_utf8_at_end(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_8, x_9);
x_12 = 34;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
goto block_6;
}
else
{
if (x_10 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Parser_ParserState_stackSize(x_3);
x_15 = l_Lean_Parser_ParserState_next(x_3, x_8, x_9);
x_16 = l_Lean_Parser_interpolatedStrFn_parse(x_1, x_8, x_14, x_9, x_2, x_15);
return x_16;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
goto block_6;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_17);
return x_18;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_interpolatedStrFn___closed__0;
x_5 = l_Lean_Parser_ParserState_mkError(x_3, x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__0;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_withoutPosition(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_7, 0, x_4);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__0;
x_2 = l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1;
x_3 = l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The parser `interpolatedStr(p)` parses a string literal like `\"foo\"` (see `str`), but the string\nmay also contain `{}` escapes, and within the escapes the parser `p` is used. For example,\n`interpolatedStr(term)` will parse `\"foo {2 + 2}\"`, where `2 + 2` is parsed as a term rather than\nas a string. Note that the full Lean term grammar is available here, including string literals,\nso for example `\"foo {\"bar\" ++ \"baz\"}\"` is a legal interpolated string (which evaluates to\n`foo barbaz`).\n\nThis parser has arity 1, and returns a `interpolatedStrKind` with an odd number of arguments,\nalternating between chunks of literal text and results from `p`. The literal chunks contain\nuninterpreted substrings of the input. For example, `\"foo\\n{2 + 2}\"` would have three arguments:\nan atom `\"foo\\n{`, the parsed `2 + 2` term, and then the atom `}\"`. ", 840, 840);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2;
x_3 = l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = l_Lean_Parser_interpolatedStrFn_parse___closed__4;
x_4 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__0;
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_withoutPosition(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = l_Lean_Parser_interpolatedStr___closed__0;
x_7 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_8, 0, x_4);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
x_9 = l_Lean_Parser_withAntiquot(x_6, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Parser_interpolatedStr___closed__0;
x_12 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_withAntiquot(x_11, x_14);
return x_15;
}
}
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_interpolatedStrFn_parse___closed__0 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__0();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__0);
l_Lean_Parser_interpolatedStrFn_parse___closed__1 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__1);
l_Lean_Parser_interpolatedStrFn_parse___closed__2 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__2);
l_Lean_Parser_interpolatedStrFn_parse___closed__3 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__3();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__3);
l_Lean_Parser_interpolatedStrFn_parse___closed__4 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__4();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__4);
l_Lean_Parser_interpolatedStrFn_parse___closed__5 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__5();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__5);
l_Lean_Parser_interpolatedStrFn_parse___closed__6 = _init_l_Lean_Parser_interpolatedStrFn_parse___closed__6();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn_parse___closed__6);
l_Lean_Parser_interpolatedStrFn___closed__0 = _init_l_Lean_Parser_interpolatedStrFn___closed__0();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn___closed__0);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__0 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__0();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__0);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__1 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__1);
l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0 = _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0);
l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1 = _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1);
l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2 = _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2);
l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3 = _init_l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3);
if (builtin) {res = l_Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_interpolatedStr___closed__0 = _init_l_Lean_Parser_interpolatedStr___closed__0();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
