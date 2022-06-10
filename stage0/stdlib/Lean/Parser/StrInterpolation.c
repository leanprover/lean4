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
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__5;
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_interpolatedStrKind;
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__4;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStr___elambda__1___closed__1;
static lean_object* l_Lean_Parser_interpolatedStr___elambda__1___closed__2;
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__2;
static lean_object* l_Lean_Parser_interpolatedStrFn___closed__1;
static lean_object* l_Lean_Parser_interpolatedStr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot;
static lean_object* l_Lean_Parser_interpolatedStrFn_parse___closed__3;
static lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__3;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr;
static lean_object* l_Lean_Parser_interpolatedStrFn___closed__2;
static lean_object* l_Lean_Parser_interpolatedStr___closed__1;
static lean_object* l_Lean_Parser_interpolatedStr___closed__2;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_ParserState_setError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__2;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_822____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_interpolatedStrNoAntiquot___closed__4;
extern lean_object* l_Lean_interpolatedStrLitKind;
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
uint8_t x_5; 
x_5 = 1;
return x_5;
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
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_interpolatedStrFn_parse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'}'", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_isQuotableCharForStrInterpolant___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn_parse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unterminated string literal", 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_get(x_1, x_6);
x_9 = lean_string_utf8_next(x_1, x_6);
lean_dec(x_6);
x_10 = l_Lean_Parser_ParserState_setPos(x_5, x_9);
x_11 = 34;
x_12 = lean_uint32_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 92;
x_14 = lean_uint32_dec_eq(x_8, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 123;
x_16 = lean_uint32_dec_eq(x_8, x_15);
if (x_16 == 0)
{
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = l_Lean_interpolatedStrLitKind;
x_19 = l_Lean_Parser_mkNodeToken(x_18, x_3, x_4, x_10);
x_20 = l_Lean_Parser_interpolatedStrFn_parse___closed__2;
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_22 = l_Lean_Parser_categoryParser___elambda__1(x_20, x_21, x_4, x_19);
x_23 = lean_ctor_get(x_22, 4);
lean_inc(x_23);
x_24 = lean_box(0);
x_25 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_822____at_Lean_Parser_ParserState_hasError___spec__1(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
x_27 = lean_string_utf8_get(x_1, x_26);
x_28 = 125;
x_29 = lean_uint32_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = l_Lean_Parser_ParserState_pushSyntax(x_22, x_30);
x_32 = l_Lean_interpolatedStrKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_2);
x_34 = l_Lean_Parser_interpolatedStrFn_parse___closed__3;
x_35 = l_Lean_Parser_ParserState_setError(x_33, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_string_utf8_next(x_1, x_26);
x_37 = l_Lean_Parser_ParserState_setPos(x_22, x_36);
x_3 = x_26;
x_5 = x_37;
goto _start;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = l_Lean_Parser_interpolatedStrFn_parse___closed__4;
x_40 = l_Lean_Parser_quotedCharCoreFn(x_39, x_4, x_10);
x_41 = lean_ctor_get(x_40, 4);
lean_inc(x_41);
x_42 = lean_box(0);
x_43 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_822____at_Lean_Parser_ParserState_hasError___spec__1(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_40;
}
else
{
x_5 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Lean_interpolatedStrLitKind;
x_46 = l_Lean_Parser_mkNodeToken(x_45, x_3, x_4, x_10);
lean_dec(x_4);
x_47 = l_Lean_interpolatedStrKind;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_2);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_49 = lean_box(0);
x_50 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_49);
x_51 = l_Lean_interpolatedStrKind;
x_52 = l_Lean_Parser_ParserState_mkNode(x_50, x_51, x_2);
x_53 = l_Lean_Parser_interpolatedStrFn_parse___closed__5;
x_54 = l_Lean_Parser_ParserState_setError(x_52, x_53);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_interpolatedStrFn_parse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("interpolated string", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected end of input", 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_4, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get(x_4, x_7);
x_10 = 34;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_12 = l_Lean_Parser_interpolatedStrFn___closed__1;
x_13 = l_Lean_Parser_ParserState_mkError(x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_ParserState_next(x_2, x_4, x_7);
x_15 = l_Lean_Parser_interpolatedStrFn_parse(x_4, x_6, x_7, x_1, x_14);
lean_dec(x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = l_Lean_Parser_interpolatedStrFn___closed__2;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_17, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("interpolatedStr", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__2;
x_2 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStrNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_interpolatedStrKind;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__2() {
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
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_3 = l_Lean_Parser_interpolatedStr___elambda__1___closed__2;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_get(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = 36;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = l_Lean_Parser_interpolatedStrFn(x_1, x_2);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = l_Lean_Parser_interpolatedStrNoAntiquot___closed__3;
x_13 = 1;
x_14 = l_Lean_Parser_orelseFnCore(x_4, x_12, x_13, x_1, x_2);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___closed__1() {
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
static lean_object* _init_l_Lean_Parser_interpolatedStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStr___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_interpolatedStr___closed__1;
x_2 = l_Lean_Parser_interpolatedStr___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_interpolatedStr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_interpolatedStr___closed__3;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Parser_interpolatedStrFn___closed__1 = _init_l_Lean_Parser_interpolatedStrFn___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn___closed__1);
l_Lean_Parser_interpolatedStrFn___closed__2 = _init_l_Lean_Parser_interpolatedStrFn___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStrFn___closed__2);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__1 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__1);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__2 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__2);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__3 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__3);
l_Lean_Parser_interpolatedStrNoAntiquot___closed__4 = _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__4();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot___closed__4);
l_Lean_Parser_interpolatedStrNoAntiquot = _init_l_Lean_Parser_interpolatedStrNoAntiquot();
lean_mark_persistent(l_Lean_Parser_interpolatedStrNoAntiquot);
l_Lean_Parser_interpolatedStr___elambda__1___closed__1 = _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___elambda__1___closed__1);
l_Lean_Parser_interpolatedStr___elambda__1___closed__2 = _init_l_Lean_Parser_interpolatedStr___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___elambda__1___closed__2);
l_Lean_Parser_interpolatedStr___closed__1 = _init_l_Lean_Parser_interpolatedStr___closed__1();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___closed__1);
l_Lean_Parser_interpolatedStr___closed__2 = _init_l_Lean_Parser_interpolatedStr___closed__2();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___closed__2);
l_Lean_Parser_interpolatedStr___closed__3 = _init_l_Lean_Parser_interpolatedStr___closed__3();
lean_mark_persistent(l_Lean_Parser_interpolatedStr___closed__3);
l_Lean_Parser_interpolatedStr = _init_l_Lean_Parser_interpolatedStr();
lean_mark_persistent(l_Lean_Parser_interpolatedStr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
