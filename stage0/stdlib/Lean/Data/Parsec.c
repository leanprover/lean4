// Lean compiler output
// Module: Lean.Data.Parsec
// Imports: Init
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
static lean_object* l_Lean_Parsec_instMonadParsec___closed__9;
static lean_object* l_Lean_Parsec_unexpectedEndOfInput___closed__1;
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_Parsec_instMonadParsec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parsec_instAlternativeParsec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_orElse(lean_object*);
static lean_object* l_Lean_Parsec_instMonadParsec___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instInhabitedParsec(lean_object*);
static lean_object* l_Lean_Parsec_instMonadParsec___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parsec_expectedEndOfInput;
LEAN_EXPORT lean_object* l_Lean_Parsec_many1___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parsec_instAlternativeParsec;
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_instAlternativeParsec___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parsec_many1Chars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_manyChars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instReprParseResult___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instAlternativeParsec___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_pchar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_satisfy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_eof(lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6;
static lean_object* l_Lean_Parsec_instAlternativeParsec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parsec_digit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_many(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_pstring___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_pstring___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_attempt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_skipChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_bind(lean_object*, lean_object*);
lean_object* l_String_Iterator_forward(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_asciiLetter___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parsec_peek_x3f(lean_object*);
lean_object* l_String_Iterator_extract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_anyChar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_notFollowedBy___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_many___rarg___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__10;
static lean_object* l_Lean_Parsec_instMonadParsec___closed__1;
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parsec_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_many___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parsec_attempt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec;
LEAN_EXPORT lean_object* l_Lean_Parsec_pstring(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_instMonadParsec___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parsec_instInhabitedParsec___rarg(lean_object*);
uint8_t l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_many1(lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_peek_x21(lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parsec_fail___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_pchar___closed__2;
static lean_object* l_Lean_Parsec_pchar___closed__1;
static lean_object* l_Lean_Parsec_expectedEndOfInput___closed__1;
uint8_t l_String_Iterator_hasNext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_pchar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_manyCore(lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parsec_notFollowedBy(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
static lean_object* l_Lean_Parsec_digit___closed__1;
static lean_object* l_Lean_Parsec_instMonadParsec___closed__5;
static lean_object* l_Lean_Parsec_instMonadParsec___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__12;
static lean_object* l_Lean_Parsec_satisfy___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instReprParseResult(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_unexpectedEndOfInput;
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_manyCharsCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_manyCore___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_skipChar(uint32_t, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_asciiLetter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_skip(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_orElse___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_hexDigit(lean_object*);
static lean_object* l_Lean_Parsec_instMonadParsec___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
static lean_object* l_Lean_Parsec_many1___rarg___closed__1;
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parsec_ws(lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__4;
static lean_object* l_Lean_Parsec_instAlternativeParsec___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parsec_skipString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parsec_skipString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_skipWs(lean_object*);
static lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__2;
static lean_object* l_Lean_Parsec_instMonadParsec___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parsec_fail(lean_object*);
static lean_object* l_Lean_Parsec_hexDigit___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parsec.ParseResult.success");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String.Iterator.mk ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parsec.ParseResult.error");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__11;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_nat_dec_le(x_6, x_3);
x_8 = lean_apply_2(x_1, x_5, x_6);
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_String_quote(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Nat_repr(x_10);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Repr_addAppParen(x_19, x_6);
x_21 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__3;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
x_26 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__4;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = 0;
x_29 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = l_Repr_addAppParen(x_29, x_3);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_dec(x_4);
x_33 = l_String_quote(x_31);
lean_dec(x_31);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Nat_repr(x_32);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Repr_addAppParen(x_41, x_6);
x_43 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__3;
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
x_48 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__9;
x_49 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = 0;
x_51 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = l_Repr_addAppParen(x_51, x_3);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_dec(x_2);
x_55 = lean_unsigned_to_nat(1024u);
x_56 = lean_nat_dec_le(x_55, x_3);
x_57 = l_String_quote(x_54);
lean_dec(x_54);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (x_56 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_dec(x_53);
x_61 = l_String_quote(x_59);
lean_dec(x_59);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6;
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8;
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Nat_repr(x_60);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Repr_addAppParen(x_69, x_55);
x_71 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__12;
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_box(1);
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_58);
x_76 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__4;
x_77 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = 0;
x_79 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = l_Repr_addAppParen(x_79, x_3);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_81 = lean_ctor_get(x_53, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_53, 1);
lean_inc(x_82);
lean_dec(x_53);
x_83 = l_String_quote(x_81);
lean_dec(x_81);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6;
x_86 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8;
x_88 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Nat_repr(x_82);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Repr_addAppParen(x_91, x_55);
x_93 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__12;
x_94 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_box(1);
x_96 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_58);
x_98 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__9;
x_99 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = 0;
x_101 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
x_102 = l_Repr_addAppParen(x_101, x_3);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instReprParseResult___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instReprParseResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_instReprParseResult___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parsec_instInhabitedParsec___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instInhabitedParsec___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instInhabitedParsec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_instInhabitedParsec___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_pure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_pure___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, x_6, x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parsec_bind___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_apply_1(x_3, x_8);
lean_ctor_set(x_6, 1, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_apply_1(x_3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_apply_1(x_8, x_12);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_apply_1(x_8, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_dec(x_12);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_4, x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instMonadParsec___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_4, x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instMonadParsec___lambda__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instMonadParsec___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parsec_instMonadParsec___closed__1;
x_2 = l_Lean_Parsec_instMonadParsec___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instMonadParsec___lambda__3), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instMonadParsec___lambda__4), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instMonadParsec___lambda__5), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instMonadParsec___lambda__6), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parsec_instMonadParsec___closed__3;
x_2 = l_Lean_Parsec_instMonadParsec___closed__4;
x_3 = l_Lean_Parsec_instMonadParsec___closed__5;
x_4 = l_Lean_Parsec_instMonadParsec___closed__6;
x_5 = l_Lean_Parsec_instMonadParsec___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instMonadParsec___lambda__7), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parsec_instMonadParsec___closed__8;
x_2 = l_Lean_Parsec_instMonadParsec___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parsec_instMonadParsec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parsec_instMonadParsec___closed__10;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_fail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_fail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_fail___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_10);
if (x_12 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_2, x_13, x_3);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_2, x_19, x_3);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_orElse___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_attempt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_attempt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_attempt___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instAlternativeParsec___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_instAlternativeParsec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_4, x_11);
if (x_13 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_3, x_14, x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_4, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_3, x_20, x_4);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Lean_Parsec_instAlternativeParsec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instAlternativeParsec___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instAlternativeParsec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_instAlternativeParsec___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_instAlternativeParsec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parsec_instMonadParsec;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parsec_instAlternativeParsec___closed__1;
x_4 = l_Lean_Parsec_instAlternativeParsec___closed__2;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parsec_instAlternativeParsec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parsec_instAlternativeParsec___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_expectedEndOfInput___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected end of input");
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_expectedEndOfInput() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parsec_expectedEndOfInput___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_eof(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_expectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_manyCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = lean_array_push(x_2, x_6);
x_8 = l_Lean_Parsec_manyCore(lean_box(0));
x_9 = lean_apply_3(x_8, x_1, x_7, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_15);
if (x_17 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
x_26 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_24);
if (x_26 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_2);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_manyCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_manyCore___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parsec_many___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_many___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parsec_many___rarg___closed__1;
x_4 = l_Lean_Parsec_manyCore(lean_box(0));
x_5 = lean_apply_3(x_4, x_1, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_many(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_many___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parsec_many1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_many1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Parsec_many1___rarg___closed__1;
x_7 = lean_array_push(x_6, x_5);
x_8 = l_Lean_Parsec_manyCore(lean_box(0));
x_9 = lean_apply_3(x_8, x_1, x_7, x_4);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_many1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_many1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_manyCharsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unbox_uint32(x_6);
lean_dec(x_6);
lean_inc(x_2);
x_8 = lean_string_push(x_2, x_7);
x_9 = l_Lean_Parsec_manyCharsCore(x_1, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_15);
if (x_17 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
x_26 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_24);
if (x_26 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_2);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_manyChars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_4 = l_Lean_Parsec_manyCharsCore(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_many1Chars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_7 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_8 = lean_string_push(x_6, x_7);
x_9 = l_Lean_Parsec_manyCharsCore(x_1, x_8, x_4);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Parsec_pstring___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_pstring(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_string_length(x_1);
lean_inc(x_2);
x_4 = l_String_Iterator_forward(x_2, x_3);
x_5 = l_String_Iterator_extract(x_2, x_4);
x_6 = lean_string_dec_eq(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = l_Lean_Parsec_pstring___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_pstring___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parsec_pstring(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_skipString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parsec_pstring(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_skipString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parsec_skipString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parsec_unexpectedEndOfInput___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected end of input");
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_unexpectedEndOfInput() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parsec_unexpectedEndOfInput___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_anyChar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
lean_dec(x_1);
x_7 = lean_box_uint32(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Parsec_pchar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected: '");
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_pchar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_pchar(uint32_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Iterator_hasNext(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parsec_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_2);
x_6 = l_String_Iterator_next(x_2);
x_7 = l_String_Iterator_curr(x_2);
x_8 = x_7 == x_1;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_9 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_10 = lean_string_push(x_9, x_1);
x_11 = l_Lean_Parsec_pchar___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Parsec_pchar___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_box_uint32(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_pchar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parsec_pchar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_skipChar(uint32_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Iterator_hasNext(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parsec_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_2);
x_6 = l_String_Iterator_next(x_2);
x_7 = l_String_Iterator_curr(x_2);
x_8 = x_7 == x_1;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_9 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_10 = lean_string_push(x_9, x_1);
x_11 = l_Lean_Parsec_pchar___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Parsec_pchar___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_skipChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parsec_skipChar(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parsec_digit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("digit expected");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_digit(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
x_7 = 48;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = l_Lean_Parsec_digit___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 57;
x_12 = x_6 <= x_11;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_Lean_Parsec_digit___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_box_uint32(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
static lean_object* _init_l_Lean_Parsec_hexDigit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hex digit expected");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_hexDigit(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_32; uint8_t x_33; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
x_32 = 48;
x_33 = x_32 <= x_6;
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_7 = x_34;
goto block_31;
}
else
{
uint32_t x_35; uint8_t x_36; 
x_35 = 57;
x_36 = x_6 <= x_35;
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_7 = x_37;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_box_uint32(x_6);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
block_31:
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = 97;
x_9 = x_8 <= x_6;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 65;
x_11 = x_10 <= x_6;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l_Lean_Parsec_hexDigit___closed__1;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = x_6 <= x_10;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l_Lean_Parsec_hexDigit___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box_uint32(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = x_6 <= x_8;
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 65;
x_21 = x_20 <= x_6;
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_22 = l_Lean_Parsec_hexDigit___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = x_6 <= x_20;
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_25 = l_Lean_Parsec_hexDigit___closed__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box_uint32(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_box_uint32(x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Parsec_asciiLetter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ASCII letter expected");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_asciiLetter(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
x_7 = 65;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 97;
x_10 = x_9 <= x_6;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Lean_Parsec_asciiLetter___closed__1;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 122;
x_14 = x_6 <= x_13;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l_Lean_Parsec_asciiLetter___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box_uint32(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 90;
x_20 = x_6 <= x_19;
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 97;
x_22 = x_21 <= x_6;
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = l_Lean_Parsec_asciiLetter___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 122;
x_26 = x_6 <= x_25;
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_27 = l_Lean_Parsec_asciiLetter___closed__1;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_box_uint32(x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_box_uint32(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Parsec_satisfy___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("condition not satisfied");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_satisfy(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Iterator_hasNext(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = l_Lean_Parsec_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_6 = l_String_Iterator_next(x_2);
x_7 = l_String_Iterator_curr(x_2);
x_8 = lean_box_uint32(x_7);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = l_Lean_Parsec_satisfy___closed__1;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_box_uint32(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_notFollowedBy___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = l_Lean_Parsec_instInhabitedParsec___rarg___closed__1;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_notFollowedBy(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_notFollowedBy___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_skipWs(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_3 = l_String_Iterator_curr(x_1);
x_4 = 9;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 10;
x_7 = x_3 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 13;
x_9 = x_3 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 32;
x_11 = x_3 == x_10;
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; 
x_12 = l_String_Iterator_next(x_1);
x_1 = x_12;
goto _start;
}
}
else
{
lean_object* x_14; 
x_14 = l_String_Iterator_next(x_1);
x_1 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; 
x_16 = l_String_Iterator_next(x_1);
x_1 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; 
x_18 = l_String_Iterator_next(x_1);
x_1 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_peek_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = lean_box_uint32(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_peek_x21(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = lean_box_uint32(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_skip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_String_Iterator_next(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_ws(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parsec_skipWs(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Parsec(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__1 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__1();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__1);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__2 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__2();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__2);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__3 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__3();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__3);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__4 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__4();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__4);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__5 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__5();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__5);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__6);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__7 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__7();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__7);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__8);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__9 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__9();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__9);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__10 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__10();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__10);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__11 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__11();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__11);
l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__12 = _init_l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__12();
lean_mark_persistent(l___private_Lean_Data_Parsec_0__Lean_Parsec_reprParseResult____x40_Lean_Data_Parsec___hyg_44____rarg___closed__12);
l_Lean_Parsec_instInhabitedParsec___rarg___closed__1 = _init_l_Lean_Parsec_instInhabitedParsec___rarg___closed__1();
lean_mark_persistent(l_Lean_Parsec_instInhabitedParsec___rarg___closed__1);
l_Lean_Parsec_instMonadParsec___closed__1 = _init_l_Lean_Parsec_instMonadParsec___closed__1();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__1);
l_Lean_Parsec_instMonadParsec___closed__2 = _init_l_Lean_Parsec_instMonadParsec___closed__2();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__2);
l_Lean_Parsec_instMonadParsec___closed__3 = _init_l_Lean_Parsec_instMonadParsec___closed__3();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__3);
l_Lean_Parsec_instMonadParsec___closed__4 = _init_l_Lean_Parsec_instMonadParsec___closed__4();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__4);
l_Lean_Parsec_instMonadParsec___closed__5 = _init_l_Lean_Parsec_instMonadParsec___closed__5();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__5);
l_Lean_Parsec_instMonadParsec___closed__6 = _init_l_Lean_Parsec_instMonadParsec___closed__6();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__6);
l_Lean_Parsec_instMonadParsec___closed__7 = _init_l_Lean_Parsec_instMonadParsec___closed__7();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__7);
l_Lean_Parsec_instMonadParsec___closed__8 = _init_l_Lean_Parsec_instMonadParsec___closed__8();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__8);
l_Lean_Parsec_instMonadParsec___closed__9 = _init_l_Lean_Parsec_instMonadParsec___closed__9();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__9);
l_Lean_Parsec_instMonadParsec___closed__10 = _init_l_Lean_Parsec_instMonadParsec___closed__10();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec___closed__10);
l_Lean_Parsec_instMonadParsec = _init_l_Lean_Parsec_instMonadParsec();
lean_mark_persistent(l_Lean_Parsec_instMonadParsec);
l_Lean_Parsec_instAlternativeParsec___closed__1 = _init_l_Lean_Parsec_instAlternativeParsec___closed__1();
lean_mark_persistent(l_Lean_Parsec_instAlternativeParsec___closed__1);
l_Lean_Parsec_instAlternativeParsec___closed__2 = _init_l_Lean_Parsec_instAlternativeParsec___closed__2();
lean_mark_persistent(l_Lean_Parsec_instAlternativeParsec___closed__2);
l_Lean_Parsec_instAlternativeParsec___closed__3 = _init_l_Lean_Parsec_instAlternativeParsec___closed__3();
lean_mark_persistent(l_Lean_Parsec_instAlternativeParsec___closed__3);
l_Lean_Parsec_instAlternativeParsec = _init_l_Lean_Parsec_instAlternativeParsec();
lean_mark_persistent(l_Lean_Parsec_instAlternativeParsec);
l_Lean_Parsec_expectedEndOfInput___closed__1 = _init_l_Lean_Parsec_expectedEndOfInput___closed__1();
lean_mark_persistent(l_Lean_Parsec_expectedEndOfInput___closed__1);
l_Lean_Parsec_expectedEndOfInput = _init_l_Lean_Parsec_expectedEndOfInput();
lean_mark_persistent(l_Lean_Parsec_expectedEndOfInput);
l_Lean_Parsec_many___rarg___closed__1 = _init_l_Lean_Parsec_many___rarg___closed__1();
lean_mark_persistent(l_Lean_Parsec_many___rarg___closed__1);
l_Lean_Parsec_many1___rarg___closed__1 = _init_l_Lean_Parsec_many1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parsec_many1___rarg___closed__1);
l_Lean_Parsec_pstring___closed__1 = _init_l_Lean_Parsec_pstring___closed__1();
lean_mark_persistent(l_Lean_Parsec_pstring___closed__1);
l_Lean_Parsec_unexpectedEndOfInput___closed__1 = _init_l_Lean_Parsec_unexpectedEndOfInput___closed__1();
lean_mark_persistent(l_Lean_Parsec_unexpectedEndOfInput___closed__1);
l_Lean_Parsec_unexpectedEndOfInput = _init_l_Lean_Parsec_unexpectedEndOfInput();
lean_mark_persistent(l_Lean_Parsec_unexpectedEndOfInput);
l_Lean_Parsec_pchar___closed__1 = _init_l_Lean_Parsec_pchar___closed__1();
lean_mark_persistent(l_Lean_Parsec_pchar___closed__1);
l_Lean_Parsec_pchar___closed__2 = _init_l_Lean_Parsec_pchar___closed__2();
lean_mark_persistent(l_Lean_Parsec_pchar___closed__2);
l_Lean_Parsec_digit___closed__1 = _init_l_Lean_Parsec_digit___closed__1();
lean_mark_persistent(l_Lean_Parsec_digit___closed__1);
l_Lean_Parsec_hexDigit___closed__1 = _init_l_Lean_Parsec_hexDigit___closed__1();
lean_mark_persistent(l_Lean_Parsec_hexDigit___closed__1);
l_Lean_Parsec_asciiLetter___closed__1 = _init_l_Lean_Parsec_asciiLetter___closed__1();
lean_mark_persistent(l_Lean_Parsec_asciiLetter___closed__1);
l_Lean_Parsec_satisfy___closed__1 = _init_l_Lean_Parsec_satisfy___closed__1();
lean_mark_persistent(l_Lean_Parsec_satisfy___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
