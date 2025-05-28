// Lean compiler output
// Module: Std.Internal.Parsec.Basic
// Imports: Init.NotationExtra Init.Data.ToString.Macro
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_expectedEndOfInput;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instAlternative___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___rarg(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__9;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_unexpectedEndOfInput;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__7;
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__7;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_satisfy___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__6;
static lean_object* l_Std_Internal_Parsec_expectedEndOfInput___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__4;
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__8;
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__6;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instInhabited___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__10;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__5;
static lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instAlternative___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_instMonad___closed__1;
static lean_object* l_Std_Internal_Parsec_unexpectedEndOfInput___closed__1;
static lean_object* l_Std_Internal_Parsec_instMonad___closed__8;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_many___rarg___closed__1;
static lean_object* l_Std_Internal_Parsec_instMonad___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Internal.Parsec.ParseResult.success", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Internal.Parsec.ParseResult.error", 37, 37);
return x_1;
}
}
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__7;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = lean_nat_dec_le(x_8, x_4);
x_10 = lean_apply_2(x_2, x_6, x_8);
x_11 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__3;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_apply_2(x_1, x_7, x_8);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
if (x_9 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = 0;
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = l_Repr_addAppParen(x_19, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
x_23 = 0;
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = l_Repr_addAppParen(x_24, x_4);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_4);
x_30 = lean_apply_2(x_2, x_26, x_28);
x_31 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__3;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_apply_2(x_1, x_27, x_28);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
if (x_29 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = 0;
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = l_Repr_addAppParen(x_40, x_4);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
x_44 = 0;
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = l_Repr_addAppParen(x_45, x_4);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_4);
x_52 = lean_apply_2(x_2, x_48, x_50);
x_53 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__8;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_52);
lean_ctor_set(x_3, 0, x_53);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_String_quote(x_49);
lean_dec(x_49);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
if (x_51 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4;
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = 0;
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = l_Repr_addAppParen(x_62, x_4);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5;
x_65 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
x_66 = 0;
x_67 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = l_Repr_addAppParen(x_67, x_4);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_3, 0);
x_70 = lean_ctor_get(x_3, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_3);
x_71 = lean_unsigned_to_nat(1024u);
x_72 = lean_nat_dec_le(x_71, x_4);
x_73 = lean_apply_2(x_2, x_69, x_71);
x_74 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__8;
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_box(1);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_String_quote(x_70);
lean_dec(x_70);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
if (x_72 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4;
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = 0;
x_84 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = l_Repr_addAppParen(x_84, x_4);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_86 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5;
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_80);
x_88 = 0;
x_89 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = l_Repr_addAppParen(x_89, x_4);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instReprParseResult___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instInhabited___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_instInhabited___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instInhabited___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_pure___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_bind___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instMonad___lambda__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instMonad___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_Parsec_instMonad___closed__1;
x_2 = l_Std_Internal_Parsec_instMonad___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instMonad___lambda__3), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instMonad___lambda__4), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instMonad___lambda__5), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instMonad___lambda__6), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Internal_Parsec_instMonad___closed__3;
x_2 = l_Std_Internal_Parsec_instMonad___closed__4;
x_3 = l_Std_Internal_Parsec_instMonad___closed__5;
x_4 = l_Std_Internal_Parsec_instMonad___closed__6;
x_5 = l_Std_Internal_Parsec_instMonad___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_bind), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instMonad___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_Parsec_instMonad___closed__8;
x_2 = l_Std_Internal_Parsec_instMonad___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_instMonad___closed__10;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_fail___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_8);
x_9 = lean_apply_1(x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_2(x_6, x_11, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_16);
x_17 = lean_apply_1(x_16, x_8);
lean_inc(x_14);
x_18 = lean_apply_1(x_16, x_14);
x_19 = lean_apply_2(x_1, x_17, x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_9);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_7, x_21, x_14);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
lean_inc(x_25);
x_26 = lean_apply_1(x_25, x_8);
lean_inc(x_23);
x_27 = lean_apply_1(x_25, x_23);
x_28 = lean_apply_2(x_1, x_26, x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = lean_apply_2(x_7, x_31, x_23);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_tryCatch___rarg___boxed), 8, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_Parsec_tryCatch___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_6);
x_7 = lean_apply_1(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_15);
x_16 = lean_apply_1(x_15, x_6);
lean_inc(x_13);
x_17 = lean_apply_1(x_15, x_13);
x_18 = lean_apply_2(x_1, x_16, x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_5, x_20, x_13);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
lean_inc(x_24);
x_25 = lean_apply_1(x_24, x_6);
lean_inc(x_22);
x_26 = lean_apply_1(x_24, x_22);
x_27 = lean_apply_2(x_1, x_25, x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_apply_2(x_5, x_30, x_22);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_orElse___rarg___boxed), 6, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_orElse___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_attempt___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Parsec_instInhabited___rarg___closed__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_6);
x_7 = lean_apply_1(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_15);
x_16 = lean_apply_1(x_15, x_6);
lean_inc(x_13);
x_17 = lean_apply_1(x_15, x_13);
x_18 = lean_apply_2(x_2, x_16, x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_5, x_20, x_13);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_24);
x_25 = lean_apply_1(x_24, x_6);
lean_inc(x_22);
x_26 = lean_apply_1(x_24, x_22);
x_27 = lean_apply_2(x_2, x_25, x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_apply_2(x_5, x_30, x_22);
return x_31;
}
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_instAlternative___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Parsec_instMonad(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instAlternative___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___rarg___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Std_Internal_Parsec_instAlternative___rarg___closed__1;
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___rarg___lambda__2), 6, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
x_7 = l_Std_Internal_Parsec_instAlternative___rarg___closed__2;
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_Parsec_instAlternative___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_expectedEndOfInput___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected end of input", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_expectedEndOfInput() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Parsec_expectedEndOfInput___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Internal_Parsec_expectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_eof___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_eof(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_isEof___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_isEof(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_6);
x_7 = lean_apply_1(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_push(x_5, x_9);
x_5 = x_10;
x_6 = x_8;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_15);
x_16 = lean_apply_1(x_15, x_6);
lean_inc(x_13);
x_17 = lean_apply_1(x_15, x_13);
x_18 = lean_apply_2(x_1, x_16, x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_dec(x_14);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_22);
x_23 = lean_apply_1(x_22, x_6);
lean_inc(x_20);
x_24 = lean_apply_1(x_22, x_20);
x_25 = lean_apply_2(x_1, x_23, x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_manyCore___rarg___boxed), 6, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_manyCore___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Std_Internal_Parsec_many___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_Internal_Parsec_many___rarg___closed__1;
x_7 = l_Std_Internal_Parsec_manyCore___rarg(x_1, x_2, x_3, x_4, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_many___rarg___boxed), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_many___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
x_12 = l_Std_Internal_Parsec_manyCore___rarg(x_1, x_2, x_3, x_4, x_11, x_7);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_many1___rarg___boxed), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_many1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_Parsec_unexpectedEndOfInput___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_unexpectedEndOfInput() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Parsec_unexpectedEndOfInput___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_apply_2(x_8, x_2, lean_box(0));
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_10, x_2, lean_box(0));
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_any___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_any(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_Parsec_satisfy___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("condition not satisfied", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_inc(x_3);
x_10 = lean_apply_2(x_9, x_3, lean_box(0));
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_11, x_3, lean_box(0));
lean_inc(x_10);
x_13 = lean_apply_1(x_2, x_10);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
x_15 = l_Std_Internal_Parsec_satisfy___rarg___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_satisfy___rarg), 3, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_satisfy(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Std_Internal_Parsec_instInhabited___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = l_Std_Internal_Parsec_instInhabited___rarg___closed__1;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_notFollowedBy___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_2);
x_9 = lean_apply_2(x_8, x_2, lean_box(0));
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_peek_x3f___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_peek_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_2);
x_9 = lean_apply_2(x_8, x_2, lean_box(0));
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_peek_x21___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_peek_x21(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_8, x_3, lean_box(0));
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_peekD___rarg), 3, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_peekD(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_8, x_2, lean_box(0));
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_skip___rarg), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_skip(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_6);
x_7 = lean_apply_1(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unbox_uint32(x_9);
lean_dec(x_9);
x_11 = lean_string_push(x_5, x_10);
x_5 = x_11;
x_6 = x_8;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_16);
x_17 = lean_apply_1(x_16, x_6);
lean_inc(x_14);
x_18 = lean_apply_1(x_16, x_14);
x_19 = lean_apply_2(x_1, x_17, x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
lean_dec(x_15);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
lean_inc(x_23);
x_24 = lean_apply_1(x_23, x_6);
lean_inc(x_21);
x_25 = lean_apply_1(x_23, x_21);
x_26 = lean_apply_2(x_1, x_24, x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_5);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_manyCharsCore___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_manyCharsCore___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_Internal_Parsec_instInhabited___rarg___closed__1;
x_7 = l_Std_Internal_Parsec_manyCharsCore___rarg(x_1, x_2, x_3, x_4, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_manyChars___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_manyChars___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_Internal_Parsec_instInhabited___rarg___closed__1;
x_10 = lean_unbox_uint32(x_8);
lean_dec(x_8);
x_11 = lean_string_push(x_9, x_10);
x_12 = l_Std_Internal_Parsec_manyCharsCore___rarg(x_1, x_2, x_3, x_4, x_11, x_7);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_many1Chars___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_many1Chars___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__1 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__1();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__1);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__2 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__2();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__2);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__3 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__3();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__3);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__4);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__5);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__6 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__6();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__6);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__7 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__7();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__7);
l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__8 = _init_l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__8();
lean_mark_persistent(l___private_Std_Internal_Parsec_Basic_0__Std_Internal_Parsec_reprParseResult____x40_Std_Internal_Parsec_Basic___hyg_60____rarg___closed__8);
l_Std_Internal_Parsec_instInhabited___rarg___closed__1 = _init_l_Std_Internal_Parsec_instInhabited___rarg___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_instInhabited___rarg___closed__1);
l_Std_Internal_Parsec_instMonad___closed__1 = _init_l_Std_Internal_Parsec_instMonad___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__1);
l_Std_Internal_Parsec_instMonad___closed__2 = _init_l_Std_Internal_Parsec_instMonad___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__2);
l_Std_Internal_Parsec_instMonad___closed__3 = _init_l_Std_Internal_Parsec_instMonad___closed__3();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__3);
l_Std_Internal_Parsec_instMonad___closed__4 = _init_l_Std_Internal_Parsec_instMonad___closed__4();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__4);
l_Std_Internal_Parsec_instMonad___closed__5 = _init_l_Std_Internal_Parsec_instMonad___closed__5();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__5);
l_Std_Internal_Parsec_instMonad___closed__6 = _init_l_Std_Internal_Parsec_instMonad___closed__6();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__6);
l_Std_Internal_Parsec_instMonad___closed__7 = _init_l_Std_Internal_Parsec_instMonad___closed__7();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__7);
l_Std_Internal_Parsec_instMonad___closed__8 = _init_l_Std_Internal_Parsec_instMonad___closed__8();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__8);
l_Std_Internal_Parsec_instMonad___closed__9 = _init_l_Std_Internal_Parsec_instMonad___closed__9();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__9);
l_Std_Internal_Parsec_instMonad___closed__10 = _init_l_Std_Internal_Parsec_instMonad___closed__10();
lean_mark_persistent(l_Std_Internal_Parsec_instMonad___closed__10);
l_Std_Internal_Parsec_instAlternative___rarg___closed__1 = _init_l_Std_Internal_Parsec_instAlternative___rarg___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_instAlternative___rarg___closed__1);
l_Std_Internal_Parsec_instAlternative___rarg___closed__2 = _init_l_Std_Internal_Parsec_instAlternative___rarg___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_instAlternative___rarg___closed__2);
l_Std_Internal_Parsec_expectedEndOfInput___closed__1 = _init_l_Std_Internal_Parsec_expectedEndOfInput___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_expectedEndOfInput___closed__1);
l_Std_Internal_Parsec_expectedEndOfInput = _init_l_Std_Internal_Parsec_expectedEndOfInput();
lean_mark_persistent(l_Std_Internal_Parsec_expectedEndOfInput);
l_Std_Internal_Parsec_many___rarg___closed__1 = _init_l_Std_Internal_Parsec_many___rarg___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_many___rarg___closed__1);
l_Std_Internal_Parsec_unexpectedEndOfInput___closed__1 = _init_l_Std_Internal_Parsec_unexpectedEndOfInput___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_unexpectedEndOfInput___closed__1);
l_Std_Internal_Parsec_unexpectedEndOfInput = _init_l_Std_Internal_Parsec_unexpectedEndOfInput();
lean_mark_persistent(l_Std_Internal_Parsec_unexpectedEndOfInput);
l_Std_Internal_Parsec_satisfy___rarg___closed__1 = _init_l_Std_Internal_Parsec_satisfy___rarg___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_satisfy___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
