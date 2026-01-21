// Lean compiler output
// Module: Std.Internal.Parsec.String
// Imports: public import Std.Internal.Parsec.Basic public import Init.Data.String.Slice public import Init.Data.String.Termination
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(lean_object*);
static lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Std_Internal_Parsec_String_digit___closed__1;
static lean_object* l_Std_Internal_Parsec_String_asciiLetter___closed__0;
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed(lean_object*);
uint32_t l_String_Slice_Pos_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Std_Internal_Parsec_String_hexDigit___closed__1;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed(lean_object*);
lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1(lean_object*);
static lean_object* l_Std_Internal_Parsec_String_hexDigit___closed__0;
static lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1;
static lean_object* l_Std_Internal_Parsec_String_asciiLetter___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t);
static lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_pstring___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_pchar___closed__1;
static lean_object* l_Std_Internal_Parsec_String_digit___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1;
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5;
static lean_object* l_Std_Internal_Parsec_String_pchar___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_pchar___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_Pos_next_x21(x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_7);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_byte_size(x_9);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_String_Slice_Pos_next_x21(x_13, x_10);
lean_dec(x_10);
lean_dec_ref(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_Pos_get_x21(x_6, x_3);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_get_fast(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5;
x_2 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4;
x_3 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3;
x_4 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2;
x_5 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1;
x_6 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6;
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("offset ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0;
x_12 = l_Nat_reprFast(x_10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_defWidth;
x_15 = l_Std_Format_pretty(x_13, x_14, x_3, x_3);
x_16 = lean_string_append(x_11, x_15);
lean_dec_ref(x_15);
x_17 = l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1;
x_18 = lean_string_append(x_16, x_17);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_23; 
x_23 = l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2;
x_19 = x_23;
goto block_22;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_9);
x_19 = x_24;
goto block_22;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_Parsec_String_Parser_run___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_pstring___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_string_utf8_byte_size(x_1);
x_12 = lean_nat_sub(x_10, x_9);
x_13 = lean_nat_dec_le(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
goto block_7;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_memcmp(x_8, x_1, x_9, x_14, x_11);
if (x_15 == 0)
{
goto block_7;
}
else
{
uint8_t x_16; 
lean_inc(x_9);
lean_inc(x_8);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 0);
lean_dec(x_18);
x_19 = lean_string_length(x_1);
lean_inc(x_8);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_10);
x_21 = l_String_Slice_Pos_nextn(x_20, x_9, x_19);
lean_dec_ref(x_20);
lean_ctor_set(x_2, 1, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_1);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_23 = lean_string_length(x_1);
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_10);
x_25 = l_String_Slice_Pos_nextn(x_24, x_9, x_23);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
return x_27;
}
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_Internal_Parsec_String_pstring___closed__0;
x_4 = lean_string_append(x_3, x_1);
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_String_pstring(x_1, x_2);
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
static lean_object* _init_l_Std_Internal_Parsec_String_pchar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: '", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_pchar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_pchar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get_fast(x_3, x_4);
x_8 = lean_uint32_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Std_Internal_Parsec_String_pchar___closed__0;
x_10 = l_Std_Internal_Parsec_String_pchar___closed__1;
x_11 = lean_string_push(x_10, x_1);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = l_Std_Internal_Parsec_String_pchar___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_inc(x_4);
lean_inc(x_3);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_20);
x_21 = lean_box_uint32(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_23 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box_uint32(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_String_pchar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get_fast(x_3, x_4);
x_8 = lean_uint32_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Std_Internal_Parsec_String_pchar___closed__0;
x_10 = l_Std_Internal_Parsec_String_pchar___closed__1;
x_11 = lean_string_push(x_10, x_1);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = l_Std_Internal_Parsec_String_pchar___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_inc(x_4);
lean_inc(x_3);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_23 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_String_skipChar(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_digit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("digit expected", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_digit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_Parsec_String_digit___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get_fast(x_5, x_6);
x_10 = 48;
x_11 = lean_uint32_dec_le(x_10, x_9);
if (x_11 == 0)
{
goto block_4;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = lean_uint32_dec_le(x_9, x_12);
if (x_13 == 0)
{
goto block_4;
}
else
{
uint8_t x_14; 
lean_inc(x_6);
lean_inc(x_5);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_17);
x_18 = lean_box_uint32(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_20 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box_uint32(x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_digit___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(48u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get_fast(x_1, x_2);
x_7 = 48;
x_8 = lean_uint32_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 57;
x_11 = lean_uint32_dec_le(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_uint32_to_nat(x_6);
x_14 = lean_unsigned_to_nat(48u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(10u);
x_17 = lean_nat_mul(x_3, x_16);
lean_dec(x_3);
x_18 = lean_nat_add(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
x_19 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_2 = x_19;
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_4, x_5, x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_6, 1, x_8);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_ctor_set(x_2, 1, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_13, x_14, x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_17);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get_fast(x_5, x_6);
x_10 = 48;
x_11 = lean_uint32_dec_le(x_10, x_9);
if (x_11 == 0)
{
goto block_4;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = lean_uint32_dec_le(x_9, x_12);
if (x_13 == 0)
{
goto block_4;
}
else
{
uint8_t x_14; 
lean_inc(x_6);
lean_inc(x_5);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_18 = lean_uint32_to_nat(x_9);
x_19 = lean_unsigned_to_nat(48u);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_18);
x_21 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_5, x_17, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_28 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_29 = lean_uint32_to_nat(x_9);
x_30 = lean_unsigned_to_nat(48u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
x_32 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_5, x_28, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_digit___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_hexDigit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hex digit expected", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_hexDigit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_Parsec_String_hexDigit___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_24; uint8_t x_25; 
x_9 = lean_string_utf8_get_fast(x_5, x_6);
x_10 = lean_string_utf8_next_fast(x_5, x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box_uint32(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_24 = 48;
x_25 = lean_uint32_dec_le(x_24, x_9);
if (x_25 == 0)
{
goto block_23;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 57;
x_27 = lean_uint32_dec_le(x_9, x_26);
if (x_27 == 0)
{
goto block_23;
}
else
{
lean_dec_ref(x_1);
return x_13;
}
}
block_18:
{
uint32_t x_14; uint8_t x_15; 
x_14 = 65;
x_15 = lean_uint32_dec_le(x_14, x_9);
if (x_15 == 0)
{
lean_dec_ref(x_13);
goto block_4;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 70;
x_17 = lean_uint32_dec_le(x_9, x_16);
if (x_17 == 0)
{
lean_dec_ref(x_13);
goto block_4;
}
else
{
lean_dec_ref(x_1);
return x_13;
}
}
}
block_23:
{
uint32_t x_19; uint8_t x_20; 
x_19 = 97;
x_20 = lean_uint32_dec_le(x_19, x_9);
if (x_20 == 0)
{
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 102;
x_22 = lean_uint32_dec_le(x_9, x_21);
if (x_22 == 0)
{
goto block_18;
}
else
{
lean_dec_ref(x_1);
return x_13;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_hexDigit___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_asciiLetter___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ASCII letter expected", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_asciiLetter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_Parsec_String_asciiLetter___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_19; uint8_t x_20; 
x_9 = lean_string_utf8_get_fast(x_5, x_6);
x_10 = lean_string_utf8_next_fast(x_5, x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box_uint32(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_19 = 65;
x_20 = lean_uint32_dec_le(x_19, x_9);
if (x_20 == 0)
{
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 90;
x_22 = lean_uint32_dec_le(x_9, x_21);
if (x_22 == 0)
{
goto block_18;
}
else
{
lean_dec_ref(x_1);
return x_13;
}
}
block_18:
{
uint32_t x_14; uint8_t x_15; 
x_14 = 97;
x_15 = lean_uint32_dec_le(x_14, x_9);
if (x_15 == 0)
{
lean_dec_ref(x_13);
goto block_4;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 122;
x_17 = lean_uint32_dec_le(x_9, x_16);
if (x_17 == 0)
{
lean_dec_ref(x_13);
goto block_4;
}
else
{
lean_dec_ref(x_1);
return x_13;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_asciiLetter___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_2);
x_9 = 9;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 10;
x_12 = lean_uint32_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 13;
x_14 = lean_uint32_dec_eq(x_8, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 32;
x_16 = lean_uint32_dec_eq(x_8, x_15);
if (x_16 == 0)
{
return x_2;
}
else
{
goto block_5;
}
}
else
{
goto block_5;
}
}
else
{
goto block_5;
}
}
else
{
goto block_5;
}
}
else
{
return x_2;
}
block_5:
{
lean_object* x_3; 
x_3 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_2 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_3, x_4);
lean_ctor_set(x_1, 1, x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_inc(x_1);
lean_inc(x_4);
x_8 = l_String_Slice_Pos_nextn(x_7, x_4, x_1);
lean_dec_ref(x_7);
x_9 = lean_string_utf8_extract(x_3, x_4, x_8);
x_10 = lean_string_length(x_9);
x_11 = lean_nat_dec_eq(x_10, x_1);
lean_dec(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_inc(x_3);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
}
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0 = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1 = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2 = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3 = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4 = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5 = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6 = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6);
l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw = _init_l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw);
l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0 = _init_l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0);
l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1 = _init_l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1);
l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2 = _init_l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2);
l_Std_Internal_Parsec_String_pstring___closed__0 = _init_l_Std_Internal_Parsec_String_pstring___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_String_pstring___closed__0);
l_Std_Internal_Parsec_String_pchar___closed__0 = _init_l_Std_Internal_Parsec_String_pchar___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_String_pchar___closed__0);
l_Std_Internal_Parsec_String_pchar___closed__1 = _init_l_Std_Internal_Parsec_String_pchar___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_pchar___closed__1);
l_Std_Internal_Parsec_String_pchar___closed__2 = _init_l_Std_Internal_Parsec_String_pchar___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_String_pchar___closed__2);
l_Std_Internal_Parsec_String_digit___closed__0 = _init_l_Std_Internal_Parsec_String_digit___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_String_digit___closed__0);
l_Std_Internal_Parsec_String_digit___closed__1 = _init_l_Std_Internal_Parsec_String_digit___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_digit___closed__1);
l_Std_Internal_Parsec_String_hexDigit___closed__0 = _init_l_Std_Internal_Parsec_String_hexDigit___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_String_hexDigit___closed__0);
l_Std_Internal_Parsec_String_hexDigit___closed__1 = _init_l_Std_Internal_Parsec_String_hexDigit___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_hexDigit___closed__1);
l_Std_Internal_Parsec_String_asciiLetter___closed__0 = _init_l_Std_Internal_Parsec_String_asciiLetter___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_String_asciiLetter___closed__0);
l_Std_Internal_Parsec_String_asciiLetter___closed__1 = _init_l_Std_Internal_Parsec_String_asciiLetter___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_asciiLetter___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
