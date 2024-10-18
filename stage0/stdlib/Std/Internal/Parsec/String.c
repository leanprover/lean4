// Lean compiler output
// Module: Std.Internal.Parsec.String
// Imports: Std.Internal.Parsec.Basic
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_take___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__1(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__9;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Std_Internal_Parsec_String_digit___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__8;
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__4;
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__6(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__5;
static lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__4(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Std_Internal_Parsec_String_hexDigit___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_take___closed__2;
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object*);
lean_object* l_instDecidableEqPos___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__6;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t, lean_object*);
extern lean_object* l_Std_Internal_Parsec_unexpectedEndOfInput;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__1___boxed(lean_object*);
static lean_object* l_Std_Internal_Parsec_String_asciiLetter___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__3___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object*);
lean_object* l_String_Iterator_forward(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object*);
static lean_object* l_Std_Internal_Parsec_String_pchar___closed__1;
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__7;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_pchar___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_String_pstring___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__4___boxed(lean_object*);
static lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_next(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_get(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_get_fast(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqPos___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__4___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__5), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__6___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__3;
x_2 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__4;
x_3 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__5;
x_4 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__6;
x_5 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__7;
x_6 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__8;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__3___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__3(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__4___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__4(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lambda__6(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_Parser_run___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("offset ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_Parser_run___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Std_Format_defWidth;
x_14 = lean_format_pretty(x_12, x_13, x_3, x_3);
x_15 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_9);
lean_dec(x_9);
x_20 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_Parser_run___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_pstring___closed__1() {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_3 = lean_string_length(x_1);
lean_inc(x_2);
x_4 = l_String_Iterator_forward(x_2, x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_string_dec_eq(x_5, x_7);
lean_dec(x_7);
x_10 = l_instDecidableNot___rarg(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_8, x_6);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_string_utf8_extract(x_5, x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_string_dec_eq(x_12, x_1);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_18 = lean_string_append(x_17, x_1);
x_19 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_20 = lean_string_append(x_18, x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_20);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_21 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_22 = lean_string_append(x_21, x_1);
x_23 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_4);
return x_2;
}
else
{
lean_object* x_29; 
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_30 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_31 = lean_string_dec_eq(x_30, x_1);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_36 = lean_string_append(x_35, x_1);
x_37 = lean_string_append(x_36, x_30);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_38 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_39 = lean_string_append(x_38, x_1);
x_40 = lean_string_append(x_39, x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_2, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_4);
return x_2;
}
else
{
lean_object* x_45; 
lean_dec(x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_30);
return x_45;
}
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_46 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_47 = lean_string_dec_eq(x_46, x_1);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_4);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_4, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_4, 0);
lean_dec(x_50);
x_51 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_52 = lean_string_append(x_51, x_1);
x_53 = lean_string_append(x_52, x_46);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_53);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_4);
x_54 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_55 = lean_string_append(x_54, x_1);
x_56 = lean_string_append(x_55, x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_2, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_2, 0);
lean_dec(x_60);
lean_ctor_set(x_2, 1, x_46);
lean_ctor_set(x_2, 0, x_4);
return x_2;
}
else
{
lean_object* x_61; 
lean_dec(x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_46);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_String_pstring(x_1, x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_String_skipString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_pchar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: '", 11, 11);
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_uint32_dec_eq(x_9, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_13 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_14 = lean_string_push(x_13, x_1);
x_15 = l_Std_Internal_Parsec_String_pchar___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Std_Internal_Parsec_String_pchar___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
x_23 = lean_box_uint32(x_1);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_box_uint32(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_uint32_dec_eq(x_9, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_13 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_14 = lean_string_push(x_13, x_1);
x_15 = l_Std_Internal_Parsec_String_pchar___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Std_Internal_Parsec_String_pchar___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
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
static lean_object* _init_l_Std_Internal_Parsec_String_digit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("digit expected", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Std_Internal_Parsec_String_digit___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 57;
x_16 = lean_uint32_dec_le(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_17 = l_Std_Internal_Parsec_String_digit___closed__1;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_dec(x_21);
x_22 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_box_uint32(x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = 48;
x_9 = lean_string_utf8_get(x_3, x_4);
x_10 = lean_uint32_dec_le(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = lean_uint32_dec_le(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_uint32_to_nat(x_9);
x_19 = lean_unsigned_to_nat(48u);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(10u);
x_22 = lean_nat_mul(x_2, x_21);
lean_dec(x_2);
x_23 = lean_nat_add(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
x_24 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_24);
x_2 = x_23;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_26 = lean_uint32_to_nat(x_9);
x_27 = lean_unsigned_to_nat(48u);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(10u);
x_30 = lean_nat_mul(x_2, x_29);
lean_dec(x_2);
x_31 = lean_nat_add(x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
x_32 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_32);
x_1 = x_33;
x_2 = x_31;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_ctor_set(x_3, 1, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Std_Internal_Parsec_String_digit___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 57;
x_16 = lean_uint32_dec_le(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_17 = l_Std_Internal_Parsec_String_digit___closed__1;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_19 = lean_uint32_to_nat(x_8);
x_20 = lean_unsigned_to_nat(48u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(x_21, x_10);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_hexDigit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hex digit expected", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_51; uint8_t x_52; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_51 = 48;
x_52 = lean_uint32_dec_le(x_51, x_8);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_11 = x_53;
goto block_50;
}
else
{
uint32_t x_54; uint8_t x_55; 
x_54 = 57;
x_55 = lean_uint32_dec_le(x_8, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_11 = x_56;
goto block_50;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_1, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_1, 0);
lean_dec(x_59);
x_60 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_1);
x_61 = lean_box_uint32(x_8);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
block_50:
{
uint32_t x_12; uint8_t x_13; 
lean_dec(x_11);
x_12 = 97;
x_13 = lean_uint32_dec_le(x_12, x_8);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 65;
x_15 = lean_uint32_dec_le(x_14, x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = l_Std_Internal_Parsec_String_hexDigit___closed__1;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 70;
x_19 = lean_uint32_dec_le(x_8, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_20 = l_Std_Internal_Parsec_String_hexDigit___closed__1;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_box_uint32(x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint32_t x_28; uint8_t x_29; 
x_28 = 102;
x_29 = lean_uint32_dec_le(x_8, x_28);
if (x_29 == 0)
{
uint32_t x_30; uint8_t x_31; 
x_30 = 65;
x_31 = lean_uint32_dec_le(x_30, x_8);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_10);
x_32 = l_Std_Internal_Parsec_String_hexDigit___closed__1;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
uint32_t x_34; uint8_t x_35; 
x_34 = 70;
x_35 = lean_uint32_dec_le(x_8, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
x_36 = l_Std_Internal_Parsec_String_hexDigit___closed__1;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_1, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 0);
lean_dec(x_40);
x_41 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_41);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_42 = lean_box_uint32(x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_dec(x_46);
x_47 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_47);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = lean_box_uint32(x_8);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_10);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_asciiLetter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ASCII letter expected", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = 65;
x_12 = lean_uint32_dec_le(x_11, x_8);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 97;
x_14 = lean_uint32_dec_le(x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_15 = l_Std_Internal_Parsec_String_asciiLetter___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 122;
x_18 = lean_uint32_dec_le(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_19 = l_Std_Internal_Parsec_String_asciiLetter___closed__1;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_box_uint32(x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 90;
x_28 = lean_uint32_dec_le(x_8, x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; 
x_29 = 97;
x_30 = lean_uint32_dec_le(x_29, x_8);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
x_31 = l_Std_Internal_Parsec_String_asciiLetter___closed__1;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
uint32_t x_33; uint8_t x_34; 
x_33 = 122;
x_34 = lean_uint32_dec_le(x_8, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
x_35 = l_Std_Internal_Parsec_String_asciiLetter___closed__1;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_1, 0);
lean_dec(x_39);
x_40 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_41 = lean_box_uint32(x_8);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_1, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_1, 0);
lean_dec(x_45);
x_46 = lean_box_uint32(x_8);
lean_ctor_set(x_1, 1, x_46);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = lean_box_uint32(x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = 9;
x_7 = lean_string_utf8_get_fast(x_2, x_3);
x_8 = lean_uint32_dec_eq(x_7, x_6);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 10;
x_10 = lean_uint32_dec_eq(x_7, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_7, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 32;
x_14 = lean_uint32_dec_eq(x_7, x_13);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_18);
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
x_1 = x_21;
goto _start;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_26);
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
x_1 = x_29;
goto _start;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_1, 0);
lean_dec(x_33);
x_34 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_34);
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_1 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_1, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_dec(x_41);
x_42 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_42);
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_44 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_44);
x_1 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_take___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" codepoints", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_take___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = l_String_Iterator_forward(x_2, x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_string_dec_eq(x_4, x_6);
lean_dec(x_6);
x_9 = l_instDecidableNot___rarg(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_7, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_string_utf8_extract(x_4, x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_string_length(x_11);
x_13 = lean_nat_dec_eq(x_12, x_1);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_18 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Std_Internal_Parsec_String_take___closed__1;
x_21 = lean_string_append(x_19, x_20);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
x_22 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_23 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Std_Internal_Parsec_String_take___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_2, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 0);
lean_dec(x_30);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_11);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_32 = l_Std_Internal_Parsec_String_take___closed__2;
x_33 = lean_nat_dec_eq(x_32, x_1);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_3, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_dec(x_36);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_38 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Std_Internal_Parsec_String_take___closed__1;
x_41 = lean_string_append(x_39, x_40);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_43 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_Std_Internal_Parsec_String_take___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_2, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_2, 0);
lean_dec(x_50);
x_51 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
lean_ctor_set(x_2, 1, x_51);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
x_52 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_54 = l_Std_Internal_Parsec_String_take___closed__2;
x_55 = lean_nat_dec_eq(x_54, x_1);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_3, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_3, 0);
lean_dec(x_58);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_60 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Std_Internal_Parsec_String_take___closed__1;
x_63 = lean_string_append(x_61, x_62);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_63);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
x_64 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_65 = l_Std_Internal_Parsec_String_pstring___closed__1;
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = l_Std_Internal_Parsec_String_take___closed__1;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_2);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_2, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_2, 0);
lean_dec(x_72);
x_73 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
lean_ctor_set(x_2, 1, x_73);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
x_74 = l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_String(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__1 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__1);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__2 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__2);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__3 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__3();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__3);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__4 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__4();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__4);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__5 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__5();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__5);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__6 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__6();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__6);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__7 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__7();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__7);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__8 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__8();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__8);
l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__9 = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__9();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos___closed__9);
l_Std_Internal_Parsec_String_instInputIteratorCharPos = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos);
l_Std_Internal_Parsec_String_Parser_run___rarg___closed__1 = _init_l_Std_Internal_Parsec_String_Parser_run___rarg___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_Parser_run___rarg___closed__1);
l_Std_Internal_Parsec_String_Parser_run___rarg___closed__2 = _init_l_Std_Internal_Parsec_String_Parser_run___rarg___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_String_Parser_run___rarg___closed__2);
l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3 = _init_l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3();
lean_mark_persistent(l_Std_Internal_Parsec_String_Parser_run___rarg___closed__3);
l_Std_Internal_Parsec_String_pstring___closed__1 = _init_l_Std_Internal_Parsec_String_pstring___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_pstring___closed__1);
l_Std_Internal_Parsec_String_pchar___closed__1 = _init_l_Std_Internal_Parsec_String_pchar___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_pchar___closed__1);
l_Std_Internal_Parsec_String_pchar___closed__2 = _init_l_Std_Internal_Parsec_String_pchar___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_String_pchar___closed__2);
l_Std_Internal_Parsec_String_digit___closed__1 = _init_l_Std_Internal_Parsec_String_digit___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_digit___closed__1);
l_Std_Internal_Parsec_String_hexDigit___closed__1 = _init_l_Std_Internal_Parsec_String_hexDigit___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_hexDigit___closed__1);
l_Std_Internal_Parsec_String_asciiLetter___closed__1 = _init_l_Std_Internal_Parsec_String_asciiLetter___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_asciiLetter___closed__1);
l_Std_Internal_Parsec_String_take___closed__1 = _init_l_Std_Internal_Parsec_String_take___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_String_take___closed__1);
l_Std_Internal_Parsec_String_take___closed__2 = _init_l_Std_Internal_Parsec_String_take___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_String_take___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
