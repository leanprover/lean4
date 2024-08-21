// Lean compiler output
// Module: Lean.Data.Parsec.String
// Imports: Lean.Data.Parsec.Basic
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipString(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_String_asciiLetter___closed__1;
static lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___closed__7;
static lean_object* l_Lean_Parsec_String_pchar___closed__2;
lean_object* l_String_Iterator_hasNext___boxed(lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___lambda__1___boxed(lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_hexDigit(lean_object*);
extern lean_object* l_Lean_Parsec_unexpectedEndOfInput;
static lean_object* l_Lean_Parsec_String_pstring___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipString___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pchar___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_extract(lean_object*, lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
static lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___closed__4;
lean_object* l_String_Iterator_curr___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipChar(uint32_t, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_instDecidableEqPos___boxed(lean_object*, lean_object*);
uint8_t l_String_Iterator_hasNext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_String_digit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parsec_String_take(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_String_pchar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitsCore_go(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_String_hexDigit___closed__1;
static lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parsec_String_Parser_run(lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_Parsec_String_Parser_run___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pstring___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___closed__3;
lean_object* l_String_Iterator_forward(lean_object*, lean_object*);
static lean_object* l_Lean_Parsec_String_Parser_run___rarg___closed__1;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___closed__6;
static lean_object* l_Lean_Parsec_String_Parser_run___rarg___closed__3;
static lean_object* l_Lean_Parsec_String_take___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_skipWs(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipChar___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_ws(lean_object*);
static lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitToNat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___lambda__1(lean_object*);
static lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parsec_String_digits(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_instInputIteratorCharPos;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pchar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_digit(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_asciiLetter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqPos___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_String_instInputIteratorCharPos___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_Iterator_next), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_Iterator_curr___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_Iterator_hasNext___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parsec_String_instInputIteratorCharPos___closed__3;
x_2 = l_Lean_Parsec_String_instInputIteratorCharPos___closed__4;
x_3 = l_Lean_Parsec_String_instInputIteratorCharPos___closed__5;
x_4 = l_Lean_Parsec_String_instInputIteratorCharPos___closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parsec_String_instInputIteratorCharPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parsec_String_instInputIteratorCharPos___closed__7;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_instInputIteratorCharPos___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parsec_String_instInputIteratorCharPos___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parsec_String_Parser_run___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("offset ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_Parser_run___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_Parser_run___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_Parser_run___rarg(lean_object* x_1, lean_object* x_2) {
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
x_15 = l_Lean_Parsec_String_Parser_run___rarg___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Parsec_String_Parser_run___rarg___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_9);
lean_dec(x_9);
x_20 = l_Lean_Parsec_String_Parser_run___rarg___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_Parser_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_String_Parser_run___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parsec_String_pstring___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pstring(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Parsec_String_pstring___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lean_Parsec_String_Parser_run___rarg___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pstring___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parsec_String_pstring(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parsec_String_pstring(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parsec_String_skipString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parsec_String_pchar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: '", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parsec_String_pchar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pchar(uint32_t x_1, lean_object* x_2) {
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
x_8 = lean_uint32_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_9 = l_Lean_Parsec_String_Parser_run___rarg___closed__3;
x_10 = lean_string_push(x_9, x_1);
x_11 = l_Lean_Parsec_String_pchar___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Parsec_String_pchar___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parsec_String_pchar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parsec_String_pchar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipChar(uint32_t x_1, lean_object* x_2) {
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
x_8 = lean_uint32_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_9 = l_Lean_Parsec_String_Parser_run___rarg___closed__3;
x_10 = lean_string_push(x_9, x_1);
x_11 = l_Lean_Parsec_String_pchar___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Parsec_String_pchar___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parsec_String_skipChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parsec_String_skipChar(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parsec_String_digit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("digit expected", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_digit(lean_object* x_1) {
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
x_8 = lean_uint32_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = l_Lean_Parsec_String_digit___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 57;
x_12 = lean_uint32_dec_le(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_Lean_Parsec_String_digit___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitToNat(uint32_t x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitToNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitToNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitsCore_go(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Iterator_hasNext(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = 48;
x_7 = lean_uint32_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 57;
x_10 = lean_uint32_dec_le(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_uint32_to_nat(x_5);
x_13 = lean_unsigned_to_nat(48u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(10u);
x_16 = lean_nat_mul(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_16, x_14);
lean_dec(x_14);
lean_dec(x_16);
x_18 = l_String_Iterator_next(x_1);
x_1 = x_18;
x_2 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitsCore_go(x_2, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Parsec_String_digits(lean_object* x_1) {
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
x_8 = lean_uint32_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = l_Lean_Parsec_String_digit___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 57;
x_12 = lean_uint32_dec_le(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_Lean_Parsec_String_digit___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_15 = lean_uint32_to_nat(x_6);
x_16 = lean_unsigned_to_nat(48u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_digitsCore(x_17, x_5);
return x_18;
}
}
}
}
}
static lean_object* _init_l_Lean_Parsec_String_hexDigit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hex digit expected", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_hexDigit(lean_object* x_1) {
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
lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_35; uint8_t x_36; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
x_35 = 48;
x_36 = lean_uint32_dec_le(x_35, x_6);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_7 = x_37;
goto block_34;
}
else
{
uint32_t x_38; uint8_t x_39; 
x_38 = 57;
x_39 = lean_uint32_dec_le(x_6, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_7 = x_40;
goto block_34;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_41 = lean_box_uint32(x_6);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
block_34:
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = 97;
x_9 = lean_uint32_dec_le(x_8, x_6);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 65;
x_11 = lean_uint32_dec_le(x_10, x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l_Lean_Parsec_String_hexDigit___closed__1;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 70;
x_15 = lean_uint32_dec_le(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = l_Lean_Parsec_String_hexDigit___closed__1;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_box_uint32(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 102;
x_21 = lean_uint32_dec_le(x_6, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 65;
x_23 = lean_uint32_dec_le(x_22, x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_24 = l_Lean_Parsec_String_hexDigit___closed__1;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 70;
x_27 = lean_uint32_dec_le(x_6, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
x_28 = l_Lean_Parsec_String_hexDigit___closed__1;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_box_uint32(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_box_uint32(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Parsec_String_asciiLetter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ASCII letter expected", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_asciiLetter(lean_object* x_1) {
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
x_8 = lean_uint32_dec_le(x_7, x_6);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 97;
x_10 = lean_uint32_dec_le(x_9, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Lean_Parsec_String_asciiLetter___closed__1;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 122;
x_14 = lean_uint32_dec_le(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l_Lean_Parsec_String_asciiLetter___closed__1;
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
x_20 = lean_uint32_dec_le(x_6, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 97;
x_22 = lean_uint32_dec_le(x_21, x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = l_Lean_Parsec_String_asciiLetter___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 122;
x_26 = lean_uint32_dec_le(x_6, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_27 = l_Lean_Parsec_String_asciiLetter___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_skipWs(lean_object* x_1) {
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
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 10;
x_7 = lean_uint32_dec_eq(x_3, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 13;
x_9 = lean_uint32_dec_eq(x_3, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 32;
x_11 = lean_uint32_dec_eq(x_3, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Parsec_String_ws(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Data_Parsec_String_0__Lean_Parsec_String_skipWs(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parsec_String_take___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" codepoints", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parsec_String_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = l_String_Iterator_forward(x_2, x_1);
x_4 = l_String_Iterator_extract(x_2, x_3);
x_5 = lean_string_length(x_4);
x_6 = lean_nat_dec_eq(x_5, x_1);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_8 = l_Lean_Parsec_String_pstring___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Parsec_String_take___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
lean_object* initialize_Lean_Data_Parsec_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Parsec_String(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Parsec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parsec_String_instInputIteratorCharPos___closed__1 = _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos___closed__1);
l_Lean_Parsec_String_instInputIteratorCharPos___closed__2 = _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__2();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos___closed__2);
l_Lean_Parsec_String_instInputIteratorCharPos___closed__3 = _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__3();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos___closed__3);
l_Lean_Parsec_String_instInputIteratorCharPos___closed__4 = _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__4();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos___closed__4);
l_Lean_Parsec_String_instInputIteratorCharPos___closed__5 = _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__5();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos___closed__5);
l_Lean_Parsec_String_instInputIteratorCharPos___closed__6 = _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__6();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos___closed__6);
l_Lean_Parsec_String_instInputIteratorCharPos___closed__7 = _init_l_Lean_Parsec_String_instInputIteratorCharPos___closed__7();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos___closed__7);
l_Lean_Parsec_String_instInputIteratorCharPos = _init_l_Lean_Parsec_String_instInputIteratorCharPos();
lean_mark_persistent(l_Lean_Parsec_String_instInputIteratorCharPos);
l_Lean_Parsec_String_Parser_run___rarg___closed__1 = _init_l_Lean_Parsec_String_Parser_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_Parser_run___rarg___closed__1);
l_Lean_Parsec_String_Parser_run___rarg___closed__2 = _init_l_Lean_Parsec_String_Parser_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Parsec_String_Parser_run___rarg___closed__2);
l_Lean_Parsec_String_Parser_run___rarg___closed__3 = _init_l_Lean_Parsec_String_Parser_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Parsec_String_Parser_run___rarg___closed__3);
l_Lean_Parsec_String_pstring___closed__1 = _init_l_Lean_Parsec_String_pstring___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_pstring___closed__1);
l_Lean_Parsec_String_pchar___closed__1 = _init_l_Lean_Parsec_String_pchar___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_pchar___closed__1);
l_Lean_Parsec_String_pchar___closed__2 = _init_l_Lean_Parsec_String_pchar___closed__2();
lean_mark_persistent(l_Lean_Parsec_String_pchar___closed__2);
l_Lean_Parsec_String_digit___closed__1 = _init_l_Lean_Parsec_String_digit___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_digit___closed__1);
l_Lean_Parsec_String_hexDigit___closed__1 = _init_l_Lean_Parsec_String_hexDigit___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_hexDigit___closed__1);
l_Lean_Parsec_String_asciiLetter___closed__1 = _init_l_Lean_Parsec_String_asciiLetter___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_asciiLetter___closed__1);
l_Lean_Parsec_String_take___closed__1 = _init_l_Lean_Parsec_String_take___closed__1();
lean_mark_persistent(l_Lean_Parsec_String_take___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
