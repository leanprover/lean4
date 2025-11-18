// Lean compiler output
// Module: Init.Data.String.TakeDrop
// Imports: public import Init.Data.String.Substring
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
LEAN_EXPORT uint8_t l_String_endsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00String_Internal_trimImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trim___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_trim(lean_object*);
lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object*, lean_object*);
static lean_object* l_String_trimRight___closed__0;
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropRightWhile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00String_Internal_trimImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimLeft___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_trimImpl_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_startsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimRight___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRight(lean_object*, lean_object*);
lean_object* l_Substring_Raw_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_trim(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_trimImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_Raw_beq(lean_object*, lean_object*);
lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object*, lean_object*);
lean_object* l_Substring_Raw_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_Raw_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRightWhile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_dropright(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimRight(lean_object*);
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object*);
LEAN_EXPORT lean_object* lean_string_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_Raw_nextn(x_5, x_2, x_3);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_string_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_Raw_nextn(x_5, x_2, x_3);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_dropRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_Raw_prevn(x_5, x_2, x_4);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_string_dropright(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_Raw_prevn(x_5, x_2, x_4);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_Raw_nextn(x_5, x_2, x_3);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_takeRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_inc(x_4);
x_6 = l_Substring_Raw_prevn(x_5, x_2, x_4);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_4, x_2, x_3);
lean_dec(x_4);
x_6 = lean_string_utf8_extract(x_1, x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_takeWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_4, x_2, x_3);
x_6 = lean_string_utf8_extract(x_1, x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
x_5 = l_Substring_Raw_takeRightWhileAux(x_1, x_3, x_2, x_4);
x_6 = lean_string_utf8_extract(x_1, x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_takeRightWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_takeRightWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeRightWhileAux(x_1, x_3, x_2, x_4);
x_6 = lean_string_utf8_extract(x_1, x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_dropRightWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropRightWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_startsWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_length(x_2);
x_7 = l_Substring_Raw_nextn(x_5, x_6, x_3);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_Raw_beq(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_startsWith(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_endsWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_length(x_2);
lean_inc(x_4);
x_7 = l_Substring_Raw_prevn(x_5, x_6, x_4);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_Raw_beq(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_endsWith(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_String_trimRight___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_trimRight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_trimRight___closed__0;
x_5 = l_Substring_Raw_takeRightWhileAux(x_1, x_2, x_4, x_3);
x_6 = lean_string_utf8_extract(x_1, x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_trimRight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trimRight(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_trimRight___closed__0;
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_3, x_4, x_2);
x_6 = lean_string_utf8_extract(x_1, x_5, x_3);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_trimLeft___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trimLeft(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_trimRight___closed__0;
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_3, x_4, x_2);
x_6 = l_Substring_Raw_takeRightWhileAux(x_1, x_5, x_4, x_3);
x_7 = lean_string_utf8_extract(x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_trim___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trim(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_trimImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00String_Internal_trimImpl_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_Raw_takeWhileAux___at___00String_Internal_trimImpl_spec__0(x_1, x_3, x_2);
x_5 = l_Substring_Raw_takeRightWhileAux___at___00String_Internal_trimImpl_spec__1(x_1, x_4, x_3);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_trimImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_Raw_takeWhileAux___at___00String_Internal_trimImpl_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00String_Internal_trimImpl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_Raw_takeRightWhileAux___at___00String_Internal_trimImpl_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_nextWhile(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_nextWhile(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc_ref(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(x_2, x_1, x_4, x_3);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = l_Substring_Raw_takeWhileAux(x_1, x_5, x_4, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_Pos_Raw_nextUntil___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_nextUntil(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc_ref(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(x_2, x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_nextUntil(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_Raw_dropPrefix_x3f(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_Raw_dropSuffix_x3f(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_String_dropPrefix_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_String_dropSuffix_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
}
}
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_trimRight___closed__0 = _init_l_String_trimRight___closed__0();
lean_mark_persistent(l_String_trimRight___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
