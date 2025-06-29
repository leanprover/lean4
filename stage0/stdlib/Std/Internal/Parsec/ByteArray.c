// Lean compiler output
// Module: Std.Internal.Parsec.ByteArray
// Imports: Std.Internal.Parsec.Basic Init.Data.ByteArray.Basic Init.Data.String.Extra
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
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3;
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* l_ByteArray_mkIterator(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___Std_Internal_Parsec_ByteArray_skipBytes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___Std_Internal_Parsec_ByteArray_skipBytes_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed(lean_object*, lean_object*);
static uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed(lean_object*);
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte___boxed(lean_object*, lean_object*);
static uint8_t l_Std_Internal_Parsec_ByteArray_digit___closed__1;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object*);
static lean_object* l_Std_Internal_Parsec_ByteArray_take___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0;
size_t lean_sarray_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte(uint8_t, lean_object*);
uint8_t lean_byte_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object*);
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1;
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed(lean_object*);
static uint8_t l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___boxed(lean_object*, lean_object*);
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pstring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t);
static uint8_t l_Std_Internal_Parsec_ByteArray_digit___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run(lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar(uint32_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object*);
static lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object*);
static lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
static uint8_t l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2;
size_t lean_usize_add(size_t, size_t);
static uint8_t l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar(uint32_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object*);
static lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1;
static lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte(uint8_t, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_of_nat(lean_object*);
static lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0;
static lean_object* l_Std_Internal_Parsec_ByteArray_take___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(lean_object*, lean_object*);
static uint8_t l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3;
static lean_object* l_Std_Internal_Parsec_ByteArray_digit___closed__0;
static lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint8_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_byte_array_fget(x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_byte_array_fget(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__1), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__4), 2, 0);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed), 2, 0);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__3(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__5(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("offset ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_ByteArray_mkIterator(x_2);
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0;
x_11 = l_Nat_reprFast(x_9);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_unsigned_to_nat(120u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_format_pretty(x_12, x_13, x_14, x_14);
x_16 = lean_string_append(x_10, x_15);
lean_dec(x_15);
x_17 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_8);
lean_dec(x_8);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_pbyte___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_pbyte___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: '", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_pbyte___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_10 = lean_uint8_dec_eq(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
x_12 = lean_uint8_to_nat(x_1);
x_13 = l_Nat_reprFast(x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_22);
x_23 = lean_box(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pbyte___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_ByteArray_pbyte(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_10 = lean_uint8_dec_eq(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
x_12 = lean_uint8_to_nat(x_1);
x_13 = l_Nat_reprFast(x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByte___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_ByteArray_skipByte(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___Std_Internal_Parsec_ByteArray_skipBytes_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_byte_array_size(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_13 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_15 = lean_byte_array_uget(x_2, x_4);
x_16 = lean_byte_array_fget(x_9, x_10);
x_17 = lean_uint8_dec_eq(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_18 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
x_19 = lean_uint8_to_nat(x_15);
x_20 = l_Nat_reprFast(x_19);
x_21 = lean_string_append(x_18, x_20);
lean_dec(x_20);
x_22 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_26 = lean_ctor_get(x_6, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_6, 0);
lean_dec(x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_10, x_28);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_29);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
lean_inc(x_1);
{
size_t _tmp_3 = x_31;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_6);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_10, x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
lean_inc(x_1);
{
size_t _tmp_3 = x_37;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_5 = x_35;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_sarray_size(x_1);
x_5 = 0;
x_6 = l_ByteArray_forInUnsafe_loop___at___Std_Internal_Parsec_ByteArray_skipBytes_spec__0(x_3, x_1, x_4, x_5, x_3, x_2);
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
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_forInUnsafe_loop___at___Std_Internal_Parsec_ByteArray_skipBytes_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_ByteArray_forInUnsafe_loop___at___Std_Internal_Parsec_ByteArray_skipBytes_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pstring(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_to_utf8(x_1);
x_4 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_3, x_2);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_dec(x_6);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_to_utf8(x_1);
x_4 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_3, x_2);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 1, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_ByteArray_skipString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_10 = lean_uint32_to_uint8(x_1);
x_11 = lean_uint8_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
x_13 = l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0;
x_14 = lean_string_push(x_13, x_1);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_23);
x_24 = lean_box_uint32(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box_uint32(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_pByteChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_ByteArray_pByteChar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_uint32_to_uint8(x_1);
x_10 = lean_byte_array_fget(x_3, x_4);
x_11 = lean_uint8_dec_eq(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__1;
x_13 = lean_uint8_to_nat(x_9);
x_14 = l_Nat_reprFast(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_23);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_skipByteChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_ByteArray_skipByteChar(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_digit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("digit expected", 14, 14);
return x_1;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 48;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 57;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = l_Std_Internal_Parsec_ByteArray_digit___closed__1;
x_13 = lean_uint8_dec_le(x_12, x_11);
if (x_13 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = l_Std_Internal_Parsec_ByteArray_digit___closed__2;
x_15 = lean_uint8_dec_le(x_11, x_14);
if (x_15 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_20);
x_21 = lean_uint8_to_uint32(x_11);
x_22 = lean_box_uint32(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_uint8_to_uint32(x_11);
x_28 = lean_box_uint32(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_ByteArray_digit___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Std_Internal_Parsec_ByteArray_digit___closed__1;
x_3 = lean_uint8_sub(x_1, x_2);
x_4 = lean_uint8_to_nat(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitToNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
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
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_byte_array_fget(x_3, x_4);
x_9 = l_Std_Internal_Parsec_ByteArray_digit___closed__1;
x_10 = lean_uint8_dec_le(x_9, x_8);
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
uint8_t x_12; uint8_t x_13; 
x_12 = l_Std_Internal_Parsec_ByteArray_digit___closed__2;
x_13 = lean_uint8_dec_le(x_8, x_12);
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_uint8_sub(x_8, x_9);
x_19 = lean_uint8_to_nat(x_18);
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_mul(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_21, x_19);
lean_dec(x_19);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_24);
x_2 = x_22;
goto _start;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_26 = lean_uint8_sub(x_8, x_9);
x_27 = lean_uint8_to_nat(x_26);
x_28 = lean_unsigned_to_nat(10u);
x_29 = lean_nat_mul(x_2, x_28);
lean_dec(x_2);
x_30 = lean_nat_add(x_29, x_27);
lean_dec(x_27);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
lean_dec(x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_32);
x_1 = x_33;
x_2 = x_30;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_2, x_1);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = l_Std_Internal_Parsec_ByteArray_digit___closed__1;
x_13 = lean_uint8_dec_le(x_12, x_11);
if (x_13 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = l_Std_Internal_Parsec_ByteArray_digit___closed__2;
x_15 = lean_uint8_dec_le(x_11, x_14);
if (x_15 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_20);
x_21 = lean_uint8_to_uint32(x_11);
x_22 = lean_uint32_to_uint8(x_21);
x_23 = lean_uint8_sub(x_22, x_12);
x_24 = lean_uint8_to_nat(x_23);
x_25 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_1, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_ctor_set(x_25, 1, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_6, x_32);
lean_dec(x_6);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_uint8_to_uint32(x_11);
x_36 = lean_uint32_to_uint8(x_35);
x_37 = lean_uint8_sub(x_36, x_12);
x_38 = lean_uint8_to_nat(x_37);
x_39 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_34, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_ByteArray_digit___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hex digit expected", 18, 18);
return x_1;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 65;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 70;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 97;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 102;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_hexDigit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_29; uint8_t x_30; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
x_29 = l_Std_Internal_Parsec_ByteArray_digit___closed__1;
x_30 = lean_uint8_dec_le(x_29, x_11);
if (x_30 == 0)
{
goto block_28;
}
else
{
uint8_t x_31; uint8_t x_32; 
x_31 = l_Std_Internal_Parsec_ByteArray_digit___closed__2;
x_32 = lean_uint8_dec_le(x_11, x_31);
if (x_32 == 0)
{
goto block_28;
}
else
{
lean_dec(x_1);
goto block_18;
}
}
block_18:
{
uint32_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_uint8_to_uint32(x_11);
x_16 = lean_box_uint32(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
block_23:
{
uint8_t x_19; uint8_t x_20; 
x_19 = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1;
x_20 = lean_uint8_dec_le(x_19, x_11);
if (x_20 == 0)
{
lean_dec(x_14);
goto block_4;
}
else
{
uint8_t x_21; uint8_t x_22; 
x_21 = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2;
x_22 = lean_uint8_dec_le(x_11, x_21);
if (x_22 == 0)
{
lean_dec(x_14);
goto block_4;
}
else
{
lean_dec(x_1);
goto block_18;
}
}
}
block_28:
{
uint8_t x_24; uint8_t x_25; 
x_24 = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3;
x_25 = lean_uint8_dec_le(x_24, x_11);
if (x_25 == 0)
{
goto block_23;
}
else
{
uint8_t x_26; uint8_t x_27; 
x_26 = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4;
x_27 = lean_uint8_dec_le(x_11, x_26);
if (x_27 == 0)
{
goto block_23;
}
else
{
lean_dec(x_1);
goto block_18;
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ASCII letter expected", 21, 21);
return x_1;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 122;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 90;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_asciiLetter(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = l_Std_Internal_Parsec_ByteArray_pbyte___closed__0;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_24; uint8_t x_25; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
x_24 = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1;
x_25 = lean_uint8_dec_le(x_24, x_11);
if (x_25 == 0)
{
goto block_23;
}
else
{
uint8_t x_26; uint8_t x_27; 
x_26 = l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2;
x_27 = lean_uint8_dec_le(x_11, x_26);
if (x_27 == 0)
{
goto block_23;
}
else
{
lean_dec(x_1);
goto block_18;
}
}
block_18:
{
uint32_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_uint8_to_uint32(x_11);
x_16 = lean_box_uint32(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
block_23:
{
uint8_t x_19; uint8_t x_20; 
x_19 = l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3;
x_20 = lean_uint8_dec_le(x_19, x_11);
if (x_20 == 0)
{
lean_dec(x_14);
goto block_4;
}
else
{
uint8_t x_21; uint8_t x_22; 
x_21 = l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1;
x_22 = lean_uint8_dec_le(x_11, x_21);
if (x_22 == 0)
{
lean_dec(x_14);
goto block_4;
}
else
{
lean_dec(x_1);
goto block_18;
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 9;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 10;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 13;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 32;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_9 = lean_byte_array_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0;
x_13 = lean_uint8_dec_eq(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1;
x_15 = lean_uint8_dec_eq(x_11, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2;
x_17 = lean_uint8_dec_eq(x_11, x_16);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; 
x_18 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3;
x_19 = lean_uint8_dec_eq(x_11, x_18);
if (x_19 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_dec(x_1);
goto block_8;
}
}
else
{
lean_dec(x_1);
goto block_8;
}
}
else
{
lean_dec(x_1);
goto block_8;
}
}
else
{
lean_dec(x_1);
goto block_8;
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_1 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_ws(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_take___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Parsec_ByteArray_take___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" bytes", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_nat_add(x_4, x_1);
x_6 = l_ByteArray_extract(x_3, x_4, x_5);
x_7 = lean_byte_array_size(x_6);
x_8 = lean_nat_dec_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_9 = l_Std_Internal_Parsec_ByteArray_take___closed__0;
x_10 = l_Nat_reprFast(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_Std_Internal_Parsec_ByteArray_take___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
}
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat___lam__2___closed__0();
l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat = _init_l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_instInputIteratorUInt8Nat);
l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__0);
l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1 = _init_l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_Parser_run___redArg___closed__1);
l_Std_Internal_Parsec_ByteArray_pbyte___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_pbyte___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_pbyte___closed__0);
l_Std_Internal_Parsec_ByteArray_pbyte___closed__1 = _init_l_Std_Internal_Parsec_ByteArray_pbyte___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_pbyte___closed__1);
l_Std_Internal_Parsec_ByteArray_pbyte___closed__2 = _init_l_Std_Internal_Parsec_ByteArray_pbyte___closed__2();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_pbyte___closed__2);
l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_pByteChar___closed__0);
l_Std_Internal_Parsec_ByteArray_digit___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_digit___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_digit___closed__0);
l_Std_Internal_Parsec_ByteArray_digit___closed__1 = _init_l_Std_Internal_Parsec_ByteArray_digit___closed__1();
l_Std_Internal_Parsec_ByteArray_digit___closed__2 = _init_l_Std_Internal_Parsec_ByteArray_digit___closed__2();
l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_hexDigit___closed__0);
l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1 = _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__1();
l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2 = _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__2();
l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3 = _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__3();
l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4 = _init_l_Std_Internal_Parsec_ByteArray_hexDigit___closed__4();
l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__0);
l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1 = _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__1();
l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2 = _init_l_Std_Internal_Parsec_ByteArray_asciiLetter___closed__2();
l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0 = _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__0();
l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1 = _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__1();
l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2 = _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__2();
l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3 = _init_l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_skipWs___closed__3();
l_Std_Internal_Parsec_ByteArray_take___closed__0 = _init_l_Std_Internal_Parsec_ByteArray_take___closed__0();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_take___closed__0);
l_Std_Internal_Parsec_ByteArray_take___closed__1 = _init_l_Std_Internal_Parsec_ByteArray_take___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_ByteArray_take___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
