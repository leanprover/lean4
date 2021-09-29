// Lean compiler output
// Module: Init.Data.ByteArray.Basic
// Imports: Init.Data.Array.Basic Init.Data.Array.Subarray Init.Data.UInt Init.Data.Option.Basic
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
LEAN_EXPORT lean_object* l_ByteArray_push___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_ByteArray_instAppendByteArray___closed__1;
LEAN_EXPORT lean_object* l_ByteArray_instAppendByteArray;
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object*, lean_object*, lean_object*);
uint64_t l_UInt8_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instToStringByteArray(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object*, lean_object*, lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__3;
lean_object* lean_byte_array_data(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__5;
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_ByteArray_toUInt64LE_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_data___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toByteArray_loop(lean_object*, lean_object*);
static lean_object* l_List_toString___at_instToStringByteArray___spec__1___closed__1;
static lean_object* l_ByteArray_toUInt64LE_x21___closed__6;
extern uint64_t l_instInhabitedUInt64;
static lean_object* l_List_toString___at_instToStringByteArray___spec__1___closed__2;
LEAN_EXPORT lean_object* l_ByteArray_empty;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_ByteArray_empty___closed__1;
LEAN_EXPORT lean_object* l_List_toString___at_instToStringByteArray___spec__1(lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2___closed__2;
lean_object* lean_byte_array_set(lean_object*, lean_object*, uint8_t);
static lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2___closed__1;
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
static lean_object* l_List_toString___at_instToStringByteArray___spec__1___closed__3;
static lean_object* l_ByteArray_toUInt64LE_x21___closed__1;
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_instInhabitedByteArray;
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21(lean_object*);
static lean_object* l_ByteArray_toUInt64LE_x21___closed__2;
uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
uint64_t l_UInt64_lor(uint64_t, uint64_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_append(lean_object*, lean_object*);
static lean_object* l_ByteArray_toUInt64BE_x21___closed__2;
LEAN_EXPORT lean_object* l_List_toByteArray(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object*);
static lean_object* l_ByteArray_toUInt64BE_x21___closed__1;
LEAN_EXPORT lean_object* l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1;
static lean_object* l_ByteArray_toUInt64LE_x21___closed__4;
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_mkEmpty___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_ByteArray_size___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_data___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_data(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_mkEmpty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_mk_empty_byte_array(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_ByteArray_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_byte_array(x_1);
return x_2;
}
}
static lean_object* _init_l_ByteArray_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_ByteArray_instInhabitedByteArray() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = lean_byte_array_push(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_size(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_byte_array_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_set_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = lean_byte_array_set(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ByteArray_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_copySlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_byte_array_copy_slice(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_nat_sub(x_3, x_2);
x_5 = l_ByteArray_empty;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 1;
x_8 = lean_byte_array_copy_slice(x_1, x_2, x_5, x_6, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ByteArray_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_byte_array_copy_slice(x_2, x_5, x_1, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_append(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_instAppendByteArray___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ByteArray_append___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_ByteArray_instAppendByteArray() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_instAppendByteArray___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_List_reverse___rarg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = lean_byte_array_get(x_1, x_2);
lean_dec(x_2);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_toList_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_ByteArray_toList_loop(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_toList(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_byte_array_get(x_1, x_3);
x_8 = lean_box(x_7);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f_loop(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_toByteArray_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_byte_array_push(x_2, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_empty;
x_3 = l_List_toByteArray_loop(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_toStringAux___at_instToStringByteArray___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_List_toStringAux___at_instToStringByteArray___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_List_toStringAux___at_instToStringByteArray___spec__2___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = lean_uint8_to_nat(x_6);
x_8 = l_Nat_repr(x_7);
x_9 = l_List_toStringAux___at_instToStringByteArray___spec__2___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = 0;
x_12 = l_List_toStringAux___at_instToStringByteArray___spec__2(x_11, x_5);
x_13 = lean_string_append(x_10, x_12);
lean_dec(x_12);
return x_13;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; 
x_14 = l_List_toStringAux___at_instToStringByteArray___spec__2___closed__1;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_unbox(x_15);
lean_dec(x_15);
x_18 = lean_uint8_to_nat(x_17);
x_19 = l_Nat_repr(x_18);
x_20 = 0;
x_21 = l_List_toStringAux___at_instToStringByteArray___spec__2(x_20, x_16);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_List_toString___at_instToStringByteArray___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_instToStringByteArray___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_instToStringByteArray___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_instToStringByteArray___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_instToStringByteArray___spec__1___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 1;
x_5 = l_List_toStringAux___at_instToStringByteArray___spec__2(x_4, x_1);
x_6 = l_List_toString___at_instToStringByteArray___spec__1___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_toString___at_instToStringByteArray___spec__1___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 1;
x_14 = l_List_toStringAux___at_instToStringByteArray___spec__2(x_13, x_12);
x_15 = l_List_toString___at_instToStringByteArray___spec__1___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_toString___at_instToStringByteArray___spec__1___closed__3;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_instToStringByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_toList(x_1);
lean_dec(x_1);
x_3 = l_List_toString___at_instToStringByteArray___spec__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at_instToStringByteArray___spec__2(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_instInhabitedUInt64;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_ByteArray_toUInt64LE_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assertion violation: ");
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bs.size == 8\n  ");
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__1;
x_2 = l_ByteArray_toUInt64LE_x21___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.ByteArray.Basic");
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ByteArray.toUInt64LE!");
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__4;
x_2 = l_ByteArray_toUInt64LE_x21___closed__5;
x_3 = lean_unsigned_to_nat(91u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_ByteArray_toUInt64LE_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_ByteArray_toUInt64LE_x21___closed__6;
x_6 = l_panic___at_ByteArray_toUInt64LE_x21___spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint8_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint8_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_byte_array_get(x_1, x_7);
x_9 = ((uint64_t)x_8);
x_10 = 56;
x_11 = x_9 << x_10 % 64;
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_byte_array_get(x_1, x_12);
x_14 = ((uint64_t)x_13);
x_15 = 48;
x_16 = x_14 << x_15 % 64;
x_17 = x_11 | x_16;
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_byte_array_get(x_1, x_18);
x_20 = ((uint64_t)x_19);
x_21 = 40;
x_22 = x_20 << x_21 % 64;
x_23 = x_17 | x_22;
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_byte_array_get(x_1, x_24);
x_26 = ((uint64_t)x_25);
x_27 = 32;
x_28 = x_26 << x_27 % 64;
x_29 = x_23 | x_28;
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_byte_array_get(x_1, x_30);
x_32 = ((uint64_t)x_31);
x_33 = 24;
x_34 = x_32 << x_33 % 64;
x_35 = x_29 | x_34;
x_36 = lean_unsigned_to_nat(5u);
x_37 = lean_byte_array_get(x_1, x_36);
x_38 = ((uint64_t)x_37);
x_39 = 16;
x_40 = x_38 << x_39 % 64;
x_41 = x_35 | x_40;
x_42 = lean_unsigned_to_nat(6u);
x_43 = lean_byte_array_get(x_1, x_42);
x_44 = ((uint64_t)x_43);
x_45 = 8;
x_46 = x_44 << x_45 % 64;
x_47 = x_41 | x_46;
x_48 = lean_unsigned_to_nat(7u);
x_49 = lean_byte_array_get(x_1, x_48);
lean_dec(x_1);
x_50 = ((uint64_t)x_49);
x_51 = x_47 | x_50;
x_52 = lean_box_uint64(x_51);
return x_52;
}
}
}
static lean_object* _init_l_ByteArray_toUInt64BE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ByteArray.toUInt64BE!");
return x_1;
}
}
static lean_object* _init_l_ByteArray_toUInt64BE_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_ByteArray_toUInt64LE_x21___closed__4;
x_2 = l_ByteArray_toUInt64BE_x21___closed__1;
x_3 = lean_unsigned_to_nat(103u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_ByteArray_toUInt64LE_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_ByteArray_toUInt64BE_x21___closed__2;
x_6 = l_panic___at_ByteArray_toUInt64LE_x21___spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint8_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint8_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; 
x_7 = lean_unsigned_to_nat(7u);
x_8 = lean_byte_array_get(x_1, x_7);
x_9 = ((uint64_t)x_8);
x_10 = 56;
x_11 = x_9 << x_10 % 64;
x_12 = lean_unsigned_to_nat(6u);
x_13 = lean_byte_array_get(x_1, x_12);
x_14 = ((uint64_t)x_13);
x_15 = 48;
x_16 = x_14 << x_15 % 64;
x_17 = x_11 | x_16;
x_18 = lean_unsigned_to_nat(5u);
x_19 = lean_byte_array_get(x_1, x_18);
x_20 = ((uint64_t)x_19);
x_21 = 40;
x_22 = x_20 << x_21 % 64;
x_23 = x_17 | x_22;
x_24 = lean_unsigned_to_nat(4u);
x_25 = lean_byte_array_get(x_1, x_24);
x_26 = ((uint64_t)x_25);
x_27 = 32;
x_28 = x_26 << x_27 % 64;
x_29 = x_23 | x_28;
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_byte_array_get(x_1, x_30);
x_32 = ((uint64_t)x_31);
x_33 = 24;
x_34 = x_32 << x_33 % 64;
x_35 = x_29 | x_34;
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_byte_array_get(x_1, x_36);
x_38 = ((uint64_t)x_37);
x_39 = 16;
x_40 = x_38 << x_39 % 64;
x_41 = x_35 | x_40;
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_byte_array_get(x_1, x_42);
x_44 = ((uint64_t)x_43);
x_45 = 8;
x_46 = x_44 << x_45 % 64;
x_47 = x_41 | x_46;
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_byte_array_get(x_1, x_48);
x_50 = ((uint64_t)x_49);
x_51 = x_47 | x_50;
x_52 = lean_box_uint64(x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_toUInt64BE_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_Subarray(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ByteArray_empty___closed__1 = _init_l_ByteArray_empty___closed__1();
lean_mark_persistent(l_ByteArray_empty___closed__1);
l_ByteArray_empty = _init_l_ByteArray_empty();
lean_mark_persistent(l_ByteArray_empty);
l_ByteArray_instInhabitedByteArray = _init_l_ByteArray_instInhabitedByteArray();
lean_mark_persistent(l_ByteArray_instInhabitedByteArray);
l_ByteArray_instAppendByteArray___closed__1 = _init_l_ByteArray_instAppendByteArray___closed__1();
lean_mark_persistent(l_ByteArray_instAppendByteArray___closed__1);
l_ByteArray_instAppendByteArray = _init_l_ByteArray_instAppendByteArray();
lean_mark_persistent(l_ByteArray_instAppendByteArray);
l_List_toStringAux___at_instToStringByteArray___spec__2___closed__1 = _init_l_List_toStringAux___at_instToStringByteArray___spec__2___closed__1();
lean_mark_persistent(l_List_toStringAux___at_instToStringByteArray___spec__2___closed__1);
l_List_toStringAux___at_instToStringByteArray___spec__2___closed__2 = _init_l_List_toStringAux___at_instToStringByteArray___spec__2___closed__2();
lean_mark_persistent(l_List_toStringAux___at_instToStringByteArray___spec__2___closed__2);
l_List_toString___at_instToStringByteArray___spec__1___closed__1 = _init_l_List_toString___at_instToStringByteArray___spec__1___closed__1();
lean_mark_persistent(l_List_toString___at_instToStringByteArray___spec__1___closed__1);
l_List_toString___at_instToStringByteArray___spec__1___closed__2 = _init_l_List_toString___at_instToStringByteArray___spec__1___closed__2();
lean_mark_persistent(l_List_toString___at_instToStringByteArray___spec__1___closed__2);
l_List_toString___at_instToStringByteArray___spec__1___closed__3 = _init_l_List_toString___at_instToStringByteArray___spec__1___closed__3();
lean_mark_persistent(l_List_toString___at_instToStringByteArray___spec__1___closed__3);
l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1 = _init_l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1();
lean_mark_persistent(l_panic___at_ByteArray_toUInt64LE_x21___spec__1___boxed__const__1);
l_ByteArray_toUInt64LE_x21___closed__1 = _init_l_ByteArray_toUInt64LE_x21___closed__1();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__1);
l_ByteArray_toUInt64LE_x21___closed__2 = _init_l_ByteArray_toUInt64LE_x21___closed__2();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__2);
l_ByteArray_toUInt64LE_x21___closed__3 = _init_l_ByteArray_toUInt64LE_x21___closed__3();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__3);
l_ByteArray_toUInt64LE_x21___closed__4 = _init_l_ByteArray_toUInt64LE_x21___closed__4();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__4);
l_ByteArray_toUInt64LE_x21___closed__5 = _init_l_ByteArray_toUInt64LE_x21___closed__5();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__5);
l_ByteArray_toUInt64LE_x21___closed__6 = _init_l_ByteArray_toUInt64LE_x21___closed__6();
lean_mark_persistent(l_ByteArray_toUInt64LE_x21___closed__6);
l_ByteArray_toUInt64BE_x21___closed__1 = _init_l_ByteArray_toUInt64BE_x21___closed__1();
lean_mark_persistent(l_ByteArray_toUInt64BE_x21___closed__1);
l_ByteArray_toUInt64BE_x21___closed__2 = _init_l_ByteArray_toUInt64BE_x21___closed__2();
lean_mark_persistent(l_ByteArray_toUInt64BE_x21___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
