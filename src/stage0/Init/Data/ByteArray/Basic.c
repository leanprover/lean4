// Lean compiler output
// Module: Init.Data.ByteArray.Basic
// Imports: Init.Data.Array.Basic Init.Data.UInt Init.Data.Option.Basic
#include "runtime/lean.h"
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
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_ByteArray_mk___boxed(lean_object*);
lean_object* l_ByteArray_mkEmpty___boxed(lean_object*);
lean_object* l_ByteArray_toList___boxed(lean_object*);
lean_object* l_ByteArray_toListAux___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_ByteArray_isEmpty___boxed(lean_object*);
lean_object* l_List_toByteArrayAux(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_ByteArray_data___boxed(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_ByteArray_toListAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_set(lean_object*, lean_object*, uint8_t);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_ByteArray_get_x21___boxed(lean_object*, lean_object*);
lean_object* l_ByteArray_HasToString(lean_object*);
lean_object* l_ByteArray_set_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_ByteArray_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_toString___at_ByteArray_HasToString___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_ByteArray_mkEmpty(lean_object*);
lean_object* lean_byte_array_data(lean_object*);
lean_object* l_ByteArray_toListAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_empty___closed__1;
lean_object* l_List_toByteArray(lean_object*);
lean_object* l_ByteArray_HasToString___boxed(lean_object*);
lean_object* l_ByteArray_push___boxed(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(uint8_t, lean_object*);
lean_object* l_List_toByteArrayAux___main(lean_object*, lean_object*);
lean_object* l_ByteArray_Inhabited;
lean_object* l_ByteArray_toListAux(lean_object*, lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* l_ByteArray_size___boxed(lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_ByteArray_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_mk(x_1);
return x_2;
}
}
lean_object* l_ByteArray_data___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_data(x_1);
return x_2;
}
}
lean_object* l_ByteArray_mkEmpty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_mk_empty_byte_array(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_ByteArray_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_byte_array(x_1);
return x_2;
}
}
lean_object* _init_l_ByteArray_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty___closed__1;
return x_1;
}
}
lean_object* _init_l_ByteArray_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
lean_object* l_ByteArray_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = lean_byte_array_push(x_1, x_3);
return x_4;
}
}
lean_object* l_ByteArray_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_byte_array_size(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_ByteArray_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_ByteArray_set_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_ByteArray_isEmpty(lean_object* x_1) {
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
lean_object* l_ByteArray_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ByteArray_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_ByteArray_toListAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_ByteArray_toListAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_toListAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_ByteArray_toListAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_toListAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_ByteArray_toListAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_toListAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_ByteArray_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_ByteArray_toListAux___main(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_ByteArray_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_toList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_toByteArrayAux___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_toByteArrayAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_toByteArrayAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_empty;
x_3 = l_List_toByteArrayAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = lean_uint8_to_nat(x_6);
x_8 = l_Nat_repr(x_7);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_1, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = l_String_splitAux___main___closed__1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = lean_uint8_to_nat(x_16);
x_18 = l_Nat_repr(x_17);
x_19 = 0;
x_20 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_19, x_15);
x_21 = lean_string_append(x_18, x_20);
lean_dec(x_20);
return x_21;
}
}
}
}
lean_object* l_List_toString___at_ByteArray_HasToString___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_ByteArray_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_toList(x_1);
x_3 = l_List_toString___at_ByteArray_HasToString___spec__1(x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_ByteArray_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_ByteArray_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
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
l_ByteArray_Inhabited = _init_l_ByteArray_Inhabited();
lean_mark_persistent(l_ByteArray_Inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
