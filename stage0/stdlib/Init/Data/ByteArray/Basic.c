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
lean_object* l_ByteArray_push___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_ByteArray_instAppendByteArray___closed__1;
lean_object* l_ByteArray_instAppendByteArray;
lean_object* l_ByteArray_toList_loop(lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__9;
lean_object* l_ByteArray_toList_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2(uint8_t, lean_object*);
lean_object* l_instToStringByteArray(lean_object*);
lean_object* l_ByteArray_findIdx_x3f_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_data(lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_ByteArray_set_x21_match__1(lean_object*);
lean_object* l_ByteArray_push_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_findIdx_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_ByteArray_data___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_toByteArray_loop(lean_object*, lean_object*);
lean_object* l_List_toByteArray_loop_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_empty;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_ByteArray_get_x21_match__1(lean_object*);
lean_object* l_ByteArray_get_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instReprList___rarg___closed__1;
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_empty___closed__1;
lean_object* l_instToStringByteArray___boxed(lean_object*);
lean_object* l_List_toString___at_instToStringByteArray___spec__1(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* lean_byte_array_set(lean_object*, lean_object*, uint8_t);
lean_object* l_ByteArray_toList___boxed(lean_object*);
lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* l_ByteArray_get_x21___boxed(lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* l_ByteArray_size_match__1(lean_object*);
lean_object* l_ByteArray_copySlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_append___boxed(lean_object*, lean_object*);
lean_object* l_ByteArray_instInhabitedByteArray;
lean_object* l_ByteArray_size_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_List_toByteArray_loop_match__1(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ByteArray_isEmpty___boxed(lean_object*);
lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_extract___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_append(lean_object*, lean_object*);
lean_object* l_ByteArray_push_match__1___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_List_toByteArray(lean_object*);
lean_object* l_ByteArray_set_x21_match__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_push_match__1(lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* l_ByteArray_set_x21_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_set_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_ByteArray_mk___boxed(lean_object*);
lean_object* l_ByteArray_mkEmpty___boxed(lean_object*);
extern lean_object* l_term_x5b___x5d___closed__3;
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_ByteArray_size___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
#define _init_l_ByteArray_empty___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = lean_unsigned_to_nat(0u);\
x_2 = lean_mk_empty_byte_array(x_1);\
__INIT_VAR__ = x_2; goto l_ByteArray_empty___closed__1_end;\
}\
l_ByteArray_empty___closed__1_end: ((void) 0);}
#define _init_l_ByteArray_empty(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_ByteArray_empty___closed__1;\
__INIT_VAR__ = x_1; goto l_ByteArray_empty_end;\
}\
l_ByteArray_empty_end: ((void) 0);}
#define _init_l_ByteArray_instInhabitedByteArray(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_ByteArray_empty;\
__INIT_VAR__ = x_1; goto l_ByteArray_instInhabitedByteArray_end;\
}\
l_ByteArray_instInhabitedByteArray_end: ((void) 0);}
lean_object* l_ByteArray_push_match__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(x_2);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_ByteArray_push_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ByteArray_push_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_ByteArray_push_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_ByteArray_push_match__1___rarg(x_1, x_4, x_3);
return x_5;
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
lean_object* l_ByteArray_size_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_ByteArray_size_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ByteArray_size_match__1___rarg), 2, 0);
return x_2;
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
lean_object* l_ByteArray_get_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_ByteArray_get_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ByteArray_get_x21_match__1___rarg), 3, 0);
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
lean_object* l_ByteArray_set_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(x_3);
x_7 = lean_apply_3(x_4, x_5, x_2, x_6);
return x_7;
}
}
lean_object* l_ByteArray_set_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ByteArray_set_x21_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_ByteArray_set_x21_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_ByteArray_set_x21_match__1___rarg(x_1, x_2, x_5, x_4);
return x_6;
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
lean_object* l_ByteArray_copySlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_ByteArray_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_ByteArray_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_ByteArray_append(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_ByteArray_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_append(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
#define _init_l_ByteArray_instAppendByteArray___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_ByteArray_append___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_ByteArray_instAppendByteArray___closed__1_end;\
}\
l_ByteArray_instAppendByteArray___closed__1_end: ((void) 0);}
#define _init_l_ByteArray_instAppendByteArray(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_ByteArray_instAppendByteArray___closed__1;\
__INIT_VAR__ = x_1; goto l_ByteArray_instAppendByteArray_end;\
}\
l_ByteArray_instAppendByteArray_end: ((void) 0);}
lean_object* l_ByteArray_toList_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_ByteArray_toList_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_toList_loop(x_1, x_2, x_3);
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
x_4 = l_ByteArray_toList_loop(x_1, x_3, x_2);
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
lean_object* l_ByteArray_findIdx_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_ByteArray_findIdx_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_ByteArray_findIdx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f_loop(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_ByteArray_findIdx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ByteArray_findIdx_x3f(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_toByteArray_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
lean_object* l_List_toByteArray_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toByteArray_loop_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_toByteArray_loop(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_toByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_empty;
x_3 = l_List_toByteArray_loop(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_9 = l_term_x5b___x5d___closed__5;
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
x_14 = l_Lean_instInhabitedParserDescr___closed__1;
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
lean_object* l_List_toString___at_instToStringByteArray___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_instReprList___rarg___closed__1;
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
x_6 = l_term_x5b___x5d___closed__3;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_term_x5b___x5d___closed__9;
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
x_15 = l_term_x5b___x5d___closed__3;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_term_x5b___x5d___closed__9;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
lean_object* l_instToStringByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_toList(x_1);
x_3 = l_List_toString___at_instToStringByteArray___spec__1(x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___at_instToStringByteArray___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at_instToStringByteArray___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_instToStringByteArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToStringByteArray(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_Subarray(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_ByteArray_Basic(lean_object* w) {
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
_init_l_ByteArray_empty___closed__1(l_ByteArray_empty___closed__1);
lean_mark_persistent(l_ByteArray_empty___closed__1);
_init_l_ByteArray_empty(l_ByteArray_empty);
lean_mark_persistent(l_ByteArray_empty);
_init_l_ByteArray_instInhabitedByteArray(l_ByteArray_instInhabitedByteArray);
lean_mark_persistent(l_ByteArray_instInhabitedByteArray);
_init_l_ByteArray_instAppendByteArray___closed__1(l_ByteArray_instAppendByteArray___closed__1);
lean_mark_persistent(l_ByteArray_instAppendByteArray___closed__1);
_init_l_ByteArray_instAppendByteArray(l_ByteArray_instAppendByteArray);
lean_mark_persistent(l_ByteArray_instAppendByteArray);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
