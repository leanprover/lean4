// Lean compiler output
// Module: Init.Data.String.Pattern.Char
// Imports: public import Init.Data.String.Pattern.Basic import Init.Data.String.Lemmas.FindPos import Init.Data.String.Termination import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Lemmas.Order import Init.Data.Option.Lemmas
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcher(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcher___boxed(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_sub(x_5, x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_uint32_dec_eq(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_utf8_next_fast(x_3, x_4);
x_13 = lean_nat_sub(x_12, x_4);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_string_utf8_get_fast(x_4, x_5);
x_7 = lean_uint32_dec_eq(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_string_utf8_next_fast(x_4, x_5);
x_10 = lean_nat_sub(x_9, x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_sub(x_5, x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_uint32_dec_eq(x_9, x_1);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_box_uint32(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box_uint32(x_1);
x_5 = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_box_uint32(x_1);
x_7 = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instForwardPatternChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_Slice_Pattern_Char_instForwardPatternChar(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcher(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box_uint32(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcher___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcher(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = l_String_Slice_posLE(x_2, x_10);
x_12 = lean_nat_add(x_4, x_11);
x_13 = lean_string_utf8_get_fast(x_3, x_12);
lean_dec(x_12);
x_14 = lean_uint32_dec_eq(x_13, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_6);
x_17 = lean_box(0);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_String_Slice_posLE(x_2, x_9);
x_11 = lean_nat_add(x_5, x_10);
x_12 = lean_string_utf8_get_fast(x_4, x_11);
lean_dec(x_11);
x_13 = lean_uint32_dec_eq(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = l_String_Slice_posLE(x_2, x_10);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_11);
x_13 = lean_string_utf8_get_fast(x_3, x_12);
lean_dec(x_12);
x_14 = lean_uint32_dec_eq(x_13, x_1);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_box_uint32(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box_uint32(x_1);
x_5 = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_box_uint32(x_1);
x_7 = lean_alloc_closure((void*)(l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instBackwardPatternChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_Slice_Pattern_Char_instBackwardPatternChar(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box_uint32(x_1);
x_3 = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcher(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
