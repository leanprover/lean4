// Lean compiler output
// Module: Init.Data.Slice.Array.Basic
// Imports: public import Init.Data.Array.Subarray public import Init.Data.Slice.Notation public import Init.Data.Range.Polymorphic.Nat
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
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___lam__0(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_14; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_le(x_3, x_5);
if (x_14 == 0)
{
x_7 = x_3;
goto block_13;
}
else
{
lean_dec(x_3);
x_7 = x_5;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_dec_le(x_9, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = l_Array_toSubarray___redArg(x_1, x_7, x_6);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = l_Array_toSubarray___redArg(x_1, x_7, x_9);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray___lam__0), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_le(x_3, x_5);
if (x_12 == 0)
{
x_7 = x_3;
goto block_11;
}
else
{
lean_dec(x_3);
x_7 = x_5;
goto block_11;
}
block_11:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = l_Array_toSubarray___redArg(x_1, x_7, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = l_Array_toSubarray___redArg(x_1, x_7, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__1___lam__0), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_le(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Array_toSubarray___redArg(x_1, x_2, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__2___lam__0), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_7);
x_15 = lean_nat_dec_le(x_14, x_5);
if (x_15 == 0)
{
x_8 = x_14;
goto block_13;
}
else
{
lean_dec(x_14);
x_8 = x_5;
goto block_13;
}
block_13:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_add(x_4, x_7);
x_10 = lean_nat_dec_le(x_9, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = l_Array_toSubarray___redArg(x_1, x_8, x_6);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = l_Array_toSubarray___redArg(x_1, x_8, x_9);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__3___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableArrayNatSubarray__3___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = lean_nat_dec_le(x_13, x_5);
if (x_14 == 0)
{
x_7 = x_13;
goto block_11;
}
else
{
lean_dec(x_13);
x_7 = x_5;
goto block_11;
}
block_11:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = l_Array_toSubarray___redArg(x_1, x_7, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = l_Array_toSubarray___redArg(x_1, x_7, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__4___lam__0), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Array_toSubarray___redArg(x_1, x_6, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__5___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__5___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableArrayNatSubarray__5___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
x_7 = lean_nat_dec_le(x_6, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = l_Array_toSubarray___redArg(x_1, x_3, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__6___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__6___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instSliceableArrayNatSubarray__6___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = l_Array_toSubarray___redArg(x_1, x_3, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__7___lam__0), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = l_Array_toSubarray___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instSliceableArrayNatSubarray__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instSliceableArrayNatSubarray__8___lam__0), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
