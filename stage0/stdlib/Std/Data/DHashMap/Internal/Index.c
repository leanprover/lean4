// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Index
// Imports: Init.Data.UInt.Lemmas Init.Data.UInt.Bitwise
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___redArg___boxed(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx___redArg(lean_object*, uint64_t);
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scrambleHash___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Std_DHashMap_Internal_scrambleHash(uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint64_t l_Std_DHashMap_Internal_scrambleHash(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; 
x_2 = 32;
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = lean_uint64_xor(x_1, x_3);
x_5 = 16;
x_6 = lean_uint64_shift_right(x_4, x_5);
x_7 = lean_uint64_xor(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_scrambleHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Std_DHashMap_Internal_scrambleHash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx___redArg(lean_object* x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; 
x_3 = 32;
x_4 = lean_uint64_shift_right(x_2, x_3);
x_5 = lean_uint64_xor(x_2, x_4);
x_6 = 16;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_of_nat(x_1);
x_11 = 1;
x_12 = lean_usize_sub(x_10, x_11);
x_13 = lean_usize_land(x_9, x_12);
return x_13;
}
}
LEAN_EXPORT size_t l_Std_DHashMap_Internal_mkIdx(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = 32;
x_5 = lean_uint64_shift_right(x_3, x_4);
x_6 = lean_uint64_xor(x_3, x_5);
x_7 = 16;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = lean_usize_of_nat(x_1);
x_12 = 1;
x_13 = lean_usize_sub(x_11, x_12);
x_14 = lean_usize_land(x_10, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_DHashMap_Internal_mkIdx___redArg(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_mkIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_5 = l_Std_DHashMap_Internal_mkIdx(x_1, x_2, x_4);
lean_dec(x_1);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt_Bitwise(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Bitwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
