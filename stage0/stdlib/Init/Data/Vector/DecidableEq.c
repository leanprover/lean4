// Lean compiler output
// Module: Init.Data.Vector.DecidableEq
// Imports: Init.Data.Array.DecidableEq Init.Data.Vector.Lemmas
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
LEAN_EXPORT lean_object* l_Vector_instDecidableEq___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableEq(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = lean_array_fget(x_5, x_12);
x_14 = lean_array_fget(x_6, x_12);
lean_inc(x_2);
x_15 = lean_apply_2(x_2, x_13, x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_2);
x_17 = 0;
return x_17;
}
else
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_2);
x_19 = 1;
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Vector_instDecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_1);
x_5 = l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1___rarg(x_1, x_2, x_3, x_4, x_3, x_4, x_1, lean_box(0));
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Vector_instDecidableEq___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_isEqvAux___at_Vector_instDecidableEq___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Vector_instDecidableEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Vector_instDecidableEq___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_DecidableEq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_DecidableEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
