// Lean compiler output
// Module: Init.Data.Nat.Bitwise
// Imports: Init.Data.Nat.Basic Init.Data.Nat.Div Init.Coe
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
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
lean_object* l_Nat_bitwise(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Nat_bitwise___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_bitwise___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_bitwise___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Nat_bitwise___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_div(x_2, x_7);
x_9 = lean_nat_div(x_3, x_7);
lean_inc(x_1);
x_10 = l_Nat_bitwise___main(x_1, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_nat_mod(x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_mod(x_3, x_7);
x_15 = lean_nat_dec_eq(x_14, x_12);
lean_dec(x_14);
x_16 = lean_box(x_13);
x_17 = lean_box(x_15);
x_18 = lean_apply_2(x_1, x_16, x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_nat_add(x_10, x_10);
lean_dec(x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_nat_add(x_10, x_10);
lean_dec(x_10);
x_23 = lean_nat_add(x_22, x_12);
lean_dec(x_22);
return x_23;
}
}
else
{
uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_24 = 1;
x_25 = 0;
x_26 = lean_box(x_24);
x_27 = lean_box(x_25);
x_28 = lean_apply_2(x_1, x_26, x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_unsigned_to_nat(0u);
return x_31;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
else
{
uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
x_32 = 0;
x_33 = 1;
x_34 = lean_box(x_32);
x_35 = lean_box(x_33);
x_36 = lean_apply_2(x_1, x_34, x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
x_38 = l_coeDecidableEq(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_unsigned_to_nat(0u);
return x_39;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
}
lean_object* l_Nat_bitwise___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_bitwise___main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_bitwise(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_bitwise___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_bitwise___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_bitwise(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_land(x_1, x_2);
return x_3;
}
}
lean_object* l_Nat_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_lor(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
lean_object* initialize_Init_Data_Nat_Div(lean_object*);
lean_object* initialize_Init_Coe(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Nat_Bitwise(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Coe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
