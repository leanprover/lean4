// Lean compiler output
// Module: Init.Data.Int.Cooper
// Imports: Init.Data.Int.DivMod.Lemmas Init.Data.Int.Gcd
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
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* l_Int_lcm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_int_sub(x_2, x_1);
x_5 = l_Int_toNat(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_add__of__le___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_add__of__le(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_int_mul(x_1, x_5);
x_7 = lean_int_sub(x_6, x_4);
lean_dec(x_6);
x_8 = lean_int_mul(x_1, x_3);
x_9 = l_Int_gcd(x_8, x_2);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_ediv(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
x_12 = l_Int_lcm(x_1, x_11);
lean_dec(x_11);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_emod(x_7, x_13);
lean_dec(x_13);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Int_Cooper_resolve__left(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_int_mul(x_1, x_5);
x_8 = l_Int_add__of__le(x_4, x_7, lean_box(0));
lean_dec(x_7);
x_9 = lean_int_mul(x_1, x_3);
x_10 = l_Int_gcd(x_9, x_2);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_ediv(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
x_13 = l_Int_lcm(x_1, x_12);
lean_dec(x_12);
x_14 = lean_nat_mod(x_8, x_13);
lean_dec(x_13);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_Cooper_resolve__left_x27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_int_add(x_3, x_2);
x_5 = lean_int_ediv(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_Cooper_resolve__left__inv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Cooper(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Gcd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
