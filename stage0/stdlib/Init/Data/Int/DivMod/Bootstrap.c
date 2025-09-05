// Lean compiler output
// Module: Init.Data.Int.DivMod.Bootstrap
// Imports: Init.Data.Int.DivMod.Basic Init.Data.Int.Order Init.Data.Nat.Dvd Init.RCases
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
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0;
x_10 = lean_int_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_nat_abs(x_1);
x_12 = lean_int_dec_lt(x_2, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_nat_abs(x_2);
x_14 = lean_apply_2(x_3, x_11, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_15 = lean_nat_abs(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = lean_apply_2(x_4, x_11, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_nat_abs(x_1);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_int_dec_lt(x_2, x_9);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_7);
x_23 = lean_nat_abs(x_2);
x_24 = lean_nat_dec_eq(x_23, x_8);
if (x_24 == 1)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_6);
x_25 = lean_apply_1(x_5, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_26 = lean_nat_sub(x_23, x_20);
lean_dec(x_23);
x_27 = lean_apply_2(x_6, x_21, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_nat_abs(x_2);
x_29 = lean_nat_sub(x_28, x_20);
lean_dec(x_28);
x_30 = lean_apply_2(x_7, x_21, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin, lean_object*);
lean_object* initialize_Init_RCases(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0 = _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
