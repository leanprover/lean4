// Lean compiler output
// Module: Init.Data.Int.Gcd
// Imports: Init.Data.Int.Basic Init.Data.Nat.Gcd Init.Data.Nat.Lcm Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Nat_lcm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_lcm(lean_object*, lean_object*);
lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_dvdProdDvdOfDvdProd___redArg___closed__0;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Int_gcd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_lcm___boxed(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Int_gcd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_nat_abs(x_1);
x_4 = lean_nat_abs(x_2);
x_5 = lean_nat_gcd(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_gcd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_gcd(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_dvdProdDvdOfDvdProd___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_nat_abs(x_1);
x_5 = lean_nat_abs(x_2);
x_6 = lean_nat_abs(x_3);
x_7 = l_Nat_dvdProdDvdOfDvdProd___redArg(x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = l_Int_dvdProdDvdOfDvdProd___redArg___closed__0;
x_9 = lean_int_dec_le(x_8, x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_nat_to_int(x_11);
x_14 = lean_int_neg(x_13);
lean_dec(x_13);
x_15 = lean_nat_to_int(x_12);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_nat_to_int(x_16);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = lean_nat_to_int(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_nat_to_int(x_23);
x_26 = lean_nat_to_int(x_24);
lean_ctor_set(x_7, 1, x_26);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_nat_to_int(x_27);
x_30 = lean_nat_to_int(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_dvdProdDvdOfDvdProd___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_dvdProdDvdOfDvdProd___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_dvdProdDvdOfDvdProd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_lcm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_nat_abs(x_1);
x_4 = lean_nat_abs(x_2);
x_5 = l_Nat_lcm(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_lcm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_lcm(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Lcm(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lcm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_dvdProdDvdOfDvdProd___redArg___closed__0 = _init_l_Int_dvdProdDvdOfDvdProd___redArg___closed__0();
lean_mark_persistent(l_Int_dvdProdDvdOfDvdProd___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
