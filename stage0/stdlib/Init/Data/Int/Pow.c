// Lean compiler output
// Module: Init.Data.Int.Pow
// Imports: public import Init.Data.Nat.Lemmas
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
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Int_powImp___closed__0;
LEAN_EXPORT lean_object* l_Int_powImp(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_powImp___boxed(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* _init_l_Int_powImp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_powImp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Int_powImp___closed__0;
x_9 = lean_int_dec_le(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_mod(x_2, x_10);
x_12 = lean_nat_dec_eq(x_11, x_7);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_nat_abs(x_1);
x_14 = lean_nat_pow(x_13, x_2);
lean_dec(x_13);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
return x_16;
}
else
{
goto block_6;
}
}
else
{
goto block_6;
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_nat_abs(x_1);
x_4 = lean_nat_pow(x_3, x_2);
lean_dec(x_3);
x_5 = lean_nat_to_int(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Int_powImp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_powImp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_powImp___closed__0 = _init_l_Int_powImp___closed__0();
lean_mark_persistent(l_Int_powImp___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
