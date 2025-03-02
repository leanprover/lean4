// Lean compiler output
// Module: Init.Data.Int.Gcd
// Imports: Init.Data.Int.Basic Init.Data.Nat.Gcd Init.Data.Nat.Lcm Init.Data.Int.DivMod.Lemmas
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
LEAN_EXPORT lean_object* l_Int_gcd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_lcm___boxed(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
