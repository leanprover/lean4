// Lean compiler output
// Module: Init.Data.Int.DivModLemmas
// Imports: Init.Data.Int.DivMod Init.Data.Int.Order Init.Data.Nat.Dvd Init.RCases Init.TacticsExtra
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
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object*, lean_object*);
static lean_object* l_Int_bmod___closed__1;
lean_object* l_Int_emod(lean_object*, lean_object*);
static lean_object* l_Int_bmod___closed__2;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bmod(lean_object*, lean_object*);
static lean_object* l_Int_decidableDvd___closed__1;
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_ediv(lean_object*, lean_object*);
static lean_object* _init_l_Int_decidableDvd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Int_emod(x_2, x_1);
x_4 = l_Int_decidableDvd___closed__1;
x_5 = lean_int_dec_eq(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_decidableDvd(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Int_bmod___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_bmod___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_bmod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_nat_to_int(x_2);
x_4 = l_Int_emod(x_1, x_3);
x_5 = l_Int_bmod___closed__1;
x_6 = lean_int_add(x_3, x_5);
x_7 = l_Int_bmod___closed__2;
x_8 = l_Int_ediv(x_6, x_7);
lean_dec(x_6);
x_9 = lean_int_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_int_sub(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
return x_10;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_bmod(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Int_DivMod(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin, lean_object*);
lean_object* initialize_Init_RCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivModLemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod(builtin, lean_io_mk_world());
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
res = initialize_Init_TacticsExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_decidableDvd___closed__1 = _init_l_Int_decidableDvd___closed__1();
lean_mark_persistent(l_Int_decidableDvd___closed__1);
l_Int_bmod___closed__1 = _init_l_Int_bmod___closed__1();
lean_mark_persistent(l_Int_bmod___closed__1);
l_Int_bmod___closed__2 = _init_l_Int_bmod___closed__2();
lean_mark_persistent(l_Int_bmod___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
