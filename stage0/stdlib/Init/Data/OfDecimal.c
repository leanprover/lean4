// Lean compiler output
// Module: Init.Data.OfDecimal
// Imports: Init.Data.Float Init.Data.Nat
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
double l_instOfDecimalFloat(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Float_fromDecimal_fromDec_match__1___rarg(lean_object*, lean_object*, lean_object*);
double l_Float_fromDecimal_fromDec___closed__1;
double l_Float_fromDecimal_fromDec(double, lean_object*);
lean_object* l_Float_fromDecimal_fromDec_match__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
double l_Float_div(double, double);
lean_object* l_instOfDecimalFloat___boxed(lean_object*, lean_object*);
lean_object* l_Float_fromDecimal_fromDec___boxed(lean_object*, lean_object*);
lean_object* l_Float_fromDecimal___boxed(lean_object*, lean_object*);
double l_Float_fromDecimal(lean_object*, lean_object*);
lean_object* l_Float_fromDecimal_fromDec_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_fromDecimal_fromDec_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Float_fromDecimal_fromDec_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Float_fromDecimal_fromDec_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Float_fromDecimal_fromDec_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Float_fromDecimal_fromDec_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static double _init_l_Float_fromDecimal_fromDec___closed__1() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
double l_Float_fromDecimal_fromDec(double x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; double x_7; double x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
x_7 = l_Float_fromDecimal_fromDec___closed__1;
x_8 = x_1 / x_7;
x_1 = x_8;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Float_fromDecimal_fromDec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; lean_object* x_5; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = l_Float_fromDecimal_fromDec(x_3, x_2);
x_5 = lean_box_float(x_4);
return x_5;
}
}
double l_Float_fromDecimal(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; 
x_3 = lean_float_of_nat(x_1);
x_4 = l_Float_fromDecimal_fromDec(x_3, x_2);
return x_4;
}
}
lean_object* l_Float_fromDecimal___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; lean_object* x_4; 
x_3 = l_Float_fromDecimal(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box_float(x_3);
return x_4;
}
}
double l_instOfDecimalFloat(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; 
x_3 = l_Float_fromDecimal(x_1, x_2);
return x_3;
}
}
lean_object* l_instOfDecimalFloat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; lean_object* x_4; 
x_3 = l_instOfDecimalFloat(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Float(lean_object*);
lean_object* initialize_Init_Data_Nat(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_OfDecimal(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Float_fromDecimal_fromDec___closed__1 = _init_l_Float_fromDecimal_fromDec___closed__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
