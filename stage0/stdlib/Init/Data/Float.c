// Lean compiler output
// Module: Init.Data.Float
// Imports: Init.Core Init.Data.ToString.Basic
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
lean_object* l_Float_tanh___boxed(lean_object*);
uint8_t l_floatDecLe(double, double);
lean_object* l_instBEqFloat;
double log2(double);
lean_object* l_Float_cosh___boxed(lean_object*);
lean_object* l_instAddFloat___closed__1;
double sin(double);
double asin(double);
double tan(double);
uint8_t l_floatSpec___elambda__1(lean_object*, lean_object*);
double tanh(double);
double lean_float_of_nat(lean_object*);
double l_Nat_toFloat(lean_object*);
lean_object* l_instSubFloat___closed__1;
lean_object* l_Float_cos___boxed(lean_object*);
extern uint8_t l_instDecidableTrue;
double l_instOfNatFloat(lean_object*);
uint8_t l_Float_beq(double, double);
double sqrt(double);
lean_object* l_Float_log10___boxed(lean_object*);
lean_object* l_Float_div___boxed(lean_object*, lean_object*);
lean_object* l_Float_pow___boxed(lean_object*, lean_object*);
lean_object* l_instHasLessFloat;
lean_object* l_Float_cbrt___boxed(lean_object*);
lean_object* l_Float_atanh___boxed(lean_object*);
double atanh(double);
lean_object* l_floatSpec___closed__1;
uint8_t l_Float_decLe(double, double);
double sinh(double);
lean_object* l_floatSpec___closed__2;
lean_object* l_Float_asin___boxed(lean_object*);
lean_object* l_instInhabitedFloat;
uint8_t l_Float_decLt(double, double);
lean_object* l_Float_tan___boxed(lean_object*);
lean_object* l_Float_sinh___boxed(lean_object*);
lean_object* l_instAddFloat;
lean_object* l_Float_mul___boxed(lean_object*, lean_object*);
lean_object* l_Float_sin___boxed(lean_object*);
lean_object* l_Float_acos___boxed(lean_object*);
lean_object* l_Float_ofNat___boxed(lean_object*);
lean_object* lean_float_to_string(double);
double l_Float_div(double, double);
lean_object* l_instToStringFloat;
lean_object* l_Float_decLt___boxed(lean_object*, lean_object*);
double cosh(double);
double l_Float_sub(double, double);
lean_object* l_floatSpec___elambda__1___boxed(lean_object*, lean_object*);
double l_Float_add(double, double);
double log(double);
lean_object* l_Float_log___boxed(lean_object*);
lean_object* l_instPowFloat___closed__1;
lean_object* l_instDivFloat;
double log10(double);
lean_object* l_Float_atan___boxed(lean_object*);
lean_object* l_instInhabitedFloat___closed__1;
double atan(double);
double atan2(double, double);
double exp(double);
double cos(double);
lean_object* l_Float_exp2___boxed(lean_object*);
lean_object* l_instSubFloat;
lean_object* l_Nat_toFloat___boxed(lean_object*);
lean_object* l_instToStringFloat___closed__1;
double pow(double, double);
lean_object* l_Float_decLe___boxed(lean_object*, lean_object*);
double asinh(double);
lean_object* l_instDivFloat___closed__1;
double acosh(double);
lean_object* l_Float_atan2___boxed(lean_object*, lean_object*);
double acos(double);
lean_object* l_Float_sub___boxed(lean_object*, lean_object*);
lean_object* l_instMulFloat___closed__1;
double cbrt(double);
lean_object* l_Float_sqrt___boxed(lean_object*);
uint8_t l_floatDecLt(double, double);
lean_object* l_floatSpec;
lean_object* l_floatDecLe___boxed(lean_object*, lean_object*);
lean_object* l_instOfNatFloat___boxed(lean_object*);
lean_object* l_Float_toString___boxed(lean_object*);
double exp2(double);
lean_object* l_instMulFloat;
lean_object* l_Float_beq___boxed(lean_object*, lean_object*);
lean_object* l_instHasLessEqFloat;
lean_object* l_instBEqFloat___closed__1;
lean_object* l_Float_exp___boxed(lean_object*);
lean_object* l_Float_add___boxed(lean_object*, lean_object*);
lean_object* l_instPowFloat;
lean_object* l_floatDecLt___boxed(lean_object*, lean_object*);
lean_object* l_Float_log2___boxed(lean_object*);
lean_object* l_Float_asinh___boxed(lean_object*);
double l_Float_mul(double, double);
lean_object* l_Float_acosh___boxed(lean_object*);
uint8_t l_floatSpec___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_instDecidableTrue;
return x_3;
}
}
static lean_object* _init_l_floatSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_floatSpec___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_floatSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_floatSpec___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_floatSpec() {
_start:
{
lean_object* x_1; 
x_1 = l_floatSpec___closed__2;
return x_1;
}
}
lean_object* l_floatSpec___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_floatSpec___elambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_instInhabitedFloat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instInhabitedFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instInhabitedFloat___closed__1;
return x_1;
}
}
lean_object* l_Float_ofNat___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_float_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
lean_object* l_Float_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box_float(x_5);
return x_6;
}
}
lean_object* l_Float_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box_float(x_5);
return x_6;
}
}
lean_object* l_Float_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box_float(x_5);
return x_6;
}
}
lean_object* l_Float_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = x_3 / x_4;
x_6 = lean_box_float(x_5);
return x_6;
}
}
double l_instOfNatFloat(lean_object* x_1) {
_start:
{
double x_2; 
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
lean_object* l_instOfNatFloat___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = l_instOfNatFloat(x_1);
lean_dec(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
static lean_object* _init_l_instAddFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAddFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instAddFloat___closed__1;
return x_1;
}
}
static lean_object* _init_l_instSubFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instSubFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instSubFloat___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMulFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMulFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instMulFloat___closed__1;
return x_1;
}
}
static lean_object* _init_l_instDivFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instDivFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instDivFloat___closed__1;
return x_1;
}
}
static lean_object* _init_l_instHasLessFloat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instHasLessEqFloat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Float_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = x_3 == x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_instBEqFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instBEqFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instBEqFloat___closed__1;
return x_1;
}
}
lean_object* l_Float_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Float_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_floatDecLt(double x_1, double x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
lean_object* l_floatDecLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = l_floatDecLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_floatDecLe(double x_1, double x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
lean_object* l_floatDecLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = l_floatDecLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Float_toString___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_string(x_2);
return x_3;
}
}
static lean_object* _init_l_instToStringFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instToStringFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instToStringFloat___closed__1;
return x_1;
}
}
double l_Nat_toFloat(lean_object* x_1) {
_start:
{
double x_2; 
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
lean_object* l_Nat_toFloat___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = l_Nat_toFloat(x_1);
lean_dec(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
lean_object* l_Float_sin___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = sin(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_cos___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = cos(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_tan___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = tan(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_asin___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = asin(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_acos___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = acos(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_atan___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = atan(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_atan2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = atan2(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
lean_object* l_Float_sinh___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = sinh(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_cosh___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = cosh(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_tanh___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = tanh(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_asinh___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = asinh(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_acosh___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = acosh(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_atanh___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = atanh(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_exp___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = exp(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_exp2___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = exp2(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_log___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = log(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_log2___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = log2(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_log10___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = log10(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = pow(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
lean_object* l_Float_sqrt___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = sqrt(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
lean_object* l_Float_cbrt___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = cbrt(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
static lean_object* _init_l_instPowFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instPowFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instPowFloat___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Float(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_floatSpec___closed__1 = _init_l_floatSpec___closed__1();
lean_mark_persistent(l_floatSpec___closed__1);
l_floatSpec___closed__2 = _init_l_floatSpec___closed__2();
lean_mark_persistent(l_floatSpec___closed__2);
l_floatSpec = _init_l_floatSpec();
lean_mark_persistent(l_floatSpec);
l_instInhabitedFloat___closed__1 = _init_l_instInhabitedFloat___closed__1();
lean_mark_persistent(l_instInhabitedFloat___closed__1);
l_instInhabitedFloat = _init_l_instInhabitedFloat();
lean_mark_persistent(l_instInhabitedFloat);
l_instAddFloat___closed__1 = _init_l_instAddFloat___closed__1();
lean_mark_persistent(l_instAddFloat___closed__1);
l_instAddFloat = _init_l_instAddFloat();
lean_mark_persistent(l_instAddFloat);
l_instSubFloat___closed__1 = _init_l_instSubFloat___closed__1();
lean_mark_persistent(l_instSubFloat___closed__1);
l_instSubFloat = _init_l_instSubFloat();
lean_mark_persistent(l_instSubFloat);
l_instMulFloat___closed__1 = _init_l_instMulFloat___closed__1();
lean_mark_persistent(l_instMulFloat___closed__1);
l_instMulFloat = _init_l_instMulFloat();
lean_mark_persistent(l_instMulFloat);
l_instDivFloat___closed__1 = _init_l_instDivFloat___closed__1();
lean_mark_persistent(l_instDivFloat___closed__1);
l_instDivFloat = _init_l_instDivFloat();
lean_mark_persistent(l_instDivFloat);
l_instHasLessFloat = _init_l_instHasLessFloat();
lean_mark_persistent(l_instHasLessFloat);
l_instHasLessEqFloat = _init_l_instHasLessEqFloat();
lean_mark_persistent(l_instHasLessEqFloat);
l_instBEqFloat___closed__1 = _init_l_instBEqFloat___closed__1();
lean_mark_persistent(l_instBEqFloat___closed__1);
l_instBEqFloat = _init_l_instBEqFloat();
lean_mark_persistent(l_instBEqFloat);
l_instToStringFloat___closed__1 = _init_l_instToStringFloat___closed__1();
lean_mark_persistent(l_instToStringFloat___closed__1);
l_instToStringFloat = _init_l_instToStringFloat();
lean_mark_persistent(l_instToStringFloat);
l_instPowFloat___closed__1 = _init_l_instPowFloat___closed__1();
lean_mark_persistent(l_instPowFloat___closed__1);
l_instPowFloat = _init_l_instPowFloat();
lean_mark_persistent(l_instPowFloat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
