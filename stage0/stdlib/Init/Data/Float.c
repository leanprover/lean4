// Lean compiler output
// Module: Init.Data.Float
// Imports: Init.Core Init.Data.ToString
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
double log2(double);
lean_object* l_Float_cosh___boxed(lean_object*);
double sin(double);
double asin(double);
double tan(double);
uint8_t l_floatSpec___elambda__1(lean_object*, lean_object*);
double tanh(double);
double lean_float_of_nat(lean_object*);
double l_Nat_toFloat(lean_object*);
lean_object* l_Float_cos___boxed(lean_object*);
lean_object* l_Float_HasBeq;
lean_object* l_Float_HasDiv___closed__1;
lean_object* l_Float_HasLessEq;
double l_Float_HasOne;
lean_object* l_Float_HasPow___closed__1;
lean_object* l_Float_HasPow;
uint8_t l_Float_beq(double, double);
double sqrt(double);
lean_object* l_Float_log10___boxed(lean_object*);
lean_object* l_Float_div___boxed(lean_object*, lean_object*);
lean_object* l_Float_pow___boxed(lean_object*, lean_object*);
lean_object* l_Float_cbrt___boxed(lean_object*);
lean_object* l_Float_atanh___boxed(lean_object*);
double atanh(double);
lean_object* l_floatSpec___closed__1;
uint8_t l_Float_decLe(double, double);
double sinh(double);
lean_object* l_floatSpec___closed__2;
lean_object* l_Float_HasMul;
lean_object* l_Float_HasAdd;
lean_object* l_Float_asin___boxed(lean_object*);
lean_object* l_Float_Inhabited;
lean_object* l_Float_HasOfNat;
double l_Float_HasZero___closed__1;
lean_object* l_Float_HasToString;
uint8_t l_Float_decLt(double, double);
lean_object* l_Float_tan___boxed(lean_object*);
lean_object* l_Float_sinh___boxed(lean_object*);
extern uint8_t l_True_Decidable;
lean_object* l_Float_mul___boxed(lean_object*, lean_object*);
lean_object* l_Float_sin___boxed(lean_object*);
lean_object* l_Float_acos___boxed(lean_object*);
lean_object* l_Float_ofNat___boxed(lean_object*);
lean_object* lean_float_to_string(double);
double l_Float_div(double, double);
lean_object* l_Float_HasOfNat___closed__1;
lean_object* l_Float_decLt___boxed(lean_object*, lean_object*);
double cosh(double);
double l_Float_sub(double, double);
lean_object* l_floatSpec___elambda__1___boxed(lean_object*, lean_object*);
double l_Float_add(double, double);
double l_Float_HasOne___closed__1;
double log(double);
lean_object* l_Float_log___boxed(lean_object*);
lean_object* l_Float_HasBeq___closed__1;
double log10(double);
lean_object* l_Float_atan___boxed(lean_object*);
double atan(double);
lean_object* l_Float_HasToString___closed__1;
lean_object* l_Float_HasSub;
lean_object* l_Float_HasSub___closed__1;
double atan2(double, double);
double exp(double);
double cos(double);
lean_object* l_Float_exp2___boxed(lean_object*);
lean_object* l_Float_HasLess;
lean_object* l_Nat_toFloat___boxed(lean_object*);
double pow(double, double);
lean_object* l_Float_HasDiv;
lean_object* l_Float_decLe___boxed(lean_object*, lean_object*);
double asinh(double);
double acosh(double);
lean_object* l_Float_atan2___boxed(lean_object*, lean_object*);
double acos(double);
lean_object* l_Float_sub___boxed(lean_object*, lean_object*);
double cbrt(double);
lean_object* l_Float_sqrt___boxed(lean_object*);
uint8_t l_floatDecLt(double, double);
lean_object* l_floatSpec;
lean_object* l_floatDecLe___boxed(lean_object*, lean_object*);
lean_object* l_Float_toString___boxed(lean_object*);
double exp2(double);
lean_object* l_Float_beq___boxed(lean_object*, lean_object*);
lean_object* l_Float_HasAdd___closed__1;
double l_Float_HasZero;
lean_object* l_Float_exp___boxed(lean_object*);
lean_object* l_Float_HasMul___closed__1;
lean_object* l_Float_add___boxed(lean_object*, lean_object*);
lean_object* l_floatDecLt___boxed(lean_object*, lean_object*);
lean_object* l_Float_Inhabited___closed__1;
lean_object* l_Float_log2___boxed(lean_object*);
lean_object* l_Float_asinh___boxed(lean_object*);
double l_Float_mul(double, double);
lean_object* l_Float_acosh___boxed(lean_object*);
uint8_t l_floatSpec___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_True_Decidable;
return x_3;
}
}
lean_object* _init_l_floatSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_floatSpec___elambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_floatSpec___closed__2() {
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
lean_object* _init_l_floatSpec() {
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
lean_object* _init_l_Float_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Float_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_Inhabited___closed__1;
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
double _init_l_Float_HasZero___closed__1() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
double _init_l_Float_HasZero() {
_start:
{
double x_1; 
x_1 = l_Float_HasZero___closed__1;
return x_1;
}
}
double _init_l_Float_HasOne___closed__1() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
double _init_l_Float_HasOne() {
_start:
{
double x_1; 
x_1 = l_Float_HasOne___closed__1;
return x_1;
}
}
lean_object* _init_l_Float_HasOfNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_ofNat___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasOfNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasOfNat___closed__1;
return x_1;
}
}
lean_object* _init_l_Float_HasAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_add___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasAdd___closed__1;
return x_1;
}
}
lean_object* _init_l_Float_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_Float_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasMul___closed__1;
return x_1;
}
}
lean_object* _init_l_Float_HasDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_div___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasDiv___closed__1;
return x_1;
}
}
lean_object* _init_l_Float_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Float_HasLessEq() {
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
lean_object* _init_l_Float_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasBeq___closed__1;
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
lean_object* _init_l_Float_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_toString___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasToString___closed__1;
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
lean_object* _init_l_Float_HasPow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_pow___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Float_HasPow() {
_start:
{
lean_object* x_1; 
x_1 = l_Float_HasPow___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Float(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_floatSpec___closed__1 = _init_l_floatSpec___closed__1();
lean_mark_persistent(l_floatSpec___closed__1);
l_floatSpec___closed__2 = _init_l_floatSpec___closed__2();
lean_mark_persistent(l_floatSpec___closed__2);
l_floatSpec = _init_l_floatSpec();
lean_mark_persistent(l_floatSpec);
l_Float_Inhabited___closed__1 = _init_l_Float_Inhabited___closed__1();
lean_mark_persistent(l_Float_Inhabited___closed__1);
l_Float_Inhabited = _init_l_Float_Inhabited();
lean_mark_persistent(l_Float_Inhabited);
l_Float_HasZero___closed__1 = _init_l_Float_HasZero___closed__1();
l_Float_HasZero = _init_l_Float_HasZero();
l_Float_HasOne___closed__1 = _init_l_Float_HasOne___closed__1();
l_Float_HasOne = _init_l_Float_HasOne();
l_Float_HasOfNat___closed__1 = _init_l_Float_HasOfNat___closed__1();
lean_mark_persistent(l_Float_HasOfNat___closed__1);
l_Float_HasOfNat = _init_l_Float_HasOfNat();
lean_mark_persistent(l_Float_HasOfNat);
l_Float_HasAdd___closed__1 = _init_l_Float_HasAdd___closed__1();
lean_mark_persistent(l_Float_HasAdd___closed__1);
l_Float_HasAdd = _init_l_Float_HasAdd();
lean_mark_persistent(l_Float_HasAdd);
l_Float_HasSub___closed__1 = _init_l_Float_HasSub___closed__1();
lean_mark_persistent(l_Float_HasSub___closed__1);
l_Float_HasSub = _init_l_Float_HasSub();
lean_mark_persistent(l_Float_HasSub);
l_Float_HasMul___closed__1 = _init_l_Float_HasMul___closed__1();
lean_mark_persistent(l_Float_HasMul___closed__1);
l_Float_HasMul = _init_l_Float_HasMul();
lean_mark_persistent(l_Float_HasMul);
l_Float_HasDiv___closed__1 = _init_l_Float_HasDiv___closed__1();
lean_mark_persistent(l_Float_HasDiv___closed__1);
l_Float_HasDiv = _init_l_Float_HasDiv();
lean_mark_persistent(l_Float_HasDiv);
l_Float_HasLess = _init_l_Float_HasLess();
lean_mark_persistent(l_Float_HasLess);
l_Float_HasLessEq = _init_l_Float_HasLessEq();
lean_mark_persistent(l_Float_HasLessEq);
l_Float_HasBeq___closed__1 = _init_l_Float_HasBeq___closed__1();
lean_mark_persistent(l_Float_HasBeq___closed__1);
l_Float_HasBeq = _init_l_Float_HasBeq();
lean_mark_persistent(l_Float_HasBeq);
l_Float_HasToString___closed__1 = _init_l_Float_HasToString___closed__1();
lean_mark_persistent(l_Float_HasToString___closed__1);
l_Float_HasToString = _init_l_Float_HasToString();
lean_mark_persistent(l_Float_HasToString);
l_Float_HasPow___closed__1 = _init_l_Float_HasPow___closed__1();
lean_mark_persistent(l_Float_HasPow___closed__1);
l_Float_HasPow = _init_l_Float_HasPow();
lean_mark_persistent(l_Float_HasPow);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
