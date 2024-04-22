// Lean compiler output
// Module: Init.Data.Float
// Imports: Init.Core Init.Data.Int.Basic Init.Data.ToString.Basic
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
LEAN_EXPORT lean_object* l_Float_toUInt64___boxed(lean_object*);
uint8_t lean_float_isinf(double);
LEAN_EXPORT lean_object* l_instBEqFloat;
double exp2(double);
double lean_float_scaleb(double, lean_object*);
double exp(double);
LEAN_EXPORT uint8_t l_floatSpec___elambda__1(lean_object*, lean_object*);
double lean_float_mul(double, double);
LEAN_EXPORT lean_object* l_Float_isFinite___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instDivFloat;
LEAN_EXPORT lean_object* l_Float_sqrt___boxed(lean_object*);
double lean_float_div(double, double);
extern uint8_t l_instDecidableTrue;
LEAN_EXPORT lean_object* l_Float_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_frExp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_floatDecLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instLEFloat;
LEAN_EXPORT lean_object* l_Float_round___boxed(lean_object*);
double ceil(double);
LEAN_EXPORT lean_object* l_Float_floor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_toUInt16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_toUInt32___boxed(lean_object*);
static lean_object* l_instInhabitedFloat___closed__1;
LEAN_EXPORT lean_object* l_Float_tanh___boxed(lean_object*);
double acos(double);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Float_add___boxed(lean_object*, lean_object*);
size_t lean_float_to_usize(double);
double cos(double);
LEAN_EXPORT lean_object* l_Float_acosh___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_atan2___boxed(lean_object*, lean_object*);
LEAN_EXPORT double l_instMinFloat(double, double);
double lean_float_negate(double);
LEAN_EXPORT lean_object* l_Float_sub___boxed(lean_object*, lean_object*);
uint8_t lean_float_to_uint8(double);
double sin(double);
LEAN_EXPORT lean_object* l_instMulFloat;
double atanh(double);
double sinh(double);
double sqrt(double);
static lean_object* l_instBEqFloat___closed__1;
LEAN_EXPORT lean_object* l_Float_sinh___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_cosh___boxed(lean_object*);
double lean_float_add(double, double);
static lean_object* l_instMulFloat___closed__1;
static lean_object* l_instSubFloat___closed__1;
LEAN_EXPORT lean_object* l_instInhabitedFloat;
double atan(double);
LEAN_EXPORT lean_object* l_Float_log___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMaxFloat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_isInf___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_atan___boxed(lean_object*);
double cbrt(double);
double lean_uint64_to_float(uint64_t);
LEAN_EXPORT lean_object* l_Float_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint8_t l_floatDecLt(double, double);
LEAN_EXPORT lean_object* l_Float_isNaN___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_cos___boxed(lean_object*);
lean_object* lean_float_frexp(double);
double log(double);
LEAN_EXPORT lean_object* l_Float_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_floatSpec;
LEAN_EXPORT lean_object* l_Float_abs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instLTFloat;
double asinh(double);
double pow(double, double);
double atan2(double, double);
LEAN_EXPORT lean_object* l_instMinFloat___boxed(lean_object*, lean_object*);
static lean_object* l_instToStringFloat___closed__1;
LEAN_EXPORT lean_object* l_instReprFloat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_toFloat___boxed(lean_object*);
uint8_t lean_float_isnan(double);
double tanh(double);
double tan(double);
LEAN_EXPORT lean_object* l_Float_neg___boxed(lean_object*);
LEAN_EXPORT double l_instMaxFloat(double, double);
LEAN_EXPORT lean_object* l_Float_asinh___boxed(lean_object*);
LEAN_EXPORT lean_object* l_floatSpec___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_atanh___boxed(lean_object*);
static lean_object* l_instNegFloat___closed__1;
static lean_object* l_floatSpec___closed__1;
LEAN_EXPORT lean_object* l_Float_scaleB___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringFloat;
LEAN_EXPORT lean_object* l_Float_div___boxed(lean_object*, lean_object*);
uint16_t lean_float_to_uint16(double);
uint32_t lean_float_to_uint32(double);
LEAN_EXPORT lean_object* l_instReprAtomFloat;
LEAN_EXPORT lean_object* l_Float_cbrt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_floatDecLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instNegFloat;
double acosh(double);
double log2(double);
LEAN_EXPORT uint8_t l_floatDecLe(double, double);
double cosh(double);
LEAN_EXPORT lean_object* l_instAddFloat;
LEAN_EXPORT lean_object* l_Float_ceil___boxed(lean_object*);
lean_object* lean_float_to_string(double);
static lean_object* l_floatSpec___closed__2;
double asin(double);
static lean_object* l_instDivFloat___closed__1;
uint8_t lean_float_beq(double, double);
static lean_object* l_instAddFloat___closed__1;
LEAN_EXPORT lean_object* l_Float_exp2___boxed(lean_object*);
uint8_t lean_float_decLe(double, double);
uint64_t lean_float_to_uint64(double);
LEAN_EXPORT lean_object* l_Float_acos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_toUSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_exp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_mul___boxed(lean_object*, lean_object*);
double log10(double);
double floor(double);
double round(double);
LEAN_EXPORT lean_object* l_instReprFloat(double, lean_object*);
LEAN_EXPORT lean_object* l_Float_asin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_pow___boxed(lean_object*, lean_object*);
double fabs(double);
LEAN_EXPORT lean_object* l_Float_tan___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instHomogeneousPowFloat;
LEAN_EXPORT lean_object* l_Float_log2___boxed(lean_object*);
static lean_object* l_instHomogeneousPowFloat___closed__1;
LEAN_EXPORT lean_object* l_Float_sin___boxed(lean_object*);
uint8_t lean_float_isfinite(double);
LEAN_EXPORT lean_object* l_Float_log10___boxed(lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_instSubFloat;
LEAN_EXPORT uint8_t l_floatSpec___elambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_floatSpec___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Float_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = lean_float_add(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Float_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = lean_float_sub(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Float_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = lean_float_mul(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Float_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = lean_float_div(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Float_neg___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_negate(x_2);
x_4 = lean_box_float(x_3);
return x_4;
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
static lean_object* _init_l_instNegFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_neg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instNegFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instNegFloat___closed__1;
return x_1;
}
}
static lean_object* _init_l_instLTFloat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEFloat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Float_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = lean_float_beq(x_3, x_4);
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
LEAN_EXPORT lean_object* l_Float_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = lean_float_decLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Float_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = lean_float_decLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_floatDecLt(double x_1, double x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_float_decLt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_floatDecLt___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_floatDecLe(double x_1, double x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_float_decLe(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_floatDecLe___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Float_toString___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_string(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt8___boxed(lean_object* x_1) {
_start:
{
double x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_uint8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt16___boxed(lean_object* x_1) {
_start:
{
double x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_uint16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt32___boxed(lean_object* x_1) {
_start:
{
double x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_uint32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt64___boxed(lean_object* x_1) {
_start:
{
double x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_uint64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_toUSize___boxed(lean_object* x_1) {
_start:
{
double x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_to_usize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_isNaN___boxed(lean_object* x_1) {
_start:
{
double x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_isnan(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_isFinite___boxed(lean_object* x_1) {
_start:
{
double x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_isfinite(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_isInf___boxed(lean_object* x_1) {
_start:
{
double x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_isinf(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_frExp___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = lean_float_frexp(x_2);
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
LEAN_EXPORT lean_object* l_instReprFloat(double x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_float_to_string(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprFloat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; lean_object* x_4; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = l_instReprFloat(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprAtomFloat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFloat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_uint64_to_float(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_sin___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_cos___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_tan___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_asin___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_acos___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_atan___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_atan2___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Float_sinh___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_cosh___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_tanh___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_asinh___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_acosh___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_atanh___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_exp___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_exp2___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_log___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_log2___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_log10___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_pow___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Float_sqrt___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_cbrt___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Float_ceil___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = ceil(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_floor___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = floor(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_round___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = round(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Float_abs___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec(x_1);
x_3 = fabs(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
static lean_object* _init_l_instHomogeneousPowFloat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Float_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instHomogeneousPowFloat() {
_start:
{
lean_object* x_1; 
x_1 = l_instHomogeneousPowFloat___closed__1;
return x_1;
}
}
LEAN_EXPORT double l_instMinFloat(double x_1, double x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_float_decLe(x_1, x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_instMinFloat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = l_instMinFloat(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
LEAN_EXPORT double l_instMaxFloat(double x_1, double x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_float_decLe(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_instMaxFloat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; double x_5; lean_object* x_6; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox_float(x_2);
lean_dec(x_2);
x_5 = l_instMaxFloat(x_3, x_4);
x_6 = lean_box_float(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Float_scaleB___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; lean_object* x_5; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_float_scaleb(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_float(x_4);
return x_5;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
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
l_instNegFloat___closed__1 = _init_l_instNegFloat___closed__1();
lean_mark_persistent(l_instNegFloat___closed__1);
l_instNegFloat = _init_l_instNegFloat();
lean_mark_persistent(l_instNegFloat);
l_instLTFloat = _init_l_instLTFloat();
lean_mark_persistent(l_instLTFloat);
l_instLEFloat = _init_l_instLEFloat();
lean_mark_persistent(l_instLEFloat);
l_instBEqFloat___closed__1 = _init_l_instBEqFloat___closed__1();
lean_mark_persistent(l_instBEqFloat___closed__1);
l_instBEqFloat = _init_l_instBEqFloat();
lean_mark_persistent(l_instBEqFloat);
l_instToStringFloat___closed__1 = _init_l_instToStringFloat___closed__1();
lean_mark_persistent(l_instToStringFloat___closed__1);
l_instToStringFloat = _init_l_instToStringFloat();
lean_mark_persistent(l_instToStringFloat);
l_instReprAtomFloat = _init_l_instReprAtomFloat();
lean_mark_persistent(l_instReprAtomFloat);
l_instHomogeneousPowFloat___closed__1 = _init_l_instHomogeneousPowFloat___closed__1();
lean_mark_persistent(l_instHomogeneousPowFloat___closed__1);
l_instHomogeneousPowFloat = _init_l_instHomogeneousPowFloat();
lean_mark_persistent(l_instHomogeneousPowFloat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
