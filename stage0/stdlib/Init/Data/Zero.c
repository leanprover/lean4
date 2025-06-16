// Lean compiler output
// Module: Init.Data.Zero
// Imports: Init.Core
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
LEAN_EXPORT lean_object* l_npowRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Zero_ofOfNat0(lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg(lean_object*);
LEAN_EXPORT lean_object* l_nsmulRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_npowRec(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_npowRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_nsmulRec(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0(lean_object*);
LEAN_EXPORT lean_object* l_nsmulRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1(lean_object*);
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Zero_toOfNat0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Zero_toOfNat0___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Zero_toOfNat0___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Zero_ofOfNat0___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Zero_ofOfNat0___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_One_toOfNat1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_One_toOfNat1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_One_ofOfNat1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_One_ofOfNat1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_npowRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_inc(x_4);
lean_inc(x_2);
x_9 = l_npowRec___rarg(x_1, x_2, x_8, x_4);
lean_dec(x_8);
x_10 = lean_apply_2(x_2, x_9, x_4);
return x_10;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_npowRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_npowRec___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_npowRec___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_npowRec___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_nsmulRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_inc(x_4);
lean_inc(x_2);
x_9 = l_nsmulRec___rarg(x_1, x_2, x_8, x_4);
lean_dec(x_8);
x_10 = lean_apply_2(x_2, x_9, x_4);
return x_10;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_nsmulRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_nsmulRec___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_nsmulRec___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_nsmulRec___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Zero(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
