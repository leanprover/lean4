// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Nat
// Imports: Init.Data.Nat.Lemmas Init.Data.Range.Polymorphic.Basic
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
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Std_PRange_instLeast_x3fNat___closed__0;
static lean_object* l_Std_PRange_instLeast_x3fNat___closed__1;
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instLeast_x3fNat;
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedNat;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenNat;
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_add(x_2, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_PRange_instUpwardEnumerableNat() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PRange_instUpwardEnumerableNat___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instUpwardEnumerableNat___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PRange_instLeast_x3fNat___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_instLeast_x3fNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_instLeast_x3fNat___closed__0;
x_2 = l_Std_PRange_instUpwardEnumerableNat;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PRange_instLeast_x3fNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PRange_instLeast_x3fNat___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Range_Polymorphic_Nat_0__Std_PRange_rangeRev_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Std_PRange_instRangeSizeClosedNat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PRange_instRangeSizeClosedNat___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instRangeSizeClosedNat___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_PRange_instRangeSizeOpenNat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PRange_instRangeSizeOpenNat___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instRangeSizeOpenNat___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_PRange_instUpwardEnumerableNat = _init_l_Std_PRange_instUpwardEnumerableNat();
lean_mark_persistent(l_Std_PRange_instUpwardEnumerableNat);
l_Std_PRange_instLeast_x3fNat___closed__0 = _init_l_Std_PRange_instLeast_x3fNat___closed__0();
lean_mark_persistent(l_Std_PRange_instLeast_x3fNat___closed__0);
l_Std_PRange_instLeast_x3fNat___closed__1 = _init_l_Std_PRange_instLeast_x3fNat___closed__1();
lean_mark_persistent(l_Std_PRange_instLeast_x3fNat___closed__1);
l_Std_PRange_instLeast_x3fNat = _init_l_Std_PRange_instLeast_x3fNat();
lean_mark_persistent(l_Std_PRange_instLeast_x3fNat);
l_Std_PRange_instRangeSizeClosedNat = _init_l_Std_PRange_instRangeSizeClosedNat();
lean_mark_persistent(l_Std_PRange_instRangeSizeClosedNat);
l_Std_PRange_instRangeSizeOpenNat = _init_l_Std_PRange_instRangeSizeOpenNat();
lean_mark_persistent(l_Std_PRange_instRangeSizeOpenNat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
