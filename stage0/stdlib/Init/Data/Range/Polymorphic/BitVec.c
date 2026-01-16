// Lean compiler output
// Module: Init.Data.Range.Polymorphic.BitVec
// Imports: public import Init.Data.Range.Polymorphic.Instances public import Init.Data.Order.Lemmas public import Init.Data.UInt import Init.Omega
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
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_BitVec_instRxcHasSize___closed__0;
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_BitVec_instRxoHasSize___closed__0;
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_BitVec_ofNat(x_1, x_3);
x_5 = l_BitVec_add(x_1, x_2, x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_BitVec_ofNat(x_1, x_6);
x_8 = lean_nat_dec_eq(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_instUpwardEnumerable___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_nat_add(x_3, x_2);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_pow(x_5, x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_instUpwardEnumerable___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_BitVec_instUpwardEnumerable___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_BitVec_instUpwardEnumerable___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_sub(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_instRxcHasSize___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_BitVec_instRxcHasSize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_instRxcHasSize___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instRxcHasSize___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instRxcHasSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_sub(x_4, x_1);
lean_dec(x_4);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_instRxoHasSize___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_BitVec_instRxoHasSize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_instRxoHasSize___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instRxoHasSize___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instRxoHasSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_pow(x_3, x_1);
x_5 = lean_nat_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_instRxiHasSize___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_instRxiHasSize___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_BitVec_instRxcHasSize___closed__0 = _init_l_BitVec_instRxcHasSize___closed__0();
lean_mark_persistent(l_BitVec_instRxcHasSize___closed__0);
l_BitVec_instRxoHasSize___closed__0 = _init_l_BitVec_instRxoHasSize___closed__0();
lean_mark_persistent(l_BitVec_instRxoHasSize___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
