// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Int
// Imports: Init.Data.Range.Polymorphic.Instances Init.Data.Order.Classes Init.Omega
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
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenInt;
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt;
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instNatCastInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedInt;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenInt___lam__0(lean_object*, lean_object*);
static lean_object* _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0;
x_3 = lean_int_add(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_instNatCastInt___lam__0(x_1);
x_4 = lean_int_add(x_2, x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_PRange_instUpwardEnumerableInt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PRange_instUpwardEnumerableInt___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instUpwardEnumerableInt___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0;
x_4 = lean_int_add(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
x_6 = l_Int_toNat(x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Std_PRange_instRangeSizeClosedInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PRange_instRangeSizeClosedInt___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeClosedInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instRangeSizeClosedInt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0;
x_5 = lean_int_add(x_1, x_4);
x_6 = lean_int_sub(x_5, x_2);
lean_dec(x_5);
x_7 = l_Int_toNat(x_6);
lean_dec(x_6);
x_8 = lean_nat_sub(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Std_PRange_instRangeSizeOpenInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PRange_instRangeSizeOpenInt___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instRangeSizeOpenInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instRangeSizeOpenInt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Int(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0 = _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0();
lean_mark_persistent(l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0);
l_Std_PRange_instUpwardEnumerableInt = _init_l_Std_PRange_instUpwardEnumerableInt();
lean_mark_persistent(l_Std_PRange_instUpwardEnumerableInt);
l_Std_PRange_instRangeSizeClosedInt = _init_l_Std_PRange_instRangeSizeClosedInt();
lean_mark_persistent(l_Std_PRange_instRangeSizeClosedInt);
l_Std_PRange_instRangeSizeOpenInt = _init_l_Std_PRange_instRangeSizeOpenInt();
lean_mark_persistent(l_Std_PRange_instRangeSizeOpenInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
