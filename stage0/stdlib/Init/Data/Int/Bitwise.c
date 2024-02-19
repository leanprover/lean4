// Lean compiler output
// Module: Init.Data.Int.Bitwise
// Imports: Init.Data.Int.Basic Init.Data.Nat.Bitwise
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
LEAN_EXPORT lean_object* l_Int_instComplementInt;
LEAN_EXPORT lean_object* l_Int_not(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_instHShiftRightIntNat;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Int_instComplementInt___closed__1;
static lean_object* l_Int_not___closed__1;
static lean_object* l_Int_instHShiftRightIntNat___closed__1;
LEAN_EXPORT lean_object* l_Int_shiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_shiftRight(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Int_not___boxed(lean_object*);
static lean_object* _init_l_Int_not___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_not(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_not___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = lean_int_neg_succ_of_nat(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_to_int(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Int_not___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_not(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instComplementInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_not___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instComplementInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instComplementInt___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_shiftRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_not___closed__1;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_nat_shiftr(x_5, x_2);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_nat_shiftr(x_10, x_2);
lean_dec(x_10);
x_12 = lean_int_neg_succ_of_nat(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Int_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_shiftRight(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instHShiftRightIntNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instHShiftRightIntNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instHShiftRightIntNat___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Bitwise(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Bitwise(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_not___closed__1 = _init_l_Int_not___closed__1();
lean_mark_persistent(l_Int_not___closed__1);
l_Int_instComplementInt___closed__1 = _init_l_Int_instComplementInt___closed__1();
lean_mark_persistent(l_Int_instComplementInt___closed__1);
l_Int_instComplementInt = _init_l_Int_instComplementInt();
lean_mark_persistent(l_Int_instComplementInt);
l_Int_instHShiftRightIntNat___closed__1 = _init_l_Int_instHShiftRightIntNat___closed__1();
lean_mark_persistent(l_Int_instHShiftRightIntNat___closed__1);
l_Int_instHShiftRightIntNat = _init_l_Int_instHShiftRightIntNat();
lean_mark_persistent(l_Int_instHShiftRightIntNat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
