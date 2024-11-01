// Lean compiler output
// Module: Init.Data.Nat.Bitwise.Basic
// Imports: Init.Data.Nat.Basic Init.Data.Nat.Div Init.Coe
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
LEAN_EXPORT lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instAndOp;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
static lean_object* l_Nat_instXor___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_bitwise___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_instShiftRight___closed__1;
static lean_object* l_Nat_instShiftLeft___closed__1;
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_bitwise(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_instOrOp___closed__1;
LEAN_EXPORT lean_object* l_Nat_instShiftRight;
LEAN_EXPORT lean_object* l_Nat_instXor;
LEAN_EXPORT lean_object* l_Nat_testBit___boxed(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_testBit(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_xor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instOrOp;
LEAN_EXPORT lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
static lean_object* l_Nat_instAndOp___closed__1;
LEAN_EXPORT lean_object* l_Nat_instShiftLeft;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_bitwise(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_div(x_2, x_7);
x_9 = lean_nat_div(x_3, x_7);
lean_inc(x_1);
x_10 = l_Nat_bitwise(x_1, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_nat_mod(x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_mod(x_3, x_7);
x_15 = lean_nat_dec_eq(x_14, x_12);
lean_dec(x_14);
x_16 = lean_box(x_13);
x_17 = lean_box(x_15);
x_18 = lean_apply_2(x_1, x_16, x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_nat_add(x_10, x_10);
lean_dec(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_nat_add(x_10, x_10);
lean_dec(x_10);
x_22 = lean_nat_add(x_21, x_12);
lean_dec(x_21);
return x_22;
}
}
else
{
uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = 1;
x_24 = 0;
x_25 = lean_box(x_23);
x_26 = lean_box(x_24);
x_27 = lean_apply_2(x_1, x_25, x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_unsigned_to_nat(0u);
return x_29;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
else
{
uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = 0;
x_31 = 1;
x_32 = lean_box(x_30);
x_33 = lean_box(x_31);
x_34 = lean_apply_2(x_1, x_32, x_33);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_unsigned_to_nat(0u);
return x_36;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_bitwise___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_bitwise(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_land(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_lor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_lxor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_shiftl(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_shiftr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_instAndOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instAndOp() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instAndOp___closed__1;
return x_1;
}
}
static lean_object* _init_l_Nat_instOrOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instOrOp() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instOrOp___closed__1;
return x_1;
}
}
static lean_object* _init_l_Nat_instXor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instXor() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instXor___closed__1;
return x_1;
}
}
static lean_object* _init_l_Nat_instShiftLeft___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instShiftLeft() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instShiftLeft___closed__1;
return x_1;
}
}
static lean_object* _init_l_Nat_instShiftRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instShiftRight() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instShiftRight___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Nat_testBit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_nat_shiftr(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_land(x_4, x_3);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Nat_testBit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_testBit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Div(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Coe(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Coe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_instAndOp___closed__1 = _init_l_Nat_instAndOp___closed__1();
lean_mark_persistent(l_Nat_instAndOp___closed__1);
l_Nat_instAndOp = _init_l_Nat_instAndOp();
lean_mark_persistent(l_Nat_instAndOp);
l_Nat_instOrOp___closed__1 = _init_l_Nat_instOrOp___closed__1();
lean_mark_persistent(l_Nat_instOrOp___closed__1);
l_Nat_instOrOp = _init_l_Nat_instOrOp();
lean_mark_persistent(l_Nat_instOrOp);
l_Nat_instXor___closed__1 = _init_l_Nat_instXor___closed__1();
lean_mark_persistent(l_Nat_instXor___closed__1);
l_Nat_instXor = _init_l_Nat_instXor();
lean_mark_persistent(l_Nat_instXor);
l_Nat_instShiftLeft___closed__1 = _init_l_Nat_instShiftLeft___closed__1();
lean_mark_persistent(l_Nat_instShiftLeft___closed__1);
l_Nat_instShiftLeft = _init_l_Nat_instShiftLeft();
lean_mark_persistent(l_Nat_instShiftLeft);
l_Nat_instShiftRight___closed__1 = _init_l_Nat_instShiftRight___closed__1();
lean_mark_persistent(l_Nat_instShiftRight___closed__1);
l_Nat_instShiftRight = _init_l_Nat_instShiftRight();
lean_mark_persistent(l_Nat_instShiftRight);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
