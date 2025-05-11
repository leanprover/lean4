// Lean compiler output
// Module: Init.Data.Fin.Lemmas
// Imports: Init.Data.Fin.Basic Init.Data.Nat.Lemmas Init.Data.Int.DivMod.Lemmas Init.Ext Init.ByCases Init.Conv Init.Omega
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
LEAN_EXPORT lean_object* l_Fin_reverseInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instIntCastOfNeZeroNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_inductionOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_ofNat_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_intCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instNatCastOfNeZeroNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_intCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRecOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Fin_intCast___closed__1;
LEAN_EXPORT lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRec___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRec(lean_object*);
LEAN_EXPORT lean_object* l_Fin_addCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instNatCastOfNeZeroNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_ofNat_x27___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Fin_intCast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_intCast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Fin_intCast___closed__1;
x_5 = lean_int_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_nat_abs(x_3);
x_7 = lean_nat_mod(x_6, x_1);
lean_dec(x_6);
x_8 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
x_9 = lean_nat_mod(x_8, x_1);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_abs(x_3);
x_11 = lean_nat_mod(x_10, x_1);
lean_dec(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Fin_intCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_intCast(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_instIntCastOfNeZeroNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_intCast___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_succRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_nat_dec_eq(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_nat_sub(x_4, x_6);
lean_inc(x_2);
x_10 = l_Fin_succRec___rarg(x_1, x_2, x_7, x_9);
x_11 = lean_apply_3(x_2, x_7, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_apply_1(x_1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Fin_succRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_succRec___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_succRec___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Fin_succRec___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_succRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_succRec___rarg(x_4, x_5, x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_succRecOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_succRecOn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_induction_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
lean_inc(x_4);
x_11 = l_Fin_induction_go(x_1, lean_box(0), x_3, x_4, x_10, lean_box(0));
x_12 = lean_apply_2(x_4, x_10, x_11);
return x_12;
}
else
{
lean_dec(x_4);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Fin_induction_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_induction_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_induction_go(x_1, lean_box(0), x_3, x_4, x_5, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_induction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_induction(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_inductionOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_induction_go(x_1, lean_box(0), x_4, x_5, x_2, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_inductionOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_inductionOn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Fin_cases___lambda__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l_Fin_induction_go(x_1, lean_box(0), x_3, x_6, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_cases(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_5, x_7);
lean_inc(x_4);
x_9 = l_Fin_reverseInduction(x_1, lean_box(0), x_3, x_4, x_8);
x_10 = lean_apply_2(x_4, x_5, x_9);
return x_10;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_reverseInduction(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Fin_cases___lambda__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l_Fin_reverseInduction(x_1, lean_box(0), x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_lastCases(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_addCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_nat_sub(x_6, x_1);
lean_dec(x_6);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_apply_1(x_4, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Fin_addCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_addCases(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Init_ByCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Conv(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Conv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Fin_intCast___closed__1 = _init_l_Fin_intCast___closed__1();
lean_mark_persistent(l_Fin_intCast___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
