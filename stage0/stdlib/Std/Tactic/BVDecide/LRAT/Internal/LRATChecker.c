// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.LRATChecker
// Imports: Std.Tactic.BVDecide.LRAT.Actions Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___closed__1;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__3;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(x_1);
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("success", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("out of proof", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rup failure", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__3;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_3(x_10, x_5, x_11, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 2;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_4, 4);
lean_inc(x_20);
x_21 = lean_apply_3(x_20, x_5, x_18, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
x_24 = 2;
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_5 = x_25;
x_6 = x_17;
goto _start;
}
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 4);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
x_33 = lean_apply_5(x_32, x_5, x_28, x_29, x_30, x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_2);
x_36 = 2;
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_5 = x_37;
x_6 = x_27;
goto _start;
}
}
default: 
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_ctor_get(x_4, 3);
lean_inc(x_41);
x_42 = lean_apply_2(x_41, x_5, x_40);
x_5 = x_42;
x_6 = x_39;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_Result_noConfusion___rarg___closed__1);
l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult();
l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__1);
l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__2);
l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
