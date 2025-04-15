// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.CachedGatesLemmas Std.Sat.AIG.LawfulVecOperator Std.Sat.AIG.If
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Bool_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Bool_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__2;
x_3 = lean_nat_lor(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_nat_sub(x_7, x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_7, x_14);
lean_dec(x_7);
x_16 = lean_array_fget(x_5, x_13);
lean_dec(x_13);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_div(x_16, x_17);
x_19 = lean_nat_land(x_14, x_16);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_nat_mul(x_18, x_17);
lean_dec(x_18);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__1;
x_24 = lean_nat_lor(x_22, x_23);
lean_dec(x_22);
x_25 = lean_array_push(x_9, x_24);
x_7 = x_15;
x_8 = lean_box(0);
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_nat_mul(x_18, x_17);
lean_dec(x_18);
x_28 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__2;
x_29 = lean_nat_lor(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_push(x_9, x_29);
x_7 = x_15;
x_8 = lean_box(0);
x_9 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_7, x_32);
lean_dec(x_7);
x_34 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__3;
x_35 = lean_array_push(x_9, x_34);
x_7 = x_33;
x_8 = lean_box(0);
x_9 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_mk_empty_array_with_capacity(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg(x_1, x_2, x_3, x_4, x_6, x_7, x_9, lean_box(0), x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_nat_dec_lt(x_9, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_pow(x_12, x_9);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg(x_1, x_2, x_3, x_4, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_fget(x_8, x_9);
x_19 = lean_nat_div(x_18, x_12);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_land(x_20, x_18);
lean_dec(x_18);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 1;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
lean_inc(x_7);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_7);
x_27 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_16, x_26);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_7);
x_31 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_16, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
x_11 = lean_nat_dec_lt(x_7, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_6);
lean_inc(x_4);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_13);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg(x_1, x_2, x_3, x_5, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_5 = x_16;
x_7 = x_13;
x_8 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_8);
lean_inc(x_6);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___rarg(x_1, x_2, x_3, x_4, x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___rarg(x_1, x_2, x_3, x_6, x_13, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_If(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__1);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__2 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__2);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__3 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
