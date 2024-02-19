// Lean compiler output
// Module: Init.Data.Int.DivMod
// Imports: Init.Data.Int.Basic
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
static lean_object* l_Int_fdiv___closed__1;
LEAN_EXPORT lean_object* l_Int_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fdiv(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_div___boxed(lean_object*, lean_object*);
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_instDivInt;
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Int_instDivInt___closed__1;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Int_instModInt;
LEAN_EXPORT lean_object* l_Int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Int_instModInt___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_div(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_fdiv___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_fdiv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_fdiv___closed__1;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
x_10 = lean_int_dec_lt(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_11 = lean_nat_abs(x_2);
x_12 = lean_nat_div(x_5, x_11);
lean_dec(x_11);
lean_dec(x_5);
x_13 = lean_nat_to_int(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_14 = lean_nat_abs(x_2);
x_15 = lean_nat_sub(x_14, x_8);
lean_dec(x_14);
x_16 = lean_nat_add(x_15, x_8);
lean_dec(x_15);
x_17 = lean_nat_div(x_9, x_16);
lean_dec(x_16);
lean_dec(x_9);
x_18 = lean_int_neg_succ_of_nat(x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = l_Int_fdiv___closed__1;
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_nat_abs(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_int_dec_lt(x_2, x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_nat_abs(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_nat_sub(x_24, x_21);
lean_dec(x_24);
x_28 = lean_nat_add(x_27, x_21);
lean_dec(x_27);
x_29 = lean_nat_div(x_22, x_28);
lean_dec(x_28);
lean_dec(x_22);
x_30 = lean_int_neg_succ_of_nat(x_29);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_22);
x_31 = l_Int_fdiv___closed__1;
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_nat_abs(x_2);
x_33 = lean_nat_sub(x_32, x_21);
lean_dec(x_32);
x_34 = lean_nat_add(x_22, x_21);
lean_dec(x_22);
x_35 = lean_nat_add(x_33, x_21);
lean_dec(x_33);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_37 = lean_nat_to_int(x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_fdiv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_fdiv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_fmod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_fdiv___closed__1;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
x_10 = lean_int_dec_lt(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_11 = lean_nat_abs(x_2);
x_12 = lean_nat_mod(x_5, x_11);
lean_dec(x_11);
lean_dec(x_5);
x_13 = lean_nat_to_int(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_14 = lean_nat_abs(x_2);
x_15 = lean_nat_sub(x_14, x_8);
lean_dec(x_14);
x_16 = lean_nat_add(x_15, x_8);
x_17 = lean_nat_mod(x_9, x_16);
lean_dec(x_16);
lean_dec(x_9);
x_18 = l_Int_subNatNat(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = l_Int_fdiv___closed__1;
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_nat_abs(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_int_dec_lt(x_2, x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_nat_abs(x_2);
x_25 = lean_nat_mod(x_22, x_24);
lean_dec(x_22);
x_26 = lean_nat_add(x_25, x_21);
lean_dec(x_25);
x_27 = l_Int_subNatNat(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_nat_abs(x_2);
x_29 = lean_nat_sub(x_28, x_21);
lean_dec(x_28);
x_30 = lean_nat_add(x_22, x_21);
lean_dec(x_22);
x_31 = lean_nat_add(x_29, x_21);
lean_dec(x_29);
x_32 = lean_nat_mod(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_int_neg(x_33);
lean_dec(x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_fmod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_fmod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_ediv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_fdiv___closed__1;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_int_dec_lt(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_nat_abs(x_2);
x_8 = lean_nat_div(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
x_9 = lean_nat_to_int(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_nat_abs(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_nat_add(x_12, x_11);
lean_dec(x_12);
x_14 = lean_nat_div(x_5, x_13);
lean_dec(x_13);
lean_dec(x_5);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_nat_abs(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_int_dec_lt(x_2, x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_nat_abs(x_2);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_nat_sub(x_21, x_18);
lean_dec(x_21);
x_25 = lean_nat_add(x_24, x_18);
lean_dec(x_24);
x_26 = lean_nat_div(x_19, x_25);
lean_dec(x_25);
lean_dec(x_19);
x_27 = lean_int_neg_succ_of_nat(x_26);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_19);
x_28 = l_Int_fdiv___closed__1;
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_nat_abs(x_2);
x_30 = lean_nat_sub(x_29, x_18);
lean_dec(x_29);
x_31 = lean_nat_add(x_30, x_18);
lean_dec(x_30);
x_32 = lean_nat_div(x_19, x_31);
lean_dec(x_31);
lean_dec(x_19);
x_33 = lean_nat_add(x_32, x_18);
lean_dec(x_32);
x_34 = lean_nat_to_int(x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_ediv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_emod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Int_fdiv___closed__1;
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_nat_abs(x_2);
x_7 = lean_nat_mod(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_nat_to_int(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_nat_abs(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = lean_nat_abs(x_2);
x_13 = lean_nat_mod(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_add(x_13, x_10);
lean_dec(x_13);
x_15 = l_Int_subNatNat(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_emod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instDivInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_ediv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instDivInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instDivInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instModInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_emod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instModInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instModInt___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_fdiv___closed__1 = _init_l_Int_fdiv___closed__1();
lean_mark_persistent(l_Int_fdiv___closed__1);
l_Int_instDivInt___closed__1 = _init_l_Int_instDivInt___closed__1();
lean_mark_persistent(l_Int_instDivInt___closed__1);
l_Int_instDivInt = _init_l_Int_instDivInt();
lean_mark_persistent(l_Int_instDivInt);
l_Int_instModInt___closed__1 = _init_l_Int_instModInt___closed__1();
lean_mark_persistent(l_Int_instModInt___closed__1);
l_Int_instModInt = _init_l_Int_instModInt();
lean_mark_persistent(l_Int_instModInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
