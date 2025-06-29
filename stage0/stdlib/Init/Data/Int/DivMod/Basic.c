// Lean compiler output
// Module: Init.Data.Int.DivMod.Basic
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
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Int_bmod_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Int_instDiv;
static lean_object* l_Int_bmod___closed__1;
LEAN_EXPORT lean_object* l_Int_divExact___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_instMod___closed__0;
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
lean_object* lean_int_div_exact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fdiv(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_tmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fdiv___boxed(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
static lean_object* l_Int_fdiv___closed__0;
LEAN_EXPORT lean_object* l_Int_tdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
static lean_object* l_Int_instDiv___closed__0;
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_instMod;
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bdiv(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
static lean_object* l_Int_bmod___closed__0;
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_ediv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_emod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instDiv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_ediv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instDiv___closed__0;
return x_1;
}
}
static lean_object* _init_l_Int_instMod___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_emod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instMod() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instMod___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_divExact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_int_div_exact(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_tdiv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_div(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_tmod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_fdiv___closed__0() {
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
lean_object* x_3; lean_object* x_4; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Int_fdiv___closed__0;
x_12 = lean_int_dec_lt(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_nat_abs(x_1);
x_14 = lean_nat_dec_eq(x_13, x_10);
if (x_14 == 1)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_int_dec_lt(x_2, x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_nat_abs(x_2);
x_17 = lean_nat_div(x_13, x_16);
lean_dec(x_16);
lean_dec(x_13);
x_18 = lean_nat_to_int(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_13, x_19);
lean_dec(x_13);
x_21 = lean_nat_abs(x_2);
x_22 = lean_nat_sub(x_21, x_19);
lean_dec(x_21);
x_3 = x_20;
x_4 = x_22;
goto block_9;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_nat_abs(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = lean_int_dec_lt(x_2, x_11);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_nat_abs(x_2);
x_28 = lean_nat_dec_eq(x_27, x_10);
if (x_28 == 1)
{
lean_dec(x_27);
lean_dec(x_25);
return x_11;
}
else
{
lean_object* x_29; 
x_29 = lean_nat_sub(x_27, x_24);
lean_dec(x_27);
x_3 = x_25;
x_4 = x_29;
goto block_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_nat_abs(x_2);
x_31 = lean_nat_sub(x_30, x_24);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_25, x_32);
lean_dec(x_25);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_31, x_34);
lean_dec(x_31);
x_36 = lean_nat_div(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
x_37 = lean_nat_to_int(x_36);
return x_37;
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_nat_div(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_int_neg_succ_of_nat(x_7);
return x_8;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Int_fdiv___closed__0;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_nat_dec_eq(x_6, x_3);
if (x_7 == 1)
{
lean_dec(x_6);
return x_4;
}
else
{
uint8_t x_8; 
x_8 = lean_int_dec_lt(x_2, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_nat_abs(x_2);
x_10 = lean_nat_mod(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_nat_to_int(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_nat_abs(x_2);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_15, x_16);
x_18 = lean_nat_mod(x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
x_19 = l_Int_subNatNat(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_nat_abs(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_int_dec_lt(x_2, x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_nat_abs(x_2);
x_25 = lean_nat_mod(x_22, x_24);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = l_Int_subNatNat(x_24, x_27);
lean_dec(x_27);
lean_dec(x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_nat_abs(x_2);
x_30 = lean_nat_sub(x_29, x_21);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_30, x_33);
lean_dec(x_30);
x_35 = lean_nat_mod(x_32, x_34);
lean_dec(x_34);
lean_dec(x_32);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_int_neg(x_36);
lean_dec(x_36);
return x_37;
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
static lean_object* _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0;
x_11 = lean_int_dec_lt(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_nat_abs(x_1);
x_13 = lean_nat_dec_eq(x_12, x_9);
if (x_13 == 1)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_apply_1(x_3, x_2);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
x_15 = lean_int_dec_lt(x_2, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_nat_abs(x_2);
lean_dec(x_2);
x_17 = lean_apply_3(x_4, x_12, x_16, lean_box(0));
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_12, x_18);
lean_dec(x_12);
x_20 = lean_nat_abs(x_2);
lean_dec(x_2);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_20);
x_22 = lean_apply_2(x_5, x_19, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_nat_abs(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = lean_int_dec_lt(x_2, x_10);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_8);
x_27 = lean_nat_abs(x_2);
lean_dec(x_2);
x_28 = lean_nat_dec_eq(x_27, x_9);
if (x_28 == 1)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_7);
x_29 = lean_apply_1(x_6, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_30 = lean_nat_sub(x_27, x_24);
lean_dec(x_27);
x_31 = lean_apply_2(x_7, x_25, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_nat_abs(x_2);
lean_dec(x_2);
x_33 = lean_nat_sub(x_32, x_24);
lean_dec(x_32);
x_34 = lean_apply_2(x_8, x_25, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Int_bmod_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_bmod___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_bmod___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_bmod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_nat_to_int(x_2);
x_4 = lean_int_emod(x_1, x_3);
x_5 = l_Int_bmod___closed__0;
x_6 = lean_int_add(x_3, x_5);
x_7 = l_Int_bmod___closed__1;
x_8 = lean_int_ediv(x_6, x_7);
lean_dec(x_6);
x_9 = lean_int_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_int_sub(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
return x_10;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_bmod(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_bdiv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_nat_to_int(x_2);
x_6 = lean_int_ediv(x_1, x_5);
x_7 = lean_int_emod(x_1, x_5);
x_8 = l_Int_bmod___closed__0;
x_9 = lean_int_add(x_5, x_8);
lean_dec(x_5);
x_10 = l_Int_bmod___closed__1;
x_11 = lean_int_ediv(x_9, x_10);
lean_dec(x_9);
x_12 = lean_int_dec_lt(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_int_add(x_6, x_8);
lean_dec(x_6);
return x_13;
}
else
{
return x_6;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Int_fdiv___closed__0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Int_bdiv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_bdiv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_instDiv___closed__0 = _init_l_Int_instDiv___closed__0();
lean_mark_persistent(l_Int_instDiv___closed__0);
l_Int_instDiv = _init_l_Int_instDiv();
lean_mark_persistent(l_Int_instDiv);
l_Int_instMod___closed__0 = _init_l_Int_instMod___closed__0();
lean_mark_persistent(l_Int_instMod___closed__0);
l_Int_instMod = _init_l_Int_instMod();
lean_mark_persistent(l_Int_instMod);
l_Int_fdiv___closed__0 = _init_l_Int_fdiv___closed__0();
lean_mark_persistent(l_Int_fdiv___closed__0);
l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0 = _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
l_Int_bmod___closed__0 = _init_l_Int_bmod___closed__0();
lean_mark_persistent(l_Int_bmod___closed__0);
l_Int_bmod___closed__1 = _init_l_Int_bmod___closed__1();
lean_mark_persistent(l_Int_bmod___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
