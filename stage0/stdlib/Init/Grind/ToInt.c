// Lean compiler output
// Module: Init.Grind.ToInt
// Imports: Init.Data.Int.DivMod.Lemmas
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
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint___boxed(lean_object*);
static lean_object* l_Lean_Grind_IntInterval_wrap___closed__0;
static lean_object* l_Lean_Grind_IntInterval_uint___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_instMembershipInt;
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_hi_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_IntInterval_uint___closed__1;
LEAN_EXPORT uint8_t l_Lean_Grind_instDecidableEqIntInterval(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_nonEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_isFinite___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_lo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_isFinite(lean_object*);
static lean_object* l_Lean_Grind_instBEqIntInterval___closed__0;
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_nonEmpty(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_beqIntInterval____x40_Init_Grind_ToInt___hyg_55_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_decEqIntInterval____x40_Init_Grind_ToInt___hyg_188____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_decEqIntInterval____x40_Init_Grind_ToInt___hyg_188_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_beqIntInterval____x40_Init_Grind_ToInt___hyg_55____boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqIntInterval;
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instDecidableEqIntInterval___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_beqIntInterval____x40_Init_Grind_ToInt___hyg_55_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_int_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_int_dec_eq(x_4, x_6);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_int_dec_eq(x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_int_dec_eq(x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_beqIntInterval____x40_Init_Grind_ToInt___hyg_55____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_beqIntInterval____x40_Init_Grind_ToInt___hyg_55_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_instBEqIntInterval___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_beqIntInterval____x40_Init_Grind_ToInt___hyg_55____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instBEqIntInterval() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instBEqIntInterval___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_decEqIntInterval____x40_Init_Grind_ToInt___hyg_188_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_box(1);
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_int_dec_eq(x_5, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_unbox(x_3);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_int_dec_eq(x_6, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_unbox(x_3);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_4);
return x_13;
}
}
}
else
{
uint8_t x_14; 
x_14 = lean_unbox(x_3);
return x_14;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_int_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_unbox(x_3);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_unbox(x_4);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = lean_unbox(x_3);
return x_20;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_int_dec_eq(x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_unbox(x_3);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_unbox(x_4);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = lean_unbox(x_3);
return x_26;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_27; 
x_27 = lean_unbox(x_4);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_unbox(x_3);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_decEqIntInterval____x40_Init_Grind_ToInt___hyg_188____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_decEqIntInterval____x40_Init_Grind_ToInt___hyg_188_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instDecidableEqIntInterval(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Grind_decEqIntInterval____x40_Init_Grind_ToInt___hyg_188_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instDecidableEqIntInterval___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_instDecidableEqIntInterval(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_IntInterval_uint___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_IntInterval_uint___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Grind_IntInterval_uint___closed__0;
x_3 = l_Lean_Grind_IntInterval_uint___closed__1;
x_4 = l_Int_pow(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_uint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_IntInterval_uint(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Grind_IntInterval_uint___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_1, x_3);
x_5 = l_Int_pow(x_2, x_4);
lean_dec(x_4);
x_6 = lean_int_neg(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_sint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_IntInterval_sint(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_lo_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
default: 
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_hi_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 2:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
default: 
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_nonEmpty(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_int_dec_lt(x_2, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
default: 
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_nonEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_IntInterval_nonEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_5);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_IntInterval_isFinite(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
case 3:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
default: 
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_isFinite___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_IntInterval_isFinite(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_IntInterval_instMembershipInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_IntInterval_wrap___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_int_sub(x_2, x_3);
x_6 = lean_int_sub(x_4, x_3);
x_7 = lean_int_emod(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_int_add(x_7, x_3);
lean_dec(x_7);
return x_8;
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_int_dec_le(x_2, x_9);
if (x_10 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_9);
return x_9;
}
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Lean_Grind_IntInterval_wrap___closed__0;
x_13 = lean_int_sub(x_11, x_12);
x_14 = lean_int_dec_le(x_2, x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_dec(x_13);
lean_inc(x_2);
return x_2;
}
}
default: 
{
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntInterval_wrap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_IntInterval_wrap(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_ToInt(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instBEqIntInterval___closed__0 = _init_l_Lean_Grind_instBEqIntInterval___closed__0();
lean_mark_persistent(l_Lean_Grind_instBEqIntInterval___closed__0);
l_Lean_Grind_instBEqIntInterval = _init_l_Lean_Grind_instBEqIntInterval();
lean_mark_persistent(l_Lean_Grind_instBEqIntInterval);
l_Lean_Grind_IntInterval_uint___closed__0 = _init_l_Lean_Grind_IntInterval_uint___closed__0();
lean_mark_persistent(l_Lean_Grind_IntInterval_uint___closed__0);
l_Lean_Grind_IntInterval_uint___closed__1 = _init_l_Lean_Grind_IntInterval_uint___closed__1();
lean_mark_persistent(l_Lean_Grind_IntInterval_uint___closed__1);
l_Lean_Grind_IntInterval_instMembershipInt = _init_l_Lean_Grind_IntInterval_instMembershipInt();
lean_mark_persistent(l_Lean_Grind_IntInterval_instMembershipInt);
l_Lean_Grind_IntInterval_wrap___closed__0 = _init_l_Lean_Grind_IntInterval_wrap___closed__0();
lean_mark_persistent(l_Lean_Grind_IntInterval_wrap___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
