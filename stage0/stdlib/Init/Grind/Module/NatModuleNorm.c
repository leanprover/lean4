// Lean compiler output
// Module: Init.Grind.Module.NatModuleNorm
// Imports: public import Init.Grind.Module.Envelope public import Init.Grind.Ordered.Linarith
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
static lean_object* l_Lean_Grind_Linarith_Expr_toPolyN___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__normN__cert___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0;
lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPolyN_spec__0(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__normN__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lean_RArray_getImpl___redArg(x_2, x_6);
lean_dec(x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_12 = l_Lean_Grind_Linarith_Expr_denoteN___redArg(x_1, x_2, x_10);
x_13 = l_Lean_Grind_Linarith_Expr_denoteN___redArg(x_1, x_2, x_11);
x_14 = lean_apply_2(x_9, x_12, x_13);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec_ref(x_3);
x_18 = l_Lean_Grind_Linarith_Expr_denoteN___redArg(x_1, x_2, x_17);
x_19 = lean_apply_2(x_15, x_16, x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_20);
lean_dec(x_3);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Linarith_Expr_denoteN___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Linarith_Expr_denoteN___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Linarith_Expr_denoteN(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0;
x_14 = lean_int_dec_lt(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_nat_abs(x_10);
x_16 = l_Lean_RArray_getImpl___redArg(x_2, x_11);
lean_inc(x_7);
x_17 = lean_apply_2(x_7, x_15, x_16);
x_18 = l_Lean_Grind_Linarith_Poly_denoteN___redArg(x_1, x_2, x_12);
x_19 = lean_apply_2(x_9, x_17, x_18);
return x_19;
}
else
{
lean_dec(x_9);
lean_inc(x_8);
lean_dec_ref(x_1);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Linarith_Poly_denoteN___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Linarith_Poly_denoteN___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Linarith_Poly_denoteN(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_3(x_3, x_6, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_3(x_3, x_6, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPolyN_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Grind_Linarith_Expr_toPolyN___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_Grind_Linarith_Expr_toPolyN(x_7);
x_10 = l_Lean_Grind_Linarith_Expr_toPolyN(x_8);
x_11 = l_Lean_Grind_Linarith_Poly_combine(x_9, x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = l_Lean_Grind_Linarith_Expr_toPolyN(x_13);
x_15 = lean_nat_to_int(x_12);
x_16 = l_Lean_Grind_Linarith_Poly_mul(x_14, x_15);
lean_dec(x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_5, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_1(x_6, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = lean_apply_2(x_7, x_13, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_apply_2(x_2, x_16, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = lean_apply_1(x_3, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec_ref(x_1);
x_23 = lean_apply_2(x_8, x_21, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_apply_2(x_4, x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__normN__cert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Grind_Linarith_Expr_toPolyN(x_1);
x_4 = l_Lean_Grind_Linarith_Expr_toPolyN(x_2);
x_5 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__normN__cert___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_Linarith_eq__normN__cert(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0 = _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0();
lean_mark_persistent(l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0);
l_Lean_Grind_Linarith_Expr_toPolyN___closed__0 = _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0();
lean_mark_persistent(l_Lean_Grind_Linarith_Expr_toPolyN___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
