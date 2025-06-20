// Lean compiler output
// Module: Init.Grind.Ring.OfSemiring
// Imports: Init.Grind.Ring.Envelope Init.Data.Hashable Init.Data.RArray
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
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319____boxed(lean_object*);
lean_object* l_Lean_RArray_getImpl___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instHashableExpr;
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Var_denote___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_OfSemiring_0__Lean_Grind_Ring_OfSemiring_hashExpr_match__1_splitter____x40_Init_Grind_Ring_OfSemiring___hyg_319____rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_Ring_OfSemiring_instBEqExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Var_denote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr___closed__1;
lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_add___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Var_denote___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_hPow___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instBEqExpr;
static lean_object* l_Lean_Grind_Ring_OfSemiring_instHashableExpr___closed__1;
lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_mul___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_OfSemiring_0__Lean_Grind_Ring_OfSemiring_hashExpr_match__1_splitter____x40_Init_Grind_Ring_OfSemiring___hyg_319_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_nat_dec_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109_(x_11, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109_(x_19, x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
else
{
x_1 = x_20;
x_2 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
default: 
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109_(x_27, x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_28, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_instBEqExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_beqExpr____x40_Init_Grind_Ring_OfSemiring___hyg_109____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_instBEqExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Ring_OfSemiring_instBEqExpr___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = lean_uint64_of_nat(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 1;
x_8 = lean_uint64_of_nat(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = 2;
x_13 = l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(x_10);
x_14 = lean_uint64_mix_hash(x_12, x_13);
x_15 = l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(x_11);
x_16 = lean_uint64_mix_hash(x_14, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = 3;
x_20 = l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(x_17);
x_21 = lean_uint64_mix_hash(x_19, x_20);
x_22 = l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(x_18);
x_23 = lean_uint64_mix_hash(x_21, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = 4;
x_27 = l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(x_24);
x_28 = lean_uint64_mix_hash(x_26, x_27);
x_29 = lean_uint64_of_nat(x_25);
x_30 = lean_uint64_mix_hash(x_28, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_instHashableExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_hashExpr____x40_Init_Grind_Ring_OfSemiring___hyg_319____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_instHashableExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_Ring_OfSemiring_instHashableExpr___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Var_denote___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Var_denote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_Var_denote___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Var_denote___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_OfSemiring_Var_denote___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_RArray_getImpl___rarg(x_2, x_7);
lean_dec(x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_1);
x_12 = l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(x_1, x_2, x_9);
x_13 = l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(x_1, x_2, x_10);
x_14 = lean_apply_2(x_11, x_12, x_13);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_1);
x_18 = l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(x_1, x_2, x_15);
x_19 = l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(x_1, x_2, x_16);
x_20 = lean_apply_2(x_17, x_18, x_19);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(x_1, x_2, x_21);
x_25 = lean_apply_2(x_23, x_24, x_22);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_Expr_denote___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Grind_Ring_OfSemiring_natCast___rarg(x_1, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_RArray_getImpl___rarg(x_2, x_6);
lean_dec(x_6);
x_8 = l_Lean_Grind_Ring_OfSemiring_toQ___rarg(x_1, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_11 = l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(x_1, x_2, x_9);
lean_inc(x_1);
x_12 = l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(x_1, x_2, x_10);
x_13 = l_Lean_Grind_Ring_OfSemiring_add___rarg(x_1, x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_1);
x_16 = l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(x_1, x_2, x_14);
lean_inc(x_1);
x_17 = l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(x_1, x_2, x_15);
x_18 = l_Lean_Grind_Ring_OfSemiring_mul___rarg(x_1, x_16, x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_1);
x_21 = l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(x_1, x_2, x_19);
x_22 = l_Lean_Grind_Ring_OfSemiring_hPow___rarg(x_1, x_21, x_20);
lean_dec(x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_Expr_denoteAsRing___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_OfSemiring_0__Lean_Grind_Ring_OfSemiring_hashExpr_match__1_splitter____x40_Init_Grind_Ring_OfSemiring___hyg_319____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_2(x_5, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_2(x_6, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_OfSemiring_0__Lean_Grind_Ring_OfSemiring_hashExpr_match__1_splitter____x40_Init_Grind_Ring_OfSemiring___hyg_319_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Grind_Ring_OfSemiring_0__Lean_Grind_Ring_OfSemiring_hashExpr_match__1_splitter____x40_Init_Grind_Ring_OfSemiring___hyg_319____rarg), 6, 0);
return x_2;
}
}
lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_OfSemiring(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Envelope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr___closed__1 = _init_l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr___closed__1();
lean_mark_persistent(l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr___closed__1);
l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr = _init_l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr();
lean_mark_persistent(l_Lean_Grind_Ring_OfSemiring_instInhabitedExpr);
l_Lean_Grind_Ring_OfSemiring_instBEqExpr___closed__1 = _init_l_Lean_Grind_Ring_OfSemiring_instBEqExpr___closed__1();
lean_mark_persistent(l_Lean_Grind_Ring_OfSemiring_instBEqExpr___closed__1);
l_Lean_Grind_Ring_OfSemiring_instBEqExpr = _init_l_Lean_Grind_Ring_OfSemiring_instBEqExpr();
lean_mark_persistent(l_Lean_Grind_Ring_OfSemiring_instBEqExpr);
l_Lean_Grind_Ring_OfSemiring_instHashableExpr___closed__1 = _init_l_Lean_Grind_Ring_OfSemiring_instHashableExpr___closed__1();
lean_mark_persistent(l_Lean_Grind_Ring_OfSemiring_instHashableExpr___closed__1);
l_Lean_Grind_Ring_OfSemiring_instHashableExpr = _init_l_Lean_Grind_Ring_OfSemiring_instHashableExpr();
lean_mark_persistent(l_Lean_Grind_Ring_OfSemiring_instHashableExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
