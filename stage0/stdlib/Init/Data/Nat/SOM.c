// Lean compiler output
// Module: Init.Data.Nat.SOM
// Imports: public import Init.Data.List.BasicAux
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
uint8_t l_Nat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx___boxed(lean_object*);
static lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0;
static lean_object* l_Nat_SOM_instInhabitedExpr_default___closed__0;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim___redArg(lean_object*, lean_object*);
uint8_t l_List_decidableLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_instInhabitedExpr_default;
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_insertSorted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_SOM_Expr_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_SOM_Expr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_SOM_Expr_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_SOM_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_num_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_SOM_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_SOM_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_SOM_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_SOM_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_add_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_SOM_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_SOM_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_mul_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_SOM_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Nat_SOM_instInhabitedExpr_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_SOM_instInhabitedExpr_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_SOM_instInhabitedExpr_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Nat_SOM_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_SOM_instInhabitedExpr_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
x_6 = l_List_appendTR___redArg(x_2, x_3);
return x_6;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_1, x_11);
x_13 = l_Nat_blt(x_9, x_7);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc(x_8);
lean_inc(x_7);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = l_Nat_blt(x_7, x_9);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_10);
lean_inc(x_9);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_12, x_10, x_8);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_7);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_22 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_12, x_10, x_8);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
}
else
{
lean_object* x_24; 
x_24 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_12, x_2, x_8);
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_24);
return x_3;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = l_Nat_blt(x_7, x_9);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_10);
lean_inc(x_9);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_26 = x_2;
} else {
 lean_dec_ref(x_2);
 x_26 = lean_box(0);
}
x_27 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_12, x_10, x_8);
lean_dec(x_12);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_12, x_2, x_8);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_inc(x_10);
lean_inc(x_9);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_2, 0);
lean_dec(x_34);
x_35 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_12, x_10, x_3);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_35);
return x_2;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_12, x_10, x_3);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1000000u);
x_4 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_List_appendTR___redArg(x_2, x_3);
return x_6;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_18 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0;
lean_inc(x_14);
lean_inc(x_12);
lean_inc_ref(x_17);
x_19 = l_List_decidableLex___redArg(x_17, x_18, x_12, x_14);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_9);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
lean_inc(x_12);
lean_inc(x_14);
x_23 = l_List_decidableLex___redArg(x_17, x_18, x_14, x_12);
if (x_23 == 0)
{
uint8_t x_24; 
lean_free_object(x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_8, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_8, 0);
lean_dec(x_29);
x_30 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_31 = lean_nat_dec_eq(x_30, x_4);
if (x_31 == 0)
{
lean_object* x_32; 
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_30);
x_32 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_10, x_9);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_dec(x_30);
lean_free_object(x_8);
lean_free_object(x_2);
lean_dec(x_12);
x_1 = x_16;
x_2 = x_10;
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_8);
x_34 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_35 = lean_nat_dec_eq(x_34, x_4);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_12);
x_37 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_10, x_9);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_36);
return x_2;
}
else
{
lean_dec(x_34);
lean_free_object(x_2);
lean_dec(x_12);
x_1 = x_16;
x_2 = x_10;
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_39 = x_8;
} else {
 lean_dec_ref(x_8);
 x_39 = lean_box(0);
}
x_40 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_41 = lean_nat_dec_eq(x_40, x_4);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_12);
x_43 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_10, x_9);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_12);
x_1 = x_16;
x_2 = x_10;
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_46; 
x_46 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_2, x_9);
lean_ctor_set(x_3, 1, x_46);
return x_3;
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_14);
x_47 = l_List_decidableLex___redArg(x_17, x_18, x_14, x_12);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_48 = x_2;
} else {
 lean_dec_ref(x_2);
 x_48 = lean_box(0);
}
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_49 = x_8;
} else {
 lean_dec_ref(x_8);
 x_49 = lean_box(0);
}
x_50 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_51 = lean_nat_dec_eq(x_50, x_4);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_12);
x_53 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_10, x_9);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_48;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_12);
x_1 = x_16;
x_2 = x_10;
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_2, x_9);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_17);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_7);
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_2, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_2, 0);
lean_dec(x_60);
x_61 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_10, x_3);
lean_ctor_set(x_2, 1, x_61);
return x_2;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_62 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_16, x_10, x_3);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_7);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1000000u);
x_4 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_insertSorted(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_10 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0;
lean_inc(x_8);
lean_inc(x_2);
x_11 = l_List_decidableLex___redArg(x_9, x_10, x_2, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_7);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = l_Nat_SOM_Poly_insertSorted(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_15);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = l_Nat_SOM_Poly_insertSorted(x_1, x_2, x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_nat_mul(x_1, x_7);
lean_dec(x_7);
lean_inc(x_2);
x_10 = l_Nat_SOM_Mon_mul(x_2, x_8);
x_11 = l_Nat_SOM_Poly_insertSorted(x_9, x_10, x_4);
x_3 = x_6;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mulMon_go(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_SOM_Poly_mulMon(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_Nat_SOM_Poly_mulMon(x_1, x_6, x_7);
lean_dec(x_6);
x_9 = l_Nat_SOM_Poly_add(x_3, x_8);
x_2 = x_5;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_mul_go(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_box(0);
lean_inc(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l_Nat_SOM_Expr_toPoly(x_15);
x_18 = l_Nat_SOM_Expr_toPoly(x_16);
x_19 = l_Nat_SOM_Poly_add(x_17, x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = l_Nat_SOM_Expr_toPoly(x_20);
x_23 = l_Nat_SOM_Expr_toPoly(x_21);
x_24 = l_Nat_SOM_Poly_mul(x_22, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_SOM_Expr_toPoly(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_4(x_5, x_10, x_11, x_8, x_9);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_4, x_2);
return x_7;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_apply_2(x_5, x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_apply_4(x_6, x_11, x_12, x_9, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_apply_6(x_5, x_12, x_13, x_11, x_14, x_15, x_10);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_4, x_2);
return x_7;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_apply_2(x_5, x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_apply_6(x_6, x_13, x_14, x_12, x_15, x_16, x_11);
return x_17;
}
}
}
}
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_SOM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_SOM_instInhabitedExpr_default___closed__0 = _init_l_Nat_SOM_instInhabitedExpr_default___closed__0();
lean_mark_persistent(l_Nat_SOM_instInhabitedExpr_default___closed__0);
l_Nat_SOM_instInhabitedExpr_default = _init_l_Nat_SOM_instInhabitedExpr_default();
lean_mark_persistent(l_Nat_SOM_instInhabitedExpr_default);
l_Nat_SOM_instInhabitedExpr = _init_l_Nat_SOM_instInhabitedExpr();
lean_mark_persistent(l_Nat_SOM_instInhabitedExpr);
l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0 = _init_l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0();
lean_mark_persistent(l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
