// Lean compiler output
// Module: Init.Data.Nat.SOM
// Imports: Init.Data.Nat.Linear Init.Data.List.BasicAux
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
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_SOM_instInhabitedExpr___closed__0;
static lean_object* l_Nat_SOM_Poly_add_go___closed__0;
LEAN_EXPORT lean_object* l_Nat_SOM_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_denote(lean_object*, lean_object*);
lean_object* l_Nat_Linear_Var_denote(lean_object*, lean_object*);
uint8_t l_List_decidableLex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_insertSorted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add_go(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_denote___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_SOM_instInhabitedExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_SOM_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_SOM_instInhabitedExpr___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Nat_Linear_Var_denote(x_1, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Nat_SOM_Expr_denote(x_1, x_6);
x_9 = l_Nat_SOM_Expr_denote(x_1, x_7);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Nat_SOM_Expr_denote(x_1, x_11);
x_14 = l_Nat_SOM_Expr_denote(x_1, x_12);
x_15 = lean_nat_mul(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_SOM_Expr_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Nat_Linear_Var_denote(x_1, x_4);
x_7 = l_Nat_SOM_Mon_denote(x_1, x_5);
x_8 = lean_nat_mul(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_SOM_Mon_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_2) == 0)
{
return x_3;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_1, x_11);
x_13 = l_Nat_blt(x_7, x_9);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = l_Nat_blt(x_9, x_7);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = l_Nat_SOM_Mon_mul_go(x_12, x_8, x_10);
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_22 = l_Nat_SOM_Mon_mul_go(x_12, x_8, x_10);
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_22);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
x_24 = l_Nat_SOM_Mon_mul_go(x_12, x_2, x_10);
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_24);
return x_3;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = l_Nat_blt(x_9, x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_26 = x_2;
} else {
 lean_dec_ref(x_2);
 x_26 = lean_box(0);
}
x_27 = l_Nat_SOM_Mon_mul_go(x_12, x_8, x_10);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
x_30 = l_Nat_SOM_Mon_mul_go(x_12, x_2, x_10);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_inc(x_3);
x_32 = l_Nat_SOM_Mon_mul_go(x_12, x_8, x_3);
lean_dec(x_12);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_3, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_dec(x_35);
lean_ctor_set(x_3, 1, x_32);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_36; 
lean_dec(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_SOM_Mon_mul_go(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1000000u);
x_4 = l_Nat_SOM_Mon_mul_go(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Nat_SOM_Mon_denote(x_1, x_7);
x_9 = lean_nat_mul(x_6, x_8);
lean_dec(x_8);
x_10 = l_Nat_SOM_Poly_denote(x_1, x_5);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_SOM_Poly_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_SOM_Poly_add_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_18 = l_Nat_SOM_Poly_add_go___closed__0;
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_17);
x_19 = l_List_decidableLex___redArg(x_17, x_18, x_11, x_14);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
lean_inc(x_11);
x_23 = l_List_decidableLex___redArg(x_17, x_18, x_14, x_11);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_8, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_8, 0);
lean_dec(x_26);
x_27 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_28 = lean_nat_dec_eq(x_27, x_4);
if (x_28 == 0)
{
lean_object* x_29; 
lean_ctor_set(x_8, 1, x_11);
lean_ctor_set(x_8, 0, x_27);
x_29 = l_Nat_SOM_Poly_add_go(x_16, x_9, x_12);
lean_ctor_set(x_3, 1, x_29);
return x_3;
}
else
{
lean_dec(x_27);
lean_free_object(x_8);
lean_free_object(x_3);
lean_dec(x_11);
x_1 = x_16;
x_2 = x_9;
x_3 = x_12;
goto _start;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_8);
x_31 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_32 = lean_nat_dec_eq(x_31, x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_11);
x_34 = l_Nat_SOM_Poly_add_go(x_16, x_9, x_12);
lean_ctor_set(x_3, 1, x_34);
lean_ctor_set(x_3, 0, x_33);
return x_3;
}
else
{
lean_dec(x_31);
lean_free_object(x_3);
lean_dec(x_11);
x_1 = x_16;
x_2 = x_9;
x_3 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_36 = l_Nat_SOM_Poly_add_go(x_16, x_2, x_12);
lean_ctor_set(x_3, 1, x_36);
return x_3;
}
}
else
{
uint8_t x_37; 
lean_dec(x_3);
lean_inc(x_11);
x_37 = l_List_decidableLex___redArg(x_17, x_18, x_14, x_11);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_38 = x_8;
} else {
 lean_dec_ref(x_8);
 x_38 = lean_box(0);
}
x_39 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_40 = lean_nat_dec_eq(x_39, x_4);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_11);
x_42 = l_Nat_SOM_Poly_add_go(x_16, x_9, x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_11);
x_1 = x_16;
x_2 = x_9;
x_3 = x_12;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_45 = l_Nat_SOM_Poly_add_go(x_16, x_2, x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_inc(x_3);
x_47 = l_Nat_SOM_Poly_add_go(x_16, x_9, x_3);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_3, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_3, 0);
lean_dec(x_50);
lean_ctor_set(x_3, 1, x_47);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_51; 
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_47);
return x_51;
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
x_4 = l_Nat_SOM_Poly_add_go(x_3, x_1, x_2);
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
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_10 = l_Nat_SOM_Poly_add_go___closed__0;
lean_inc(x_2);
x_11 = l_List_decidableLex___redArg(x_9, x_10, x_2, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
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
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_SOM_Poly_mulMon_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Nat_SOM_Poly_mulMon_go(x_2, x_3, x_1, x_4);
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
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_2);
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
x_4 = l_Nat_SOM_Poly_mul_go(x_2, x_1, x_3);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = l_Nat_SOM_Expr_toPoly(x_17);
x_20 = l_Nat_SOM_Expr_toPoly(x_18);
x_21 = l_Nat_SOM_Poly_add(x_19, x_20);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = l_Nat_SOM_Expr_toPoly(x_22);
x_25 = l_Nat_SOM_Expr_toPoly(x_23);
x_26 = l_Nat_SOM_Poly_mul(x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_SOM_Expr_toPoly(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_4(x_5, x_9, x_10, x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_8);
lean_dec(x_5);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_apply_6(x_5, x_12, x_13, x_11, x_15, x_16, x_14);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_SOM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_SOM_instInhabitedExpr___closed__0 = _init_l_Nat_SOM_instInhabitedExpr___closed__0();
lean_mark_persistent(l_Nat_SOM_instInhabitedExpr___closed__0);
l_Nat_SOM_instInhabitedExpr = _init_l_Nat_SOM_instInhabitedExpr();
lean_mark_persistent(l_Nat_SOM_instInhabitedExpr);
l_Nat_SOM_Poly_add_go___closed__0 = _init_l_Nat_SOM_Poly_add_go___closed__0();
lean_mark_persistent(l_Nat_SOM_Poly_add_go___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
