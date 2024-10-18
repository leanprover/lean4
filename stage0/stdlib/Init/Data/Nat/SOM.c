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
extern lean_object* l_Nat_Linear_hugeFuel;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
static lean_object* l_Nat_SOM_Poly_add_go___closed__1;
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly___boxed(lean_object*);
uint8_t l_List_hasDecidableLt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_SOM_instInhabitedExpr___closed__1;
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_denote(lean_object*, lean_object*);
lean_object* l_Nat_Linear_Var_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Expr_toPoly(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instLTNat;
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_insertSorted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Mon_denote___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_mulMon___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_SOM_instInhabitedExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_SOM_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_SOM_instInhabitedExpr___closed__1;
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
lean_dec(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Nat_Linear_Var_denote(x_1, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
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
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
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
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
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
if (x_5 == 0)
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_1, x_12);
x_14 = l_Nat_blt(x_8, x_10);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Nat_blt(x_10, x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Nat_SOM_Mon_mul_go(x_13, x_9, x_11);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_17; 
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
x_17 = l_Nat_SOM_Mon_mul_go(x_13, x_3, x_11);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
}
else
{
lean_object* x_18; 
x_18 = l_Nat_SOM_Mon_mul_go(x_13, x_9, x_3);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_18);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_1, x_23);
x_25 = l_Nat_blt(x_19, x_21);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Nat_blt(x_21, x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Nat_SOM_Mon_mul_go(x_24, x_20, x_22);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_2, 1, x_28);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
x_30 = l_Nat_SOM_Mon_mul_go(x_24, x_29, x_22);
lean_dec(x_24);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_21);
return x_2;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
x_32 = l_Nat_SOM_Mon_mul_go(x_24, x_20, x_31);
lean_dec(x_24);
lean_ctor_set(x_2, 1, x_32);
return x_2;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_37 = x_3;
} else {
 lean_dec_ref(x_3);
 x_37 = lean_box(0);
}
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_1, x_38);
x_40 = l_Nat_blt(x_33, x_35);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Nat_blt(x_35, x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Nat_SOM_Mon_mul_go(x_39, x_34, x_36);
lean_dec(x_39);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_37;
}
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_34);
x_46 = l_Nat_SOM_Mon_mul_go(x_39, x_45, x_36);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_37)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_37;
}
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set(x_48, 1, x_36);
x_49 = l_Nat_SOM_Mon_mul_go(x_39, x_34, x_48);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
else
{
lean_object* x_51; 
x_51 = l_List_appendTR___rarg(x_2, x_3);
return x_51;
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
x_3 = l_Nat_Linear_hugeFuel;
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
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Nat_SOM_Mon_denote(x_1, x_7);
x_9 = lean_nat_mul(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
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
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_SOM_Poly_add_go___closed__1() {
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
if (x_5 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
x_23 = l_instLTNat;
x_24 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_22);
lean_inc(x_17);
x_25 = l_List_hasDecidableLt___rarg(x_23, x_24, x_17, x_22);
if (x_25 == 0)
{
uint8_t x_26; 
lean_inc(x_17);
lean_inc(x_22);
x_26 = l_List_hasDecidableLt___rarg(x_23, x_24, x_22, x_17);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_22);
lean_free_object(x_6);
lean_free_object(x_2);
x_27 = lean_nat_add(x_16, x_21);
lean_dec(x_21);
lean_dec(x_16);
x_28 = lean_nat_dec_eq(x_27, x_4);
if (x_28 == 0)
{
lean_object* x_29; 
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_27);
x_29 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_18);
lean_ctor_set(x_3, 1, x_29);
return x_3;
}
else
{
lean_dec(x_27);
lean_free_object(x_13);
lean_free_object(x_3);
lean_dec(x_17);
x_1 = x_9;
x_2 = x_7;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_31; 
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_6);
x_31 = l_Nat_SOM_Poly_add_go(x_9, x_3, x_18);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_32; 
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_16);
lean_ctor_set(x_6, 1, x_22);
lean_ctor_set(x_6, 0, x_21);
lean_ctor_set(x_3, 0, x_6);
x_32 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_3);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = l_instLTNat;
x_36 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_34);
lean_inc(x_17);
x_37 = l_List_hasDecidableLt___rarg(x_35, x_36, x_17, x_34);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc(x_17);
lean_inc(x_34);
x_38 = l_List_hasDecidableLt___rarg(x_35, x_36, x_34, x_17);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_34);
lean_free_object(x_6);
lean_free_object(x_2);
x_39 = lean_nat_add(x_16, x_33);
lean_dec(x_33);
lean_dec(x_16);
x_40 = lean_nat_dec_eq(x_39, x_4);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_17);
x_42 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_18);
lean_ctor_set(x_3, 1, x_42);
lean_ctor_set(x_3, 0, x_41);
return x_3;
}
else
{
lean_dec(x_39);
lean_free_object(x_3);
lean_dec(x_17);
x_1 = x_9;
x_2 = x_7;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_6);
x_45 = l_Nat_SOM_Poly_add_go(x_9, x_3, x_18);
lean_ctor_set(x_2, 1, x_45);
lean_ctor_set(x_2, 0, x_44);
return x_2;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_17);
lean_ctor_set(x_6, 1, x_34);
lean_ctor_set(x_6, 0, x_33);
lean_ctor_set(x_3, 0, x_6);
x_47 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_3);
lean_ctor_set(x_2, 1, x_47);
lean_ctor_set(x_2, 0, x_46);
return x_2;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_ctor_get(x_13, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_53 = x_13;
} else {
 lean_dec_ref(x_13);
 x_53 = lean_box(0);
}
x_54 = l_instLTNat;
x_55 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_52);
lean_inc(x_49);
x_56 = l_List_hasDecidableLt___rarg(x_54, x_55, x_49, x_52);
if (x_56 == 0)
{
uint8_t x_57; 
lean_inc(x_49);
lean_inc(x_52);
x_57 = l_List_hasDecidableLt___rarg(x_54, x_55, x_52, x_49);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_52);
lean_free_object(x_6);
lean_free_object(x_2);
x_58 = lean_nat_add(x_48, x_51);
lean_dec(x_51);
lean_dec(x_48);
x_59 = lean_nat_dec_eq(x_58, x_4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_53;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_49);
x_61 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_50);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
else
{
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_49);
x_1 = x_9;
x_2 = x_7;
x_3 = x_50;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
if (lean_is_scalar(x_53)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_53;
}
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_7);
x_66 = l_Nat_SOM_Poly_add_go(x_9, x_65, x_50);
lean_ctor_set(x_2, 1, x_66);
lean_ctor_set(x_2, 0, x_64);
return x_2;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
if (lean_is_scalar(x_53)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_53;
}
lean_ctor_set(x_67, 0, x_48);
lean_ctor_set(x_67, 1, x_49);
lean_ctor_set(x_6, 1, x_52);
lean_ctor_set(x_6, 0, x_51);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_6);
lean_ctor_set(x_68, 1, x_50);
x_69 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_68);
lean_ctor_set(x_2, 1, x_69);
lean_ctor_set(x_2, 0, x_67);
return x_2;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_70 = lean_ctor_get(x_6, 0);
x_71 = lean_ctor_get(x_6, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_6);
x_72 = lean_ctor_get(x_3, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_73 = x_3;
} else {
 lean_dec_ref(x_3);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_13, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_76 = x_13;
} else {
 lean_dec_ref(x_13);
 x_76 = lean_box(0);
}
x_77 = l_instLTNat;
x_78 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_75);
lean_inc(x_71);
x_79 = l_List_hasDecidableLt___rarg(x_77, x_78, x_71, x_75);
if (x_79 == 0)
{
uint8_t x_80; 
lean_inc(x_71);
lean_inc(x_75);
x_80 = l_List_hasDecidableLt___rarg(x_77, x_78, x_75, x_71);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_75);
lean_free_object(x_2);
x_81 = lean_nat_add(x_70, x_74);
lean_dec(x_74);
lean_dec(x_70);
x_82 = lean_nat_dec_eq(x_81, x_4);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_71);
x_84 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_72);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
else
{
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_71);
x_1 = x_9;
x_2 = x_7;
x_3 = x_72;
goto _start;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_76)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_76;
}
lean_ctor_set(x_87, 0, x_74);
lean_ctor_set(x_87, 1, x_75);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_70);
lean_ctor_set(x_88, 1, x_71);
if (lean_is_scalar(x_73)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_73;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_7);
x_90 = l_Nat_SOM_Poly_add_go(x_9, x_89, x_72);
lean_ctor_set(x_2, 1, x_90);
lean_ctor_set(x_2, 0, x_87);
return x_2;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_scalar(x_76)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_76;
}
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_71);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_74);
lean_ctor_set(x_92, 1, x_75);
if (lean_is_scalar(x_73)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_73;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_72);
x_94 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_93);
lean_ctor_set(x_2, 1, x_94);
lean_ctor_set(x_2, 0, x_91);
return x_2;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_2);
x_95 = lean_ctor_get(x_3, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_6, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_100 = x_3;
} else {
 lean_dec_ref(x_3);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_103 = x_95;
} else {
 lean_dec_ref(x_95);
 x_103 = lean_box(0);
}
x_104 = l_instLTNat;
x_105 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_102);
lean_inc(x_97);
x_106 = l_List_hasDecidableLt___rarg(x_104, x_105, x_97, x_102);
if (x_106 == 0)
{
uint8_t x_107; 
lean_inc(x_97);
lean_inc(x_102);
x_107 = l_List_hasDecidableLt___rarg(x_104, x_105, x_102, x_97);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
lean_dec(x_102);
lean_dec(x_98);
x_108 = lean_nat_add(x_96, x_101);
lean_dec(x_101);
lean_dec(x_96);
x_109 = lean_nat_dec_eq(x_108, x_4);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_scalar(x_103)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_103;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_97);
x_111 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_99);
if (lean_is_scalar(x_100)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_100;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
else
{
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_97);
x_1 = x_9;
x_2 = x_7;
x_3 = x_99;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
if (lean_is_scalar(x_103)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_103;
}
lean_ctor_set(x_114, 0, x_101);
lean_ctor_set(x_114, 1, x_102);
if (lean_is_scalar(x_98)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_98;
}
lean_ctor_set(x_115, 0, x_96);
lean_ctor_set(x_115, 1, x_97);
if (lean_is_scalar(x_100)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_100;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_7);
x_117 = l_Nat_SOM_Poly_add_go(x_9, x_116, x_99);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
if (lean_is_scalar(x_103)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_103;
}
lean_ctor_set(x_119, 0, x_96);
lean_ctor_set(x_119, 1, x_97);
if (lean_is_scalar(x_98)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_98;
}
lean_ctor_set(x_120, 0, x_101);
lean_ctor_set(x_120, 1, x_102);
if (lean_is_scalar(x_100)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_100;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_99);
x_122 = l_Nat_SOM_Poly_add_go(x_9, x_7, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
}
else
{
lean_object* x_124; 
lean_dec(x_1);
x_124 = l_List_appendTR___rarg(x_2, x_3);
return x_124;
}
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Nat_Linear_hugeFuel;
x_4 = l_Nat_SOM_Poly_add_go(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_SOM_Poly_insertSorted(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = l_instLTNat;
x_14 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_12);
lean_inc(x_2);
x_15 = l_List_hasDecidableLt___rarg(x_13, x_14, x_2, x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Nat_SOM_Poly_insertSorted(x_1, x_2, x_10);
lean_ctor_set(x_3, 1, x_16);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_3, 0, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_instLTNat;
x_23 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_21);
lean_inc(x_2);
x_24 = l_List_hasDecidableLt___rarg(x_22, x_23, x_2, x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
x_26 = l_Nat_SOM_Poly_insertSorted(x_1, x_2, x_19);
lean_ctor_set(x_3, 1, x_26);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_3, 0, x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = l_instLTNat;
x_36 = l_Nat_SOM_Poly_add_go___closed__1;
lean_inc(x_33);
lean_inc(x_2);
x_37 = l_List_hasDecidableLt___rarg(x_35, x_36, x_2, x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
x_39 = l_Nat_SOM_Poly_insertSorted(x_1, x_2, x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
if (lean_is_scalar(x_34)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_34;
}
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_31);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
x_10 = l_Nat_Linear_hugeFuel;
lean_inc(x_2);
x_11 = l_Nat_SOM_Mon_mul_go(x_10, x_2, x_8);
x_12 = l_Nat_SOM_Poly_insertSorted(x_9, x_11, x_4);
x_3 = x_6;
x_4 = x_12;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
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
x_9 = l_Nat_Linear_hugeFuel;
x_10 = l_Nat_SOM_Poly_add_go(x_9, x_3, x_8);
x_2 = x_5;
x_3 = x_10;
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
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l_Nat_SOM_Expr_toPoly(x_15);
x_18 = l_Nat_SOM_Expr_toPoly(x_16);
x_19 = l_Nat_Linear_hugeFuel;
x_20 = l_Nat_SOM_Poly_add_go(x_19, x_17, x_18);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = l_Nat_SOM_Expr_toPoly(x_21);
x_24 = l_Nat_SOM_Expr_toPoly(x_22);
x_25 = l_Nat_SOM_Poly_mul(x_23, x_24);
return x_25;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Nat_SOM_0__Nat_SOM_Mon_mul_go_match__1_splitter___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Nat_SOM_0__Nat_SOM_Poly_add_go_match__1_splitter___rarg), 5, 0);
return x_2;
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
l_Nat_SOM_instInhabitedExpr___closed__1 = _init_l_Nat_SOM_instInhabitedExpr___closed__1();
lean_mark_persistent(l_Nat_SOM_instInhabitedExpr___closed__1);
l_Nat_SOM_instInhabitedExpr = _init_l_Nat_SOM_instInhabitedExpr();
lean_mark_persistent(l_Nat_SOM_instInhabitedExpr);
l_Nat_SOM_Poly_add_go___closed__1 = _init_l_Nat_SOM_Poly_add_go___closed__1();
lean_mark_persistent(l_Nat_SOM_Poly_add_go___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
