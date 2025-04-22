// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
// Imports: Init.Grind.CommRing.Poly
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Grind_CommRing_hugeFuel;
static lean_object* l_Lean_Grind_CommRing_Poly_spol___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spol(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Grind_CommRing_Poly_spol___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter(lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_Poly_spol___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__2_splitter(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_coprime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divides___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_divides___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_coprime___boxed(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_lt(x_11, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_3);
x_17 = l_Lean_Grind_CommRing_Mon_lcm(x_2, x_9);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
uint8_t x_18; 
lean_free_object(x_1);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = lean_nat_dec_le(x_12, x_14);
x_22 = l_Lean_Grind_CommRing_Mon_lcm(x_6, x_9);
if (x_21 == 0)
{
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_11);
lean_ctor_set(x_2, 1, x_22);
return x_2;
}
else
{
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_11);
lean_ctor_set(x_2, 1, x_22);
return x_2;
}
}
else
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_4);
x_23 = lean_nat_dec_le(x_12, x_14);
x_24 = l_Lean_Grind_CommRing_Mon_lcm(x_6, x_9);
if (x_23 == 0)
{
lean_object* x_25; 
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; 
lean_dec(x_12);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_14);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_27 = l_Lean_Grind_CommRing_Mon_lcm(x_6, x_2);
lean_ctor_set(x_1, 1, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
x_33 = lean_nat_dec_lt(x_29, x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_nat_dec_eq(x_29, x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_6);
x_36 = l_Lean_Grind_CommRing_Mon_lcm(x_35, x_28);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_free_object(x_1);
lean_dec(x_3);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_37 = x_4;
} else {
 lean_dec_ref(x_4);
 x_37 = lean_box(0);
}
x_38 = lean_nat_dec_le(x_30, x_32);
x_39 = l_Lean_Grind_CommRing_Mon_lcm(x_6, x_28);
if (x_38 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_30);
if (lean_is_scalar(x_37)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_37;
}
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_28);
x_45 = l_Lean_Grind_CommRing_Mon_lcm(x_6, x_44);
lean_ctor_set(x_1, 1, x_45);
return x_1;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_48 = x_2;
} else {
 lean_dec_ref(x_2);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 1);
lean_inc(x_52);
x_53 = lean_nat_dec_lt(x_49, x_51);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_nat_dec_eq(x_49, x_51);
lean_dec(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_49);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_46);
x_56 = l_Lean_Grind_CommRing_Mon_lcm(x_55, x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
lean_dec(x_3);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_58 = x_4;
} else {
 lean_dec_ref(x_4);
 x_58 = lean_box(0);
}
x_59 = lean_nat_dec_le(x_50, x_52);
x_60 = l_Lean_Grind_CommRing_Mon_lcm(x_46, x_47);
if (x_59 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_50);
if (lean_is_scalar(x_48)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_48;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_50);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_52);
if (lean_is_scalar(x_48)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_48;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
if (lean_is_scalar(x_48)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_48;
}
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_47);
x_66 = l_Lean_Grind_CommRing_Mon_lcm(x_46, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_3);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_1, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_5, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__2_splitter___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_inc(x_2);
return x_2;
}
default: 
{
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_lcm_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = 1;
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_13 == 0)
{
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_5);
x_1 = x_2;
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_2);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_nat_dec_le(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_6);
x_18 = 0;
return x_18;
}
else
{
x_1 = x_6;
x_2 = x_9;
goto _start;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_20 = 0;
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
x_1 = x_27;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_6);
x_32 = 0;
return x_32;
}
else
{
x_1 = x_6;
x_2 = x_22;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
x_34 = 0;
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_divides___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Mon_divides(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_nat_dec_lt(x_10, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_free_object(x_1);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_nat_dec_eq(x_10, x_12);
lean_dec(x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_6);
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_nat_sub(x_11, x_19);
lean_dec(x_19);
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_ctor_set(x_6, 1, x_20);
x_23 = l_Lean_Grind_CommRing_Mon_div(x_7, x_9);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_dec(x_20);
lean_free_object(x_6);
lean_dec(x_10);
lean_free_object(x_2);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = lean_nat_dec_eq(x_10, x_12);
lean_dec(x_12);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_nat_sub(x_11, x_27);
lean_dec(x_27);
lean_dec(x_11);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_28);
x_32 = l_Lean_Grind_CommRing_Mon_div(x_7, x_9);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_dec(x_28);
lean_dec(x_10);
lean_free_object(x_2);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_34 = l_Lean_Grind_CommRing_Mon_div(x_7, x_2);
lean_ctor_set(x_1, 1, x_34);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_2);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_nat_dec_lt(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_free_object(x_1);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
x_44 = lean_nat_dec_eq(x_39, x_41);
lean_dec(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_45 = lean_box(0);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_nat_sub(x_40, x_46);
lean_dec(x_46);
lean_dec(x_40);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
if (lean_is_scalar(x_43)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_43;
}
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_47);
x_51 = l_Lean_Grind_CommRing_Mon_div(x_36, x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_39);
x_1 = x_36;
x_2 = x_38;
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_37);
lean_ctor_set(x_54, 1, x_38);
x_55 = l_Lean_Grind_CommRing_Mon_div(x_36, x_54);
lean_ctor_set(x_1, 1, x_55);
return x_1;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_1);
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_60 = x_2;
} else {
 lean_dec_ref(x_2);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_nat_dec_lt(x_61, x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
 x_65 = lean_box(0);
}
x_66 = lean_nat_dec_eq(x_61, x_63);
lean_dec(x_63);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_67 = lean_box(0);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_dec(x_58);
x_69 = lean_nat_sub(x_62, x_68);
lean_dec(x_68);
lean_dec(x_62);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_69);
x_73 = l_Lean_Grind_CommRing_Mon_div(x_57, x_59);
if (lean_is_scalar(x_60)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_60;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_60);
x_1 = x_57;
x_2 = x_59;
goto _start;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
if (lean_is_scalar(x_60)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_60;
}
lean_ctor_set(x_76, 0, x_58);
lean_ctor_set(x_76, 1, x_59);
x_77 = l_Lean_Grind_CommRing_Mon_div(x_57, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_56);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_coprime(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = 1;
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_13 == 0)
{
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_5);
x_1 = x_2;
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_15; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_15 = 0;
return x_15;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_17);
x_22 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_1 = x_23;
x_2 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
x_25 = 0;
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
x_1 = x_6;
x_2 = x_26;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_coprime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Mon_coprime(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_Poly_spol___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Grind_CommRing_Poly_spol___closed__2;
x_2 = l_Lean_Grind_CommRing_Poly_spol___closed__1;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spol(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = l_Lean_Grind_CommRing_Poly_spol___closed__3;
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_Grind_CommRing_Poly_spol___closed__3;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_6);
x_11 = l_Lean_Grind_CommRing_Mon_lcm(x_6, x_9);
lean_inc(x_11);
x_12 = l_Lean_Grind_CommRing_Mon_div(x_11, x_6);
x_13 = l_Lean_Grind_CommRing_Mon_div(x_11, x_9);
x_14 = lean_nat_abs(x_5);
x_15 = lean_nat_abs(x_8);
x_16 = lean_nat_gcd(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_ediv(x_8, x_17);
lean_dec(x_8);
x_19 = lean_int_neg(x_5);
lean_dec(x_5);
x_20 = lean_int_ediv(x_19, x_17);
lean_dec(x_17);
lean_dec(x_19);
lean_inc(x_12);
x_21 = l_Lean_Grind_CommRing_Poly_mulMon(x_18, x_12, x_7);
lean_inc(x_13);
x_22 = l_Lean_Grind_CommRing_Poly_mulMon(x_20, x_13, x_10);
x_23 = l_Lean_Grind_CommRing_hugeFuel;
x_24 = l_Lean_Grind_CommRing_Poly_combine_go(x_23, x_21, x_22);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_13);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
lean_inc(x_2);
x_10 = l_Lean_Grind_CommRing_Mon_divides(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(x_1, x_2, x_3, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 2);
x_18 = lean_int_mul(x_7, x_17);
lean_dec(x_7);
lean_ctor_set(x_4, 2, x_16);
lean_ctor_set(x_4, 0, x_18);
lean_ctor_set(x_14, 0, x_4);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_ctor_get(x_14, 2);
x_22 = lean_ctor_get(x_14, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_23 = lean_int_mul(x_7, x_21);
lean_dec(x_7);
lean_ctor_set(x_4, 2, x_19);
lean_ctor_set(x_4, 0, x_23);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
x_31 = lean_int_mul(x_7, x_28);
lean_dec(x_7);
lean_ctor_set(x_4, 2, x_26);
lean_ctor_set(x_4, 0, x_31);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 4, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_4);
x_34 = l_Lean_Grind_CommRing_Mon_div(x_8, x_2);
x_35 = lean_nat_abs(x_1);
x_36 = lean_nat_abs(x_7);
x_37 = lean_nat_gcd(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
x_38 = lean_int_neg(x_7);
lean_dec(x_7);
x_39 = lean_nat_to_int(x_37);
x_40 = lean_int_ediv(x_38, x_39);
lean_dec(x_38);
x_41 = lean_int_ediv(x_1, x_39);
lean_dec(x_39);
lean_inc(x_34);
x_42 = l_Lean_Grind_CommRing_Poly_mulMon(x_40, x_34, x_3);
x_43 = l_Lean_Grind_CommRing_Poly_mulConst(x_41, x_9);
x_44 = l_Lean_Grind_CommRing_hugeFuel;
x_45 = l_Lean_Grind_CommRing_Poly_combine_go(x_44, x_42, x_43);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_34);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
x_50 = lean_ctor_get(x_4, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
lean_inc(x_49);
lean_inc(x_2);
x_51 = l_Lean_Grind_CommRing_Mon_divides(x_2, x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(x_1, x_2, x_3, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec(x_49);
lean_dec(x_48);
x_53 = lean_box(0);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 3);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
x_61 = lean_int_mul(x_48, x_58);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_49);
lean_ctor_set(x_62, 2, x_56);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 4, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_59);
if (lean_is_scalar(x_55)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_55;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_65 = l_Lean_Grind_CommRing_Mon_div(x_49, x_2);
x_66 = lean_nat_abs(x_1);
x_67 = lean_nat_abs(x_48);
x_68 = lean_nat_gcd(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
x_69 = lean_int_neg(x_48);
lean_dec(x_48);
x_70 = lean_nat_to_int(x_68);
x_71 = lean_int_ediv(x_69, x_70);
lean_dec(x_69);
x_72 = lean_int_ediv(x_1, x_70);
lean_dec(x_70);
lean_inc(x_65);
x_73 = l_Lean_Grind_CommRing_Poly_mulMon(x_71, x_65, x_3);
x_74 = l_Lean_Grind_CommRing_Poly_mulConst(x_72, x_50);
x_75 = l_Lean_Grind_CommRing_hugeFuel;
x_76 = l_Lean_Grind_CommRing_Poly_combine_go(x_75, x_73, x_74);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_65);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(x_4, x_5, x_6, x_2);
lean_dec(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Grind_CommRing_Mon_degree(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Poly_degree(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Grind_CommRing_Mon_divides(x_4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divides___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Poly_divides(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Poly_lc(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Poly_lm(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Grind_CommRing_Poly(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_CommRing_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_CommRing_Poly_spol___closed__1 = _init_l_Lean_Grind_CommRing_Poly_spol___closed__1();
lean_mark_persistent(l_Lean_Grind_CommRing_Poly_spol___closed__1);
l_Lean_Grind_CommRing_Poly_spol___closed__2 = _init_l_Lean_Grind_CommRing_Poly_spol___closed__2();
lean_mark_persistent(l_Lean_Grind_CommRing_Poly_spol___closed__2);
l_Lean_Grind_CommRing_Poly_spol___closed__3 = _init_l_Lean_Grind_CommRing_Poly_spol___closed__3();
lean_mark_persistent(l_Lean_Grind_CommRing_Poly_spol___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
