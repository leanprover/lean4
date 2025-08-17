// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.VarRename
// Imports: Init.Grind.Ring.Poly Init.Grind.Ring.OfSemiring Lean.Meta.Tactic.Grind.Arith.VarRename
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_collectVar(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_Expr_renameVars___closed__0;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_array_get_size(x_4);
x_7 = lean_uint64_of_nat(x_5);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_4, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_5, x_19);
lean_dec(x_19);
lean_dec(x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_array_get_size(x_23);
x_27 = lean_uint64_of_nat(x_24);
x_28 = 32;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = 16;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = 1;
x_37 = lean_usize_sub(x_35, x_36);
x_38 = lean_usize_land(x_34, x_37);
x_39 = lean_array_uget(x_23, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_24, x_39);
lean_dec(x_39);
lean_dec(x_24);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_25);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Power_renameVars(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Grind_CommRing_Power_renameVars(x_4, x_2);
x_7 = l_Lean_Grind_CommRing_Mon_renameVars(x_5, x_2);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Grind_CommRing_Power_renameVars(x_8, x_2);
x_11 = l_Lean_Grind_CommRing_Mon_renameVars(x_9, x_2);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Mon_renameVars(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = l_Lean_Grind_CommRing_Mon_renameVars(x_4, x_2);
x_7 = l_Lean_Grind_CommRing_Poly_renameVars(x_5, x_2);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Lean_Grind_CommRing_Mon_renameVars(x_9, x_2);
x_12 = l_Lean_Grind_CommRing_Poly_renameVars(x_10, x_2);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_renameVars(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_renameVars___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_uint64_of_nat(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_free_object(x_1);
x_21 = l_Lean_Grind_CommRing_Expr_renameVars___closed__0;
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_array_get_size(x_24);
x_26 = lean_uint64_of_nat(x_23);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_24, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_23, x_38);
lean_dec(x_38);
lean_dec(x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = l_Lean_Grind_CommRing_Expr_renameVars___closed__0;
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
case 4:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = l_Lean_Grind_CommRing_Expr_renameVars(x_44, x_2);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l_Lean_Grind_CommRing_Expr_renameVars(x_46, x_2);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
case 5:
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
x_52 = l_Lean_Grind_CommRing_Expr_renameVars(x_50, x_2);
x_53 = l_Lean_Grind_CommRing_Expr_renameVars(x_51, x_2);
lean_ctor_set(x_1, 1, x_53);
lean_ctor_set(x_1, 0, x_52);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_1);
x_56 = l_Lean_Grind_CommRing_Expr_renameVars(x_54, x_2);
x_57 = l_Lean_Grind_CommRing_Expr_renameVars(x_55, x_2);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
case 6:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_1);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_ctor_get(x_1, 1);
x_62 = l_Lean_Grind_CommRing_Expr_renameVars(x_60, x_2);
x_63 = l_Lean_Grind_CommRing_Expr_renameVars(x_61, x_2);
lean_ctor_set(x_1, 1, x_63);
lean_ctor_set(x_1, 0, x_62);
return x_1;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_1, 0);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_1);
x_66 = l_Lean_Grind_CommRing_Expr_renameVars(x_64, x_2);
x_67 = l_Lean_Grind_CommRing_Expr_renameVars(x_65, x_2);
x_68 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
case 7:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_1);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
x_72 = l_Lean_Grind_CommRing_Expr_renameVars(x_70, x_2);
x_73 = l_Lean_Grind_CommRing_Expr_renameVars(x_71, x_2);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_72);
return x_1;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_1);
x_76 = l_Lean_Grind_CommRing_Expr_renameVars(x_74, x_2);
x_77 = l_Lean_Grind_CommRing_Expr_renameVars(x_75, x_2);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
case 8:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = l_Lean_Grind_CommRing_Expr_renameVars(x_80, x_2);
lean_ctor_set(x_1, 0, x_81);
return x_1;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_1);
x_84 = l_Lean_Grind_CommRing_Expr_renameVars(x_82, x_2);
x_85 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_renameVars(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_collectVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Meta_Grind_Arith_collectVar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_collectVars(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Grind_CommRing_Power_collectVars(x_3, x_2);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_collectVars(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Grind_CommRing_Mon_collectVars(x_3, x_2);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_collectVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_Lean_Meta_Grind_Arith_collectVar(x_9, x_2);
return x_10;
}
case 4:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_1 = x_11;
goto _start;
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_3 = x_13;
x_4 = x_14;
x_5 = x_2;
goto block_8;
}
case 6:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_3 = x_15;
x_4 = x_16;
x_5 = x_2;
goto block_8;
}
case 7:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_3 = x_17;
x_4 = x_18;
x_5 = x_2;
goto block_8;
}
case 8:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_1 = x_19;
goto _start;
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
block_8:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Expr_collectVars(x_3, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_uint64_of_nat(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_free_object(x_1);
x_21 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___closed__0;
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_array_get_size(x_24);
x_26 = lean_uint64_of_nat(x_23);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_24, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(x_23, x_38);
lean_dec(x_38);
lean_dec(x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___closed__0;
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
case 2:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_44, x_2);
x_47 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_45, x_2);
lean_ctor_set(x_1, 1, x_47);
lean_ctor_set(x_1, 0, x_46);
return x_1;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_1);
x_50 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_48, x_2);
x_51 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_49, x_2);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
case 3:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
x_56 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_54, x_2);
x_57 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_55, x_2);
lean_ctor_set(x_1, 1, x_57);
lean_ctor_set(x_1, 0, x_56);
return x_1;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_1);
x_60 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_58, x_2);
x_61 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_59, x_2);
x_62 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
default: 
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_1, 0);
x_65 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_64, x_2);
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_1);
x_68 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_66, x_2);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_OfSemiring_Expr_renameVars(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Expr_collectVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec_ref(x_1);
return x_2;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_Lean_Meta_Grind_Arith_collectVar(x_9, x_2);
return x_10;
}
case 4:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_1 = x_11;
goto _start;
}
default: 
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_3 = x_13;
x_4 = x_14;
x_5 = x_2;
goto block_8;
}
}
block_8:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_Ring_OfSemiring_Expr_collectVars(x_3, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
lean_object* initialize_Init_Grind_Ring_Poly(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ring_OfSemiring(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_VarRename(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_VarRename(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_OfSemiring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_VarRename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_CommRing_Expr_renameVars___closed__0 = _init_l_Lean_Grind_CommRing_Expr_renameVars___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_Expr_renameVars___closed__0);
l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___closed__0 = _init_l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___closed__0();
lean_mark_persistent(l_Lean_Grind_Ring_OfSemiring_Expr_renameVars___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
