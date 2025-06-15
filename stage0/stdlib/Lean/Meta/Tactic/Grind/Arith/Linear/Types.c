// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Types
// Imports: Std.Internal.Rat Init.Grind.CommRing.Poly Init.Grind.Ordered.Linarith Lean.Data.PersistentArray Lean.Meta.Tactic.Grind.ExprPtr
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static size_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__3;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__5;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = 1;
x_7 = lean_uint64_of_nat(x_4);
x_8 = l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(x_5);
x_9 = l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1;
x_10 = lean_int_dec_lt(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; 
x_11 = lean_nat_abs(x_3);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mul(x_12, x_11);
lean_dec(x_11);
x_14 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
x_15 = lean_uint64_mix_hash(x_6, x_14);
x_16 = lean_uint64_mix_hash(x_15, x_7);
x_17 = lean_uint64_mix_hash(x_16, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; 
x_18 = lean_nat_abs(x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_mul(x_21, x_20);
lean_dec(x_20);
x_23 = lean_nat_add(x_22, x_19);
lean_dec(x_22);
x_24 = lean_uint64_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_uint64_mix_hash(x_6, x_24);
x_26 = lean_uint64_mix_hash(x_25, x_7);
x_27 = lean_uint64_mix_hash(x_26, x_8);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = 1;
x_5 = lean_uint64_of_nat(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = 2;
x_10 = l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(x_8);
x_13 = lean_uint64_mix_hash(x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = 3;
x_17 = l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(x_14);
x_18 = lean_uint64_mix_hash(x_16, x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(x_15);
x_20 = lean_uint64_mix_hash(x_18, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = 4;
x_23 = l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(x_21);
x_24 = lean_uint64_mix_hash(x_22, x_23);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = 5;
x_28 = l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(x_26);
x_29 = l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1;
x_30 = lean_int_dec_lt(x_25, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; 
x_31 = lean_nat_abs(x_25);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_31);
lean_dec(x_31);
x_34 = lean_uint64_of_nat(x_33);
lean_dec(x_33);
x_35 = lean_uint64_mix_hash(x_27, x_34);
x_36 = lean_uint64_mix_hash(x_35, x_28);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; 
x_37 = lean_nat_abs(x_25);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_mul(x_40, x_39);
lean_dec(x_39);
x_42 = lean_nat_add(x_41, x_38);
lean_dec(x_41);
x_43 = lean_uint64_of_nat(x_42);
lean_dec(x_42);
x_44 = lean_uint64_mix_hash(x_27, x_43);
x_45 = lean_uint64_mix_hash(x_44, x_28);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_hashExpr____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_68____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__3() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3;
x_4 = lean_box(0);
x_5 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__4;
x_6 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__6;
x_7 = 0;
x_8 = lean_alloc_ctor(0, 34, 1);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_3);
lean_ctor_set(x_8, 5, x_1);
lean_ctor_set(x_8, 6, x_1);
lean_ctor_set(x_8, 7, x_1);
lean_ctor_set(x_8, 8, x_1);
lean_ctor_set(x_8, 9, x_1);
lean_ctor_set(x_8, 10, x_1);
lean_ctor_set(x_8, 11, x_1);
lean_ctor_set(x_8, 12, x_1);
lean_ctor_set(x_8, 13, x_3);
lean_ctor_set(x_8, 14, x_3);
lean_ctor_set(x_8, 15, x_1);
lean_ctor_set(x_8, 16, x_1);
lean_ctor_set(x_8, 17, x_1);
lean_ctor_set(x_8, 18, x_3);
lean_ctor_set(x_8, 19, x_3);
lean_ctor_set(x_8, 20, x_3);
lean_ctor_set(x_8, 21, x_1);
lean_ctor_set(x_8, 22, x_1);
lean_ctor_set(x_8, 23, x_3);
lean_ctor_set(x_8, 24, x_3);
lean_ctor_set(x_8, 25, x_5);
lean_ctor_set(x_8, 26, x_6);
lean_ctor_set(x_8, 27, x_5);
lean_ctor_set(x_8, 28, x_5);
lean_ctor_set(x_8, 29, x_5);
lean_ctor_set(x_8, 30, x_5);
lean_ctor_set(x_8, 31, x_1);
lean_ctor_set(x_8, 32, x_6);
lean_ctor_set(x_8, 33, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*34, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__6;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1;
return x_1;
}
}
lean_object* initialize_Std_Internal_Rat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_CommRing_Poly(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExprPtr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Rat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_CommRing_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Linarith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExprPtr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types___hyg_10____closed__1);
l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__1);
l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean = _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean);
l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__1);
l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean = _init_l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__5 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__5);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__1);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__2);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__3();
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__4);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__5 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__5);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__6 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__6);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__7 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct___closed__7);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState___closed__1);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
