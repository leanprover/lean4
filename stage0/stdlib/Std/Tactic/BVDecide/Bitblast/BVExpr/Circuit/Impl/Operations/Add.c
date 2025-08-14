// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.CachedGatesLemmas Std.Sat.AIG.LawfulVecOperator
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(lean_object*);
lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_ctor_set(x_7, 0, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_10);
lean_ctor_set(x_3, 0, x_11);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_12);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_14);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_16);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_25 = x_18;
} else {
 lean_dec_ref(x_18);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 1, 1);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_20);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_22);
lean_ctor_set(x_3, 0, x_23);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_24);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_30);
lean_dec(x_3);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_34 = x_28;
} else {
 lean_dec_ref(x_28);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_31);
if (lean_is_scalar(x_34)) {
 x_39 = lean_alloc_ctor(0, 1, 1);
} else {
 x_39 = x_34;
}
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_33);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_36);
lean_ctor_set(x_1, 2, x_40);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_38);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_46 = x_41;
} else {
 lean_dec_ref(x_41);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 1);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_45);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_48);
if (lean_is_scalar(x_46)) {
 x_55 = lean_alloc_ctor(0, 1, 1);
} else {
 x_55 = x_46;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_51);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_13);
x_14 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_12, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_16);
x_20 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_15, x_9);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_25 = x_7;
} else {
 lean_dec_ref(x_7);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 1, 1);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_21, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_15);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_20 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_14, x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_ctor_set(x_6, 0, x_16);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_17);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_19);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 0, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_24 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_22, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_24, 0, x_23);
x_28 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_27, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
lean_ctor_set(x_24, 0, x_32);
x_33 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_29, x_24);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_38 = x_23;
} else {
 lean_dec_ref(x_23);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 1, 1);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_34, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
lean_ctor_set(x_6, 0, x_16);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_17);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_19);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_45 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_42, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_50);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
x_54 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_46, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_55 = lean_ctor_get(x_9, 0);
x_56 = lean_ctor_get(x_9, 1);
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_59 = lean_ctor_get(x_6, 0);
x_60 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_61);
lean_dec(x_7);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
lean_ctor_set(x_9, 1, x_63);
lean_ctor_set(x_9, 0, x_56);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_64 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_55, x_9);
x_65 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
lean_ctor_set(x_6, 0, x_57);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_58);
lean_ctor_set(x_5, 0, x_59);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_60);
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_6);
lean_ctor_set(x_68, 1, x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_69 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_65, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_75 = x_66;
} else {
 lean_dec_ref(x_66);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_74);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
x_78 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_70, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_79 = lean_ctor_get(x_9, 0);
x_80 = lean_ctor_get(x_9, 1);
x_81 = lean_ctor_get(x_5, 0);
x_82 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_83 = lean_ctor_get(x_6, 0);
x_84 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_83);
lean_dec(x_6);
x_85 = lean_ctor_get(x_7, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_87 = x_7;
} else {
 lean_dec_ref(x_7);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_86);
lean_ctor_set(x_9, 1, x_88);
lean_ctor_set(x_9, 0, x_80);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_89 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_79, x_9);
x_90 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_82);
lean_ctor_set(x_5, 0, x_83);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_84);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_95 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_90, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc_ref(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_91, sizeof(void*)*1);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_101 = x_91;
} else {
 lean_dec_ref(x_91);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 1, 1);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_100);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
x_104 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_96, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_105 = lean_ctor_get(x_9, 0);
x_106 = lean_ctor_get(x_9, 1);
x_107 = lean_ctor_get(x_5, 0);
x_108 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_inc(x_107);
lean_dec(x_5);
x_109 = lean_ctor_get(x_6, 0);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_111 = x_6;
} else {
 lean_dec_ref(x_6);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_7, 0);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_114 = x_7;
} else {
 lean_dec_ref(x_7);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 1, 1);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_113);
lean_ctor_set(x_9, 1, x_115);
lean_ctor_set(x_9, 0, x_106);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_116 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_105, x_9);
x_117 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc_ref(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_120 = lean_alloc_ctor(0, 1, 1);
} else {
 x_120 = x_111;
}
lean_ctor_set(x_120, 0, x_107);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_108);
x_121 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_121, 0, x_109);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_110);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_123 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_117, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc_ref(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_118, 0);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_129 = x_118;
} else {
 lean_dec_ref(x_118);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 1, 1);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_128);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_125);
x_132 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_124, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_133 = lean_ctor_get(x_9, 0);
x_134 = lean_ctor_get(x_9, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_9);
x_135 = lean_ctor_get(x_5, 0);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_137 = x_5;
} else {
 lean_dec_ref(x_5);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_6, 0);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_140 = x_6;
} else {
 lean_dec_ref(x_6);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_7, 0);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_143 = x_7;
} else {
 lean_dec_ref(x_7);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 1, 1);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_134);
lean_ctor_set(x_145, 1, x_144);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_146 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_133, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc_ref(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(0, 1, 1);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_135);
lean_ctor_set_uint8(x_150, sizeof(void*)*1, x_136);
if (lean_is_scalar(x_137)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_137;
}
lean_ctor_set(x_151, 0, x_138);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_139);
if (lean_is_scalar(x_149)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_149;
}
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_153 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_147, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc_ref(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_148, 0);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_148, sizeof(void*)*1);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_159 = x_148;
} else {
 lean_dec_ref(x_148);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 1, 1);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_158);
if (lean_is_scalar(x_156)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_156;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_155);
x_162 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_154, x_161);
return x_162;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(x_4);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(x_1, x_2, x_6, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_9);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_28; lean_object* x_29; 
x_28 = lean_nat_dec_lt(x_7, x_3);
if (x_28 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_array_fget_borrowed(x_5, x_7);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_shiftr(x_41, x_42);
x_44 = lean_nat_land(x_42, x_41);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_28);
x_29 = x_47;
goto block_39;
}
else
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_29 = x_49;
goto block_39;
}
}
block_27:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(x_1, x_2, x_4, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec_ref(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_mul(x_17, x_21);
lean_dec(x_17);
x_23 = l_Bool_toNat(x_18);
x_24 = lean_nat_lor(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_array_push(x_9, x_24);
x_4 = x_15;
x_7 = x_20;
x_8 = x_16;
x_9 = x_25;
goto _start;
}
block_39:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_array_fget_borrowed(x_6, x_7);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_shiftr(x_30, x_31);
x_33 = lean_nat_land(x_31, x_30);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_28);
x_10 = x_29;
x_11 = x_36;
goto block_27;
}
else
{
uint8_t x_37; lean_object* x_38; 
x_37 = 0;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_10 = x_29;
x_11 = x_38;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0;
x_10 = lean_mk_empty_array_with_capacity(x_3);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_Std_Sat_AIG_RefVec_countKnown___redArg(x_3, x_4, x_6);
x_9 = l_Std_Sat_AIG_RefVec_countKnown___redArg(x_3, x_4, x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_5, 0);
lean_dec(x_13);
lean_ctor_set(x_5, 1, x_6);
lean_ctor_set(x_5, 0, x_7);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_6);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_1, x_2, x_3, x_4, x_15);
lean_dec_ref(x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
