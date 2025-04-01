// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5___boxed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4___boxed(lean_object*, lean_object*);
uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___boxed(lean_object*);
static lean_object* l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__6(lean_object*);
uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__10(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___rarg___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__8___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__9(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2(lean_object* x_1) {
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
x_5 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = 2;
x_10 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashFanin____x40_Std_Sat_AIG_Basic___hyg_36_(x_8);
x_13 = lean_uint64_mix_hash(x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_nat_dec_eq(x_9, x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_10, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__8___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2(x_4);
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
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2(x_22);
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
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__8___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__9(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__7(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__10(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__10(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
static lean_object* _init_l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2(x_6);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_8, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__3(x_6, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_5, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 0);
lean_dec(x_26);
x_27 = lean_array_get_size(x_4);
lean_inc(x_6);
x_28 = lean_array_push(x_4, x_6);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5(x_6, x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_7, x_30);
lean_dec(x_7);
lean_inc(x_27);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_22);
x_33 = lean_array_uset(x_8, x_21, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__6(x_33);
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_31);
lean_ctor_set(x_1, 0, x_28);
x_41 = 0;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_31);
lean_ctor_set(x_1, 0, x_28);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_box(0);
x_48 = lean_array_uset(x_8, x_21, x_47);
lean_inc(x_27);
x_49 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__10(x_6, x_27, x_22);
x_50 = lean_array_uset(x_48, x_21, x_49);
lean_ctor_set(x_5, 1, x_50);
lean_ctor_set(x_1, 0, x_28);
x_51 = 0;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_5);
x_54 = lean_array_get_size(x_4);
lean_inc(x_6);
x_55 = lean_array_push(x_4, x_6);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5(x_6, x_22);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_7, x_57);
lean_dec(x_7);
lean_inc(x_54);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set(x_59, 2, x_22);
x_60 = lean_array_uset(x_8, x_21, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__6(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_55);
x_69 = 0;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_60);
lean_ctor_set(x_1, 1, x_72);
lean_ctor_set(x_1, 0, x_55);
x_73 = 0;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_box(0);
x_77 = lean_array_uset(x_8, x_21, x_76);
lean_inc(x_54);
x_78 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__10(x_6, x_54, x_22);
x_79 = lean_array_uset(x_77, x_21, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_7);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_1, 1, x_80);
lean_ctor_set(x_1, 0, x_55);
x_81 = 0;
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_54);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_84 = lean_ctor_get(x_23, 0);
lean_inc(x_84);
lean_dec(x_23);
x_85 = 0;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; size_t x_101; size_t x_102; size_t x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; 
x_88 = lean_ctor_get(x_1, 0);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_1);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_2);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
x_93 = lean_array_get_size(x_92);
x_94 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2(x_90);
x_95 = 32;
x_96 = lean_uint64_shift_right(x_94, x_95);
x_97 = lean_uint64_xor(x_94, x_96);
x_98 = 16;
x_99 = lean_uint64_shift_right(x_97, x_98);
x_100 = lean_uint64_xor(x_97, x_99);
x_101 = lean_uint64_to_usize(x_100);
x_102 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_103 = 1;
x_104 = lean_usize_sub(x_102, x_103);
x_105 = lean_usize_land(x_101, x_104);
x_106 = lean_array_uget(x_92, x_105);
x_107 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__3(x_90, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_108 = x_89;
} else {
 lean_dec_ref(x_89);
 x_108 = lean_box(0);
}
x_109 = lean_array_get_size(x_88);
lean_inc(x_90);
x_110 = lean_array_push(x_88, x_90);
x_111 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5(x_90, x_106);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_91, x_112);
lean_dec(x_91);
lean_inc(x_109);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_90);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_106);
x_115 = lean_array_uset(x_92, x_105, x_114);
x_116 = lean_unsigned_to_nat(4u);
x_117 = lean_nat_mul(x_113, x_116);
x_118 = lean_unsigned_to_nat(3u);
x_119 = lean_nat_div(x_117, x_118);
lean_dec(x_117);
x_120 = lean_array_get_size(x_115);
x_121 = lean_nat_dec_le(x_119, x_120);
lean_dec(x_120);
lean_dec(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_122 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__6(x_115);
if (lean_is_scalar(x_108)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_108;
}
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_123);
x_125 = 0;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_109);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
if (lean_is_scalar(x_108)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_108;
}
lean_ctor_set(x_128, 0, x_113);
lean_ctor_set(x_128, 1, x_115);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_110);
lean_ctor_set(x_129, 1, x_128);
x_130 = 0;
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_109);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_box(0);
x_134 = lean_array_uset(x_92, x_105, x_133);
lean_inc(x_109);
x_135 = l_Std_DHashMap_Internal_AssocList_replace___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__10(x_90, x_109, x_106);
x_136 = lean_array_uset(x_134, x_105, x_135);
if (lean_is_scalar(x_108)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_108;
}
lean_ctor_set(x_137, 0, x_91);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_110);
lean_ctor_set(x_138, 1, x_137);
x_139 = 0;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_109);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
x_142 = lean_ctor_get(x_107, 0);
lean_inc(x_142);
lean_dec(x_107);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_88);
lean_ctor_set(x_143, 1, x_89);
x_144 = 0;
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_4, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_4);
x_10 = l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_mul(x_15, x_17);
lean_dec(x_15);
x_19 = l_Bool_toNat(x_16);
x_20 = lean_nat_lor(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_array_push(x_5, x_20);
x_1 = x_11;
x_4 = x_14;
x_5 = x_21;
x_6 = lean_box(0);
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__2(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl____x40_Std_Sat_AIG_Basic___hyg_793____at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_mk_empty_array_with_capacity(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(x_2, x_1, x_3, x_5, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(uint8_t builtin, lean_object* w) {
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
l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1___closed__1 = _init_l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_mkAtomCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___spec__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
