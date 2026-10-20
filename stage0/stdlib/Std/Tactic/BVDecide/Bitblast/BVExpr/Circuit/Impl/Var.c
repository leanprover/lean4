// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
uint64_t v___x_2_; 
v___x_2_ = 0ULL;
return v___x_2_;
}
case 1:
{
lean_object* v_idx_3_; uint64_t v___x_4_; uint64_t v___x_5_; uint64_t v___x_6_; 
v_idx_3_ = lean_ctor_get(v_x_1_, 0);
v___x_4_ = 1ULL;
v___x_5_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_3_);
v___x_6_ = lean_uint64_mix_hash(v___x_4_, v___x_5_);
return v___x_6_;
}
default: 
{
lean_object* v_l_7_; lean_object* v_r_8_; uint64_t v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v___x_13_; 
v_l_7_ = lean_ctor_get(v_x_1_, 0);
v_r_8_ = lean_ctor_get(v_x_1_, 1);
v___x_9_ = 2ULL;
v___x_10_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_7_);
v___x_11_ = lean_uint64_mix_hash(v___x_9_, v___x_10_);
v___x_12_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_8_);
v___x_13_ = lean_uint64_mix_hash(v___x_11_, v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___boxed(lean_object* v_x_14_){
_start:
{
uint64_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_x_14_);
lean_dec(v_x_14_);
v_r_16_ = lean_box_uint64(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
return v_x_17_;
}
else
{
lean_object* v_key_19_; lean_object* v_value_20_; lean_object* v_tail_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_44_; 
v_key_19_ = lean_ctor_get(v_x_18_, 0);
v_value_20_ = lean_ctor_get(v_x_18_, 1);
v_tail_21_ = lean_ctor_get(v_x_18_, 2);
v_isSharedCheck_44_ = !lean_is_exclusive(v_x_18_);
if (v_isSharedCheck_44_ == 0)
{
v___x_23_ = v_x_18_;
v_isShared_24_ = v_isSharedCheck_44_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_tail_21_);
lean_inc(v_value_20_);
lean_inc(v_key_19_);
lean_dec(v_x_18_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_44_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v_fold_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_25_ = lean_array_get_size(v_x_17_);
v___x_26_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_key_19_);
v___x_27_ = 32ULL;
v___x_28_ = lean_uint64_shift_right(v___x_26_, v___x_27_);
v_fold_29_ = lean_uint64_xor(v___x_26_, v___x_28_);
v___x_30_ = 16ULL;
v___x_31_ = lean_uint64_shift_right(v_fold_29_, v___x_30_);
v___x_32_ = lean_uint64_xor(v_fold_29_, v___x_31_);
v___x_33_ = lean_uint64_to_usize(v___x_32_);
v___x_34_ = lean_usize_of_nat(v___x_25_);
v___x_35_ = ((size_t)1ULL);
v___x_36_ = lean_usize_sub(v___x_34_, v___x_35_);
v___x_37_ = lean_usize_land(v___x_33_, v___x_36_);
v___x_38_ = lean_array_uget_borrowed(v_x_17_, v___x_37_);
lean_inc(v___x_38_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 2, v___x_38_);
v___x_40_ = v___x_23_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_key_19_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_value_20_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v___x_38_);
v___x_40_ = v_reuseFailAlloc_43_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = lean_array_uset(v_x_17_, v___x_37_, v___x_40_);
v_x_17_ = v___x_41_;
v_x_18_ = v_tail_21_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(lean_object* v_i_45_, lean_object* v_source_46_, lean_object* v_target_47_){
_start:
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_array_get_size(v_source_46_);
v___x_49_ = lean_nat_dec_lt(v_i_45_, v___x_48_);
if (v___x_49_ == 0)
{
lean_dec_ref(v_source_46_);
lean_dec(v_i_45_);
return v_target_47_;
}
else
{
lean_object* v_es_50_; lean_object* v___x_51_; lean_object* v_source_52_; lean_object* v_target_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_es_50_ = lean_array_fget(v_source_46_, v_i_45_);
v___x_51_ = lean_box(0);
v_source_52_ = lean_array_fset(v_source_46_, v_i_45_, v___x_51_);
v_target_53_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_target_47_, v_es_50_);
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = lean_nat_add(v_i_45_, v___x_54_);
lean_dec(v_i_45_);
v_i_45_ = v___x_55_;
v_source_46_ = v_source_52_;
v_target_47_ = v_target_53_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(lean_object* v_data_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_nbuckets_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_58_ = lean_array_get_size(v_data_57_);
v___x_59_ = lean_unsigned_to_nat(2u);
v_nbuckets_60_ = lean_nat_mul(v___x_58_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_box(0);
v___x_63_ = lean_mk_array(v_nbuckets_60_, v___x_62_);
v___x_64_ = lean_array_propagate_mark(v_data_57_, v___x_63_);
v___x_65_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v___x_61_, v_data_57_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(lean_object* v_a_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
uint8_t v___x_68_; 
lean_dec(v_a_66_);
v___x_68_ = 0;
return v___x_68_;
}
else
{
lean_object* v_key_69_; lean_object* v_tail_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_key_69_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_key_69_);
v_tail_70_ = lean_ctor_get(v_x_67_, 2);
lean_inc(v_tail_70_);
lean_dec_ref_known(v_x_67_, 3);
v___x_71_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_66_);
v___x_72_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_71_, v_key_69_, v_a_66_);
if (v___x_72_ == 0)
{
v_x_67_ = v_tail_70_;
goto _start;
}
else
{
lean_dec(v_tail_70_);
lean_dec(v_a_66_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_a_74_, lean_object* v_x_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_74_, v_x_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(lean_object* v_a_78_, lean_object* v_b_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_dec(v_b_79_);
lean_dec(v_a_78_);
return v_x_80_;
}
else
{
lean_object* v_key_81_; lean_object* v_value_82_; lean_object* v_tail_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_96_; 
v_key_81_ = lean_ctor_get(v_x_80_, 0);
v_value_82_ = lean_ctor_get(v_x_80_, 1);
v_tail_83_ = lean_ctor_get(v_x_80_, 2);
v_isSharedCheck_96_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_96_ == 0)
{
v___x_85_ = v_x_80_;
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_tail_83_);
lean_inc(v_value_82_);
lean_inc(v_key_81_);
lean_dec(v_x_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_78_);
lean_inc(v_key_81_);
v___x_88_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_87_, v_key_81_, v_a_78_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_78_, v_b_79_, v_tail_83_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 2, v___x_89_);
v___x_91_ = v___x_85_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_key_81_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_value_82_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
else
{
lean_object* v___x_94_; 
lean_dec(v_value_82_);
lean_dec(v_key_81_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_b_79_);
lean_ctor_set(v___x_85_, 0, v_a_78_);
v___x_94_ = v___x_85_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_78_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_b_79_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_tail_83_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(lean_object* v_m_97_, lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
lean_object* v_size_100_; lean_object* v_buckets_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_144_; 
v_size_100_ = lean_ctor_get(v_m_97_, 0);
v_buckets_101_ = lean_ctor_get(v_m_97_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_m_97_);
if (v_isSharedCheck_144_ == 0)
{
v___x_103_ = v_m_97_;
v_isShared_104_ = v_isSharedCheck_144_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_buckets_101_);
lean_inc(v_size_100_);
lean_dec(v_m_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_144_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v_fold_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; lean_object* v_bkt_118_; uint8_t v___x_119_; 
v___x_105_ = lean_array_get_size(v_buckets_101_);
v___x_106_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_98_);
v___x_107_ = 32ULL;
v___x_108_ = lean_uint64_shift_right(v___x_106_, v___x_107_);
v_fold_109_ = lean_uint64_xor(v___x_106_, v___x_108_);
v___x_110_ = 16ULL;
v___x_111_ = lean_uint64_shift_right(v_fold_109_, v___x_110_);
v___x_112_ = lean_uint64_xor(v_fold_109_, v___x_111_);
v___x_113_ = lean_uint64_to_usize(v___x_112_);
v___x_114_ = lean_usize_of_nat(v___x_105_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_sub(v___x_114_, v___x_115_);
v___x_117_ = lean_usize_land(v___x_113_, v___x_116_);
v_bkt_118_ = lean_array_uget_borrowed(v_buckets_101_, v___x_117_);
lean_inc(v_bkt_118_);
lean_inc(v_a_98_);
v___x_119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_98_, v_bkt_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_size_x27_121_; lean_object* v___x_122_; lean_object* v_buckets_x27_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v_size_x27_121_ = lean_nat_add(v_size_100_, v___x_120_);
lean_dec(v_size_100_);
lean_inc(v_bkt_118_);
v___x_122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_122_, 0, v_a_98_);
lean_ctor_set(v___x_122_, 1, v_b_99_);
lean_ctor_set(v___x_122_, 2, v_bkt_118_);
v_buckets_x27_123_ = lean_array_uset(v_buckets_101_, v___x_117_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(4u);
v___x_125_ = lean_nat_mul(v_size_x27_121_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(3u);
v___x_127_ = lean_nat_div(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_array_get_size(v_buckets_x27_123_);
v___x_129_ = lean_nat_dec_le(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v_val_130_; lean_object* v___x_132_; 
v_val_130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_buckets_x27_123_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_val_130_);
lean_ctor_set(v___x_103_, 0, v_size_x27_121_);
v___x_132_ = v___x_103_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_val_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_135_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_buckets_x27_123_);
lean_ctor_set(v___x_103_, 0, v_size_x27_121_);
v___x_135_ = v___x_103_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_size_x27_121_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_buckets_x27_123_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v___x_137_; lean_object* v_buckets_x27_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
lean_inc(v_bkt_118_);
v___x_137_ = lean_box(0);
v_buckets_x27_138_ = lean_array_uset(v_buckets_101_, v___x_117_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_98_, v_b_99_, v_bkt_118_);
v___x_140_ = lean_array_uset(v_buckets_x27_138_, v___x_117_, v___x_139_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_140_);
v___x_142_ = v___x_103_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_size_100_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(lean_object* v_a_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_147_; 
lean_dec(v_a_145_);
v___x_147_ = lean_box(0);
return v___x_147_;
}
else
{
lean_object* v_key_148_; lean_object* v_value_149_; lean_object* v_tail_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_key_148_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_key_148_);
v_value_149_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_value_149_);
v_tail_150_ = lean_ctor_get(v_x_146_, 2);
lean_inc(v_tail_150_);
lean_dec_ref_known(v_x_146_, 3);
v___x_151_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_145_);
v___x_152_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_151_, v_key_148_, v_a_145_);
if (v___x_152_ == 0)
{
lean_dec(v_value_149_);
v_x_146_ = v_tail_150_;
goto _start;
}
else
{
lean_object* v___x_154_; 
lean_dec(v_tail_150_);
lean_dec(v_a_145_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v_value_149_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(lean_object* v_m_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_buckets_157_; lean_object* v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v_fold_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; size_t v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_buckets_157_ = lean_ctor_get(v_m_155_, 1);
v___x_158_ = lean_array_get_size(v_buckets_157_);
v___x_159_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_156_);
v___x_160_ = 32ULL;
v___x_161_ = lean_uint64_shift_right(v___x_159_, v___x_160_);
v_fold_162_ = lean_uint64_xor(v___x_159_, v___x_161_);
v___x_163_ = 16ULL;
v___x_164_ = lean_uint64_shift_right(v_fold_162_, v___x_163_);
v___x_165_ = lean_uint64_xor(v_fold_162_, v___x_164_);
v___x_166_ = lean_uint64_to_usize(v___x_165_);
v___x_167_ = lean_usize_of_nat(v___x_158_);
v___x_168_ = ((size_t)1ULL);
v___x_169_ = lean_usize_sub(v___x_167_, v___x_168_);
v___x_170_ = lean_usize_land(v___x_166_, v___x_169_);
v___x_171_ = lean_array_uget_borrowed(v_buckets_157_, v___x_170_);
lean_inc(v___x_171_);
v___x_172_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_156_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_173_, v_a_174_);
lean_dec_ref(v_m_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(lean_object* v_aig_176_, lean_object* v_n_177_){
_start:
{
lean_object* v_decls_178_; lean_object* v_cache_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_201_; 
v_decls_178_ = lean_ctor_get(v_aig_176_, 0);
v_cache_179_ = lean_ctor_get(v_aig_176_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_aig_176_);
if (v_isSharedCheck_201_ == 0)
{
v___x_181_ = v_aig_176_;
v_isShared_182_ = v_isSharedCheck_201_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_cache_179_);
lean_inc(v_decls_178_);
lean_dec(v_aig_176_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_201_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_decl_183_; lean_object* v___x_184_; 
v_decl_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_183_, 0, v_n_177_);
lean_inc_ref(v_decl_183_);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_cache_179_, v_decl_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_g_185_; lean_object* v_cache_186_; lean_object* v_decls_187_; lean_object* v___x_189_; 
v_g_185_ = lean_array_get_size(v_decls_178_);
lean_inc_ref(v_decl_183_);
v_cache_186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_cache_179_, v_decl_183_, v_g_185_);
v_decls_187_ = lean_array_push(v_decls_178_, v_decl_183_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_cache_186_);
lean_ctor_set(v___x_181_, 0, v_decls_187_);
v___x_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_decls_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_cache_186_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = 0;
v___x_191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_191_, 0, v_g_185_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_189_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
return v___x_192_;
}
}
else
{
lean_object* v_val_194_; lean_object* v___x_196_; 
lean_dec_ref_known(v_decl_183_, 1);
v_val_194_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v___x_184_, 1);
if (v_isShared_182_ == 0)
{
v___x_196_ = v___x_181_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_decls_178_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_cache_179_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = 0;
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v_val_194_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_196_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_202_; lean_object* v___x_203_; 
v___x_202_ = 0;
v___x_203_ = l_Bool_toNat(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(lean_object* v_aig_204_, lean_object* v_w_205_, lean_object* v_a_206_, lean_object* v_curr_207_, lean_object* v_s_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_lt(v_curr_207_, v_w_205_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec(v_curr_207_);
lean_dec(v_a_206_);
lean_dec(v_w_205_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_aig_204_);
lean_ctor_set(v___x_210_, 1, v_s_208_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v_res_212_; lean_object* v_ref_213_; lean_object* v_aig_214_; lean_object* v_gate_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_s_222_; 
lean_inc(v_curr_207_);
lean_inc(v_w_205_);
lean_inc(v_a_206_);
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v_a_206_);
lean_ctor_set(v___x_211_, 1, v_w_205_);
lean_ctor_set(v___x_211_, 2, v_curr_207_);
v_res_212_ = l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(v_aig_204_, v___x_211_);
v_ref_213_ = lean_ctor_get(v_res_212_, 1);
lean_inc_ref(v_ref_213_);
v_aig_214_ = lean_ctor_get(v_res_212_, 0);
lean_inc_ref(v_aig_214_);
lean_dec_ref(v_res_212_);
v_gate_215_ = lean_ctor_get(v_ref_213_, 0);
lean_inc(v_gate_215_);
lean_dec_ref(v_ref_213_);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_curr_207_, v___x_216_);
lean_dec(v_curr_207_);
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_nat_mul(v_gate_215_, v___x_218_);
lean_dec(v_gate_215_);
v___x_220_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0);
v___x_221_ = lean_nat_lor(v___x_219_, v___x_220_);
lean_dec(v___x_219_);
v_s_222_ = lean_array_push(v_s_208_, v___x_221_);
v_aig_204_ = v_aig_214_;
v_curr_207_ = v___x_217_;
v_s_208_ = v_s_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object* v_aig_224_, lean_object* v_w_225_, lean_object* v_a_226_, lean_object* v_curr_227_, lean_object* v_s_228_, lean_object* v_hcurr_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_224_, v_w_225_, v_a_226_, v_curr_227_, v_s_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(lean_object* v_00_u03b2_231_, lean_object* v_m_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_232_, v_a_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_235_, lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(v_00_u03b2_235_, v_m_236_, v_a_237_);
lean_dec_ref(v_m_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(lean_object* v_00_u03b2_239_, lean_object* v_m_240_, lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_m_240_, v_a_241_, v_b_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_244_, lean_object* v_a_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_245_, v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_248_, lean_object* v_a_249_, lean_object* v_x_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_249_, v_x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_252_, lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(v_00_u03b2_252_, v_a_253_, v_x_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_257_, lean_object* v_data_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_data_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_260_, lean_object* v_a_261_, lean_object* v_b_262_, lean_object* v_x_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_261_, v_b_262_, v_x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_265_, lean_object* v_i_266_, lean_object* v_source_267_, lean_object* v_target_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v_i_266_, v_source_267_, v_target_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_x_271_, v_x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(lean_object* v_c_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_mk_empty_array_with_capacity(v_c_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg___boxed(lean_object* v_c_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(v_c_276_);
lean_dec(v_c_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(lean_object* v_aig_278_, lean_object* v_c_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_mk_empty_array_with_capacity(v_c_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___boxed(lean_object* v_aig_281_, lean_object* v_c_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(v_aig_281_, v_c_282_);
lean_dec(v_c_282_);
lean_dec_ref(v_aig_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object* v_w_284_, lean_object* v_aig_285_, lean_object* v_var_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_mk_empty_array_with_capacity(v_w_284_);
v___x_289_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_285_, v_w_284_, v_var_286_, v___x_287_, v___x_288_);
return v___x_289_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
}
#ifdef __cplusplus
}
#endif
