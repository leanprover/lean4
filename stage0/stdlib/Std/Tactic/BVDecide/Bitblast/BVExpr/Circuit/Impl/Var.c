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
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_nbuckets_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_58_ = lean_array_get_size(v_data_57_);
v___x_59_ = lean_unsigned_to_nat(2u);
v_nbuckets_60_ = lean_nat_mul(v___x_58_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_box(0);
v___x_63_ = lean_mk_array(v_nbuckets_60_, v___x_62_);
v___x_64_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v___x_61_, v_data_57_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(lean_object* v_a_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
uint8_t v___x_67_; 
lean_dec(v_a_65_);
v___x_67_ = 0;
return v___x_67_;
}
else
{
lean_object* v_key_68_; lean_object* v_tail_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_key_68_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_key_68_);
v_tail_69_ = lean_ctor_get(v_x_66_, 2);
lean_inc(v_tail_69_);
lean_dec_ref(v_x_66_);
v___x_70_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_65_);
v___x_71_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_70_, v_key_68_, v_a_65_);
if (v___x_71_ == 0)
{
v_x_66_ = v_tail_69_;
goto _start;
}
else
{
lean_dec(v_tail_69_);
lean_dec(v_a_65_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_a_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_73_, v_x_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(lean_object* v_a_77_, lean_object* v_b_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_dec(v_b_78_);
lean_dec(v_a_77_);
return v_x_79_;
}
else
{
lean_object* v_key_80_; lean_object* v_value_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_95_; 
v_key_80_ = lean_ctor_get(v_x_79_, 0);
v_value_81_ = lean_ctor_get(v_x_79_, 1);
v_tail_82_ = lean_ctor_get(v_x_79_, 2);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_95_ == 0)
{
v___x_84_ = v_x_79_;
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_value_81_);
lean_inc(v_key_80_);
lean_dec(v_x_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_77_);
lean_inc(v_key_80_);
v___x_87_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_86_, v_key_80_, v_a_77_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_77_, v_b_78_, v_tail_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 2, v___x_88_);
v___x_90_ = v___x_84_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_key_80_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_value_81_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
else
{
lean_object* v___x_93_; 
lean_dec(v_value_81_);
lean_dec(v_key_80_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_b_78_);
lean_ctor_set(v___x_84_, 0, v_a_77_);
v___x_93_ = v___x_84_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_77_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_b_78_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_tail_82_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(lean_object* v_m_96_, lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
lean_object* v_size_99_; lean_object* v_buckets_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_143_; 
v_size_99_ = lean_ctor_get(v_m_96_, 0);
v_buckets_100_ = lean_ctor_get(v_m_96_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_m_96_);
if (v_isSharedCheck_143_ == 0)
{
v___x_102_ = v_m_96_;
v_isShared_103_ = v_isSharedCheck_143_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_buckets_100_);
lean_inc(v_size_99_);
lean_dec(v_m_96_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_143_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v_fold_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; lean_object* v_bkt_117_; uint8_t v___x_118_; 
v___x_104_ = lean_array_get_size(v_buckets_100_);
v___x_105_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_97_);
v___x_106_ = 32ULL;
v___x_107_ = lean_uint64_shift_right(v___x_105_, v___x_106_);
v_fold_108_ = lean_uint64_xor(v___x_105_, v___x_107_);
v___x_109_ = 16ULL;
v___x_110_ = lean_uint64_shift_right(v_fold_108_, v___x_109_);
v___x_111_ = lean_uint64_xor(v_fold_108_, v___x_110_);
v___x_112_ = lean_uint64_to_usize(v___x_111_);
v___x_113_ = lean_usize_of_nat(v___x_104_);
v___x_114_ = ((size_t)1ULL);
v___x_115_ = lean_usize_sub(v___x_113_, v___x_114_);
v___x_116_ = lean_usize_land(v___x_112_, v___x_115_);
v_bkt_117_ = lean_array_uget_borrowed(v_buckets_100_, v___x_116_);
lean_inc(v_bkt_117_);
lean_inc(v_a_97_);
v___x_118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_97_, v_bkt_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v_size_x27_120_; lean_object* v___x_121_; lean_object* v_buckets_x27_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v_size_x27_120_ = lean_nat_add(v_size_99_, v___x_119_);
lean_dec(v_size_99_);
lean_inc(v_bkt_117_);
v___x_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_121_, 0, v_a_97_);
lean_ctor_set(v___x_121_, 1, v_b_98_);
lean_ctor_set(v___x_121_, 2, v_bkt_117_);
v_buckets_x27_122_ = lean_array_uset(v_buckets_100_, v___x_116_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(4u);
v___x_124_ = lean_nat_mul(v_size_x27_120_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(3u);
v___x_126_ = lean_nat_div(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_array_get_size(v_buckets_x27_122_);
v___x_128_ = lean_nat_dec_le(v___x_126_, v___x_127_);
lean_dec(v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v_val_129_; lean_object* v___x_131_; 
v_val_129_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_buckets_x27_122_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_val_129_);
lean_ctor_set(v___x_102_, 0, v_size_x27_120_);
v___x_131_ = v___x_102_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_val_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_134_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_buckets_x27_122_);
lean_ctor_set(v___x_102_, 0, v_size_x27_120_);
v___x_134_ = v___x_102_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_size_x27_120_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_buckets_x27_122_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v___x_136_; lean_object* v_buckets_x27_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
lean_inc(v_bkt_117_);
v___x_136_ = lean_box(0);
v_buckets_x27_137_ = lean_array_uset(v_buckets_100_, v___x_116_, v___x_136_);
v___x_138_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_97_, v_b_98_, v_bkt_117_);
v___x_139_ = lean_array_uset(v_buckets_x27_137_, v___x_116_, v___x_138_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_139_);
v___x_141_ = v___x_102_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_size_99_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(lean_object* v_a_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_146_; 
lean_dec(v_a_144_);
v___x_146_ = lean_box(0);
return v___x_146_;
}
else
{
lean_object* v_key_147_; lean_object* v_value_148_; lean_object* v_tail_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_key_147_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_key_147_);
v_value_148_ = lean_ctor_get(v_x_145_, 1);
lean_inc(v_value_148_);
v_tail_149_ = lean_ctor_get(v_x_145_, 2);
lean_inc(v_tail_149_);
lean_dec_ref(v_x_145_);
v___x_150_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_144_);
v___x_151_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_150_, v_key_147_, v_a_144_);
if (v___x_151_ == 0)
{
lean_dec(v_value_148_);
v_x_145_ = v_tail_149_;
goto _start;
}
else
{
lean_object* v___x_153_; 
lean_dec(v_tail_149_);
lean_dec(v_a_144_);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v_value_148_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(lean_object* v_m_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_buckets_156_; lean_object* v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v_fold_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_buckets_156_ = lean_ctor_get(v_m_154_, 1);
v___x_157_ = lean_array_get_size(v_buckets_156_);
v___x_158_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_155_);
v___x_159_ = 32ULL;
v___x_160_ = lean_uint64_shift_right(v___x_158_, v___x_159_);
v_fold_161_ = lean_uint64_xor(v___x_158_, v___x_160_);
v___x_162_ = 16ULL;
v___x_163_ = lean_uint64_shift_right(v_fold_161_, v___x_162_);
v___x_164_ = lean_uint64_xor(v_fold_161_, v___x_163_);
v___x_165_ = lean_uint64_to_usize(v___x_164_);
v___x_166_ = lean_usize_of_nat(v___x_157_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_sub(v___x_166_, v___x_167_);
v___x_169_ = lean_usize_land(v___x_165_, v___x_168_);
v___x_170_ = lean_array_uget_borrowed(v_buckets_156_, v___x_169_);
lean_inc(v___x_170_);
v___x_171_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_155_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_172_, v_a_173_);
lean_dec_ref(v_m_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(lean_object* v_aig_175_, lean_object* v_n_176_){
_start:
{
lean_object* v_decls_177_; lean_object* v_cache_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_200_; 
v_decls_177_ = lean_ctor_get(v_aig_175_, 0);
v_cache_178_ = lean_ctor_get(v_aig_175_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_aig_175_);
if (v_isSharedCheck_200_ == 0)
{
v___x_180_ = v_aig_175_;
v_isShared_181_ = v_isSharedCheck_200_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_cache_178_);
lean_inc(v_decls_177_);
lean_dec(v_aig_175_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_200_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_decl_182_; lean_object* v___x_183_; 
v_decl_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_182_, 0, v_n_176_);
lean_inc_ref(v_decl_182_);
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_cache_178_, v_decl_182_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_g_184_; lean_object* v_cache_185_; lean_object* v_decls_186_; lean_object* v___x_188_; 
v_g_184_ = lean_array_get_size(v_decls_177_);
lean_inc_ref(v_decl_182_);
v_cache_185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_cache_178_, v_decl_182_, v_g_184_);
v_decls_186_ = lean_array_push(v_decls_177_, v_decl_182_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v_cache_185_);
lean_ctor_set(v___x_180_, 0, v_decls_186_);
v___x_188_ = v___x_180_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_decls_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_cache_185_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_190_, 0, v_g_184_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_188_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
return v___x_191_;
}
}
else
{
lean_object* v_val_193_; lean_object* v___x_195_; 
lean_dec_ref(v_decl_182_);
v_val_193_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_val_193_);
lean_dec_ref(v___x_183_);
if (v_isShared_181_ == 0)
{
v___x_195_ = v___x_180_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_decls_177_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_cache_178_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = 0;
v___x_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_197_, 0, v_val_193_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_195_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_201_; lean_object* v___x_202_; 
v___x_201_ = 0;
v___x_202_ = l_Bool_toNat(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(lean_object* v_aig_203_, lean_object* v_w_204_, lean_object* v_a_205_, lean_object* v_curr_206_, lean_object* v_s_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = lean_nat_dec_lt(v_curr_206_, v_w_204_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec(v_curr_206_);
lean_dec(v_a_205_);
lean_dec(v_w_204_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_aig_203_);
lean_ctor_set(v___x_209_, 1, v_s_207_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v_res_211_; lean_object* v_ref_212_; lean_object* v_aig_213_; lean_object* v_gate_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_s_221_; 
lean_inc(v_curr_206_);
lean_inc(v_w_204_);
lean_inc(v_a_205_);
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v_a_205_);
lean_ctor_set(v___x_210_, 1, v_w_204_);
lean_ctor_set(v___x_210_, 2, v_curr_206_);
v_res_211_ = l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(v_aig_203_, v___x_210_);
v_ref_212_ = lean_ctor_get(v_res_211_, 1);
lean_inc_ref(v_ref_212_);
v_aig_213_ = lean_ctor_get(v_res_211_, 0);
lean_inc_ref(v_aig_213_);
lean_dec_ref(v_res_211_);
v_gate_214_ = lean_ctor_get(v_ref_212_, 0);
lean_inc(v_gate_214_);
lean_dec_ref(v_ref_212_);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_curr_206_, v___x_215_);
lean_dec(v_curr_206_);
v___x_217_ = lean_unsigned_to_nat(2u);
v___x_218_ = lean_nat_mul(v_gate_214_, v___x_217_);
lean_dec(v_gate_214_);
v___x_219_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0);
v___x_220_ = lean_nat_lor(v___x_218_, v___x_219_);
lean_dec(v___x_218_);
v_s_221_ = lean_array_push(v_s_207_, v___x_220_);
v_aig_203_ = v_aig_213_;
v_curr_206_ = v___x_216_;
v_s_207_ = v_s_221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object* v_aig_223_, lean_object* v_w_224_, lean_object* v_a_225_, lean_object* v_curr_226_, lean_object* v_s_227_, lean_object* v_hcurr_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_223_, v_w_224_, v_a_225_, v_curr_226_, v_s_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(lean_object* v_00_u03b2_230_, lean_object* v_m_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_231_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_234_, lean_object* v_m_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(v_00_u03b2_234_, v_m_235_, v_a_236_);
lean_dec_ref(v_m_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(lean_object* v_00_u03b2_238_, lean_object* v_m_239_, lean_object* v_a_240_, lean_object* v_b_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_m_239_, v_a_240_, v_b_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_243_, lean_object* v_a_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_244_, v_x_245_);
return v___x_246_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_247_, lean_object* v_a_248_, lean_object* v_x_249_){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_248_, v_x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_251_, lean_object* v_a_252_, lean_object* v_x_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(v_00_u03b2_251_, v_a_252_, v_x_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_256_, lean_object* v_data_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_data_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_259_, lean_object* v_a_260_, lean_object* v_b_261_, lean_object* v_x_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_260_, v_b_261_, v_x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_264_, lean_object* v_i_265_, lean_object* v_source_266_, lean_object* v_target_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v_i_265_, v_source_266_, v_target_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_x_270_, v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(lean_object* v_c_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_mk_empty_array_with_capacity(v_c_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg___boxed(lean_object* v_c_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(v_c_275_);
lean_dec(v_c_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(lean_object* v_aig_277_, lean_object* v_c_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_mk_empty_array_with_capacity(v_c_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___boxed(lean_object* v_aig_280_, lean_object* v_c_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(v_aig_280_, v_c_281_);
lean_dec(v_c_281_);
lean_dec_ref(v_aig_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object* v_w_283_, lean_object* v_aig_284_, lean_object* v_var_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_mk_empty_array_with_capacity(v_w_283_);
v___x_288_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_284_, v_w_283_, v_var_285_, v___x_286_, v___x_287_);
return v___x_288_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
