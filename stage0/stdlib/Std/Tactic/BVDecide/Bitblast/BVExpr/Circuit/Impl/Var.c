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
uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(lean_object* v_x_1_){
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
LEAN_EXPORT void l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint64_t v_res_14_;
v_res_14_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_x_1_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___boxed(lean_object* v_x_15_){
_start:
{
uint64_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_x_15_);
lean_dec(v_x_15_);
v_r_17_ = lean_box_uint64(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
return v_x_18_;
}
else
{
lean_object* v_key_20_; lean_object* v_value_21_; lean_object* v_tail_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_45_; 
v_key_20_ = lean_ctor_get(v_x_19_, 0);
v_value_21_ = lean_ctor_get(v_x_19_, 1);
v_tail_22_ = lean_ctor_get(v_x_19_, 2);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_19_);
if (v_isSharedCheck_45_ == 0)
{
v___x_24_ = v_x_19_;
v_isShared_25_ = v_isSharedCheck_45_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_tail_22_);
lean_inc(v_value_21_);
lean_inc(v_key_20_);
lean_dec(v_x_19_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_45_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v_fold_30_; uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_26_ = lean_array_get_size(v_x_18_);
v___x_27_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_key_20_);
v___x_28_ = 32ULL;
v___x_29_ = lean_uint64_shift_right(v___x_27_, v___x_28_);
v_fold_30_ = lean_uint64_xor(v___x_27_, v___x_29_);
v___x_31_ = 16ULL;
v___x_32_ = lean_uint64_shift_right(v_fold_30_, v___x_31_);
v___x_33_ = lean_uint64_xor(v_fold_30_, v___x_32_);
v___x_34_ = lean_uint64_to_usize(v___x_33_);
v___x_35_ = lean_usize_of_nat(v___x_26_);
v___x_36_ = ((size_t)1ULL);
v___x_37_ = lean_usize_sub(v___x_35_, v___x_36_);
v___x_38_ = lean_usize_land(v___x_34_, v___x_37_);
v___x_39_ = lean_array_uget_borrowed(v_x_18_, v___x_38_);
lean_inc(v___x_39_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 2, v___x_39_);
v___x_41_ = v___x_24_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_key_20_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_value_21_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v___x_39_);
v___x_41_ = v_reuseFailAlloc_44_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; 
v___x_42_ = lean_array_uset(v_x_18_, v___x_38_, v___x_41_);
v_x_18_ = v___x_42_;
v_x_19_ = v_tail_22_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(lean_object* v_i_46_, lean_object* v_source_47_, lean_object* v_target_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_array_get_size(v_source_47_);
v___x_50_ = lean_nat_dec_lt(v_i_46_, v___x_49_);
if (v___x_50_ == 0)
{
lean_dec_ref(v_source_47_);
lean_dec(v_i_46_);
return v_target_48_;
}
else
{
lean_object* v_es_51_; lean_object* v___x_52_; lean_object* v_source_53_; lean_object* v_target_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_es_51_ = lean_array_fget(v_source_47_, v_i_46_);
v___x_52_ = lean_box(0);
v_source_53_ = lean_array_fset(v_source_47_, v_i_46_, v___x_52_);
v_target_54_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_target_48_, v_es_51_);
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v_i_46_, v___x_55_);
lean_dec(v_i_46_);
v_i_46_ = v___x_56_;
v_source_47_ = v_source_53_;
v_target_48_ = v_target_54_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(lean_object* v_data_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_nbuckets_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_59_ = lean_array_get_size(v_data_58_);
v___x_60_ = lean_unsigned_to_nat(2u);
v_nbuckets_61_ = lean_nat_mul(v___x_59_, v___x_60_);
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_box(0);
v___x_64_ = lean_mk_array(v_nbuckets_61_, v___x_63_);
v___x_65_ = lean_array_propagate_mark(v_data_58_, v___x_64_);
v___x_66_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v___x_62_, v_data_58_, v___x_65_);
return v___x_66_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(lean_object* v_a_67_, lean_object* v_x_68_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
uint8_t v___x_69_; 
lean_dec(v_a_67_);
v___x_69_ = 0;
return v___x_69_;
}
else
{
lean_object* v_key_70_; lean_object* v_tail_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_key_70_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_key_70_);
v_tail_71_ = lean_ctor_get(v_x_68_, 2);
lean_inc(v_tail_71_);
lean_dec_ref_known(v_x_68_, 3);
v___x_72_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_67_);
v___x_73_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_72_, v_key_70_, v_a_67_);
if (v___x_73_ == 0)
{
v_x_68_ = v_tail_71_;
goto _start;
}
else
{
lean_dec(v_tail_71_);
lean_dec(v_a_67_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_67_ = stack[0].m_obj;
lean_object* v_x_68_ = stack[1].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_67_, v_x_68_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_a_76_, lean_object* v_x_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_76_, v_x_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(lean_object* v_a_80_, lean_object* v_b_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_dec(v_b_81_);
lean_dec(v_a_80_);
return v_x_82_;
}
else
{
lean_object* v_key_83_; lean_object* v_value_84_; lean_object* v_tail_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_98_; 
v_key_83_ = lean_ctor_get(v_x_82_, 0);
v_value_84_ = lean_ctor_get(v_x_82_, 1);
v_tail_85_ = lean_ctor_get(v_x_82_, 2);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_98_ == 0)
{
v___x_87_ = v_x_82_;
v_isShared_88_ = v_isSharedCheck_98_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_tail_85_);
lean_inc(v_value_84_);
lean_inc(v_key_83_);
lean_dec(v_x_82_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_98_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_80_);
lean_inc(v_key_83_);
v___x_90_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_89_, v_key_83_, v_a_80_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_80_, v_b_81_, v_tail_85_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 2, v___x_91_);
v___x_93_ = v___x_87_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_key_83_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_value_84_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_value_84_);
lean_dec(v_key_83_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v_b_81_);
lean_ctor_set(v___x_87_, 0, v_a_80_);
v___x_96_ = v___x_87_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_80_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_b_81_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v_tail_85_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(lean_object* v_m_99_, lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v_size_102_; lean_object* v_buckets_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_146_; 
v_size_102_ = lean_ctor_get(v_m_99_, 0);
v_buckets_103_ = lean_ctor_get(v_m_99_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_m_99_);
if (v_isSharedCheck_146_ == 0)
{
v___x_105_ = v_m_99_;
v_isShared_106_ = v_isSharedCheck_146_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_buckets_103_);
lean_inc(v_size_102_);
lean_dec(v_m_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_146_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v_fold_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; lean_object* v_bkt_120_; uint8_t v___x_121_; 
v___x_107_ = lean_array_get_size(v_buckets_103_);
v___x_108_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_100_);
v___x_109_ = 32ULL;
v___x_110_ = lean_uint64_shift_right(v___x_108_, v___x_109_);
v_fold_111_ = lean_uint64_xor(v___x_108_, v___x_110_);
v___x_112_ = 16ULL;
v___x_113_ = lean_uint64_shift_right(v_fold_111_, v___x_112_);
v___x_114_ = lean_uint64_xor(v_fold_111_, v___x_113_);
v___x_115_ = lean_uint64_to_usize(v___x_114_);
v___x_116_ = lean_usize_of_nat(v___x_107_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_sub(v___x_116_, v___x_117_);
v___x_119_ = lean_usize_land(v___x_115_, v___x_118_);
v_bkt_120_ = lean_array_uget_borrowed(v_buckets_103_, v___x_119_);
lean_inc(v_bkt_120_);
lean_inc(v_a_100_);
v___x_121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_100_, v_bkt_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v_size_x27_123_; lean_object* v___x_124_; lean_object* v_buckets_x27_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v_size_x27_123_ = lean_nat_add(v_size_102_, v___x_122_);
lean_dec(v_size_102_);
lean_inc(v_bkt_120_);
v___x_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_124_, 0, v_a_100_);
lean_ctor_set(v___x_124_, 1, v_b_101_);
lean_ctor_set(v___x_124_, 2, v_bkt_120_);
v_buckets_x27_125_ = lean_array_uset(v_buckets_103_, v___x_119_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(4u);
v___x_127_ = lean_nat_mul(v_size_x27_123_, v___x_126_);
v___x_128_ = lean_unsigned_to_nat(3u);
v___x_129_ = lean_nat_div(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_array_get_size(v_buckets_x27_125_);
v___x_131_ = lean_nat_dec_le(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
if (v___x_131_ == 0)
{
lean_object* v_val_132_; lean_object* v___x_134_; 
v_val_132_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_buckets_x27_125_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_val_132_);
lean_ctor_set(v___x_105_, 0, v_size_x27_123_);
v___x_134_ = v___x_105_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_size_x27_123_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_val_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v___x_137_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_buckets_x27_125_);
lean_ctor_set(v___x_105_, 0, v_size_x27_123_);
v___x_137_ = v___x_105_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_size_x27_123_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_buckets_x27_125_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_object* v___x_139_; lean_object* v_buckets_x27_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
lean_inc(v_bkt_120_);
v___x_139_ = lean_box(0);
v_buckets_x27_140_ = lean_array_uset(v_buckets_103_, v___x_119_, v___x_139_);
v___x_141_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_100_, v_b_101_, v_bkt_120_);
v___x_142_ = lean_array_uset(v_buckets_x27_140_, v___x_119_, v___x_141_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_142_);
v___x_144_ = v___x_105_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_size_102_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(lean_object* v_a_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v___x_149_; 
lean_dec(v_a_147_);
v___x_149_ = lean_box(0);
return v___x_149_;
}
else
{
lean_object* v_key_150_; lean_object* v_value_151_; lean_object* v_tail_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_key_150_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_key_150_);
v_value_151_ = lean_ctor_get(v_x_148_, 1);
lean_inc(v_value_151_);
v_tail_152_ = lean_ctor_get(v_x_148_, 2);
lean_inc(v_tail_152_);
lean_dec_ref_known(v_x_148_, 3);
v___x_153_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v_a_147_);
v___x_154_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_153_, v_key_150_, v_a_147_);
if (v___x_154_ == 0)
{
lean_dec(v_value_151_);
v_x_148_ = v_tail_152_;
goto _start;
}
else
{
lean_object* v___x_156_; 
lean_dec(v_tail_152_);
lean_dec(v_a_147_);
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_value_151_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(lean_object* v_m_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_buckets_159_; lean_object* v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v_fold_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; size_t v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_buckets_159_ = lean_ctor_get(v_m_157_, 1);
v___x_160_ = lean_array_get_size(v_buckets_159_);
v___x_161_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_158_);
v___x_162_ = 32ULL;
v___x_163_ = lean_uint64_shift_right(v___x_161_, v___x_162_);
v_fold_164_ = lean_uint64_xor(v___x_161_, v___x_163_);
v___x_165_ = 16ULL;
v___x_166_ = lean_uint64_shift_right(v_fold_164_, v___x_165_);
v___x_167_ = lean_uint64_xor(v_fold_164_, v___x_166_);
v___x_168_ = lean_uint64_to_usize(v___x_167_);
v___x_169_ = lean_usize_of_nat(v___x_160_);
v___x_170_ = ((size_t)1ULL);
v___x_171_ = lean_usize_sub(v___x_169_, v___x_170_);
v___x_172_ = lean_usize_land(v___x_168_, v___x_171_);
v___x_173_ = lean_array_uget_borrowed(v_buckets_159_, v___x_172_);
lean_inc(v___x_173_);
v___x_174_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_158_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_175_, v_a_176_);
lean_dec_ref(v_m_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(lean_object* v_aig_178_, lean_object* v_n_179_){
_start:
{
lean_object* v_decls_180_; lean_object* v_cache_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_203_; 
v_decls_180_ = lean_ctor_get(v_aig_178_, 0);
v_cache_181_ = lean_ctor_get(v_aig_178_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_aig_178_);
if (v_isSharedCheck_203_ == 0)
{
v___x_183_ = v_aig_178_;
v_isShared_184_ = v_isSharedCheck_203_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_cache_181_);
lean_inc(v_decls_180_);
lean_dec(v_aig_178_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_203_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_decl_185_; lean_object* v___x_186_; 
v_decl_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_185_, 0, v_n_179_);
lean_inc_ref(v_decl_185_);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_cache_181_, v_decl_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_g_187_; lean_object* v_cache_188_; lean_object* v_decls_189_; lean_object* v___x_191_; 
v_g_187_ = lean_array_get_size(v_decls_180_);
lean_inc_ref(v_decl_185_);
v_cache_188_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_cache_181_, v_decl_185_, v_g_187_);
v_decls_189_ = lean_array_push(v_decls_180_, v_decl_185_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v_cache_188_);
lean_ctor_set(v___x_183_, 0, v_decls_189_);
v___x_191_ = v___x_183_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_decls_189_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_cache_188_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = 0;
v___x_193_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_193_, 0, v_g_187_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_191_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
return v___x_194_;
}
}
else
{
lean_object* v_val_196_; lean_object* v___x_198_; 
lean_dec_ref_known(v_decl_185_, 1);
v_val_196_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v___x_186_, 1);
if (v_isShared_184_ == 0)
{
v___x_198_ = v___x_183_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_decls_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_cache_181_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = 0;
v___x_200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_200_, 0, v_val_196_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_198_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
return v___x_201_;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_204_; lean_object* v___x_205_; 
v___x_204_ = 0;
v___x_205_ = l_Bool_toNat(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(lean_object* v_aig_206_, lean_object* v_w_207_, lean_object* v_a_208_, lean_object* v_curr_209_, lean_object* v_s_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = lean_nat_dec_lt(v_curr_209_, v_w_207_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
lean_dec(v_curr_209_);
lean_dec(v_a_208_);
lean_dec(v_w_207_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_aig_206_);
lean_ctor_set(v___x_212_, 1, v_s_210_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v_res_214_; lean_object* v_ref_215_; lean_object* v_aig_216_; lean_object* v_gate_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_s_224_; 
lean_inc(v_curr_209_);
lean_inc(v_w_207_);
lean_inc(v_a_208_);
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v_a_208_);
lean_ctor_set(v___x_213_, 1, v_w_207_);
lean_ctor_set(v___x_213_, 2, v_curr_209_);
v_res_214_ = l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(v_aig_206_, v___x_213_);
v_ref_215_ = lean_ctor_get(v_res_214_, 1);
lean_inc_ref(v_ref_215_);
v_aig_216_ = lean_ctor_get(v_res_214_, 0);
lean_inc_ref(v_aig_216_);
lean_dec_ref(v_res_214_);
v_gate_217_ = lean_ctor_get(v_ref_215_, 0);
lean_inc(v_gate_217_);
lean_dec_ref(v_ref_215_);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_curr_209_, v___x_218_);
lean_dec(v_curr_209_);
v___x_220_ = lean_unsigned_to_nat(2u);
v___x_221_ = lean_nat_mul(v_gate_217_, v___x_220_);
lean_dec(v_gate_217_);
v___x_222_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0);
v___x_223_ = lean_nat_lor(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
v_s_224_ = lean_array_push(v_s_210_, v___x_223_);
v_aig_206_ = v_aig_216_;
v_curr_209_ = v___x_219_;
v_s_210_ = v_s_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object* v_aig_226_, lean_object* v_w_227_, lean_object* v_a_228_, lean_object* v_curr_229_, lean_object* v_s_230_, lean_object* v_hcurr_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_226_, v_w_227_, v_a_228_, v_curr_229_, v_s_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(lean_object* v_00_u03b2_233_, lean_object* v_m_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_234_, v_a_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_237_, lean_object* v_m_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(v_00_u03b2_237_, v_m_238_, v_a_239_);
lean_dec_ref(v_m_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(lean_object* v_00_u03b2_241_, lean_object* v_m_242_, lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_m_242_, v_a_243_, v_b_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_246_, lean_object* v_a_247_, lean_object* v_x_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_247_, v_x_248_);
return v___x_249_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_250_, lean_object* v_a_251_, lean_object* v_x_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_251_, v_x_252_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_251_ = stack[1].m_obj;
lean_object* v_x_252_ = stack[2].m_obj;
uint8_t v_res_254_;
v_res_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(lean_box(0), v_a_251_, v_x_252_);
stack->m_num = v_res_254_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(v_00_u03b2_255_, v_a_256_, v_x_257_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_260_, lean_object* v_data_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_data_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_263_, lean_object* v_a_264_, lean_object* v_b_265_, lean_object* v_x_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_264_, v_b_265_, v_x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_268_, lean_object* v_i_269_, lean_object* v_source_270_, lean_object* v_target_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v_i_269_, v_source_270_, v_target_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_x_274_, v_x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(lean_object* v_c_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_mk_empty_array_with_capacity(v_c_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg___boxed(lean_object* v_c_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(v_c_279_);
lean_dec(v_c_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(lean_object* v_aig_281_, lean_object* v_c_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_mk_empty_array_with_capacity(v_c_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___boxed(lean_object* v_aig_284_, lean_object* v_c_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(v_aig_284_, v_c_285_);
lean_dec(v_c_285_);
lean_dec_ref(v_aig_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object* v_w_287_, lean_object* v_aig_288_, lean_object* v_var_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_mk_empty_array_with_capacity(v_w_287_);
v___x_292_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_288_, v_w_287_, v_var_289_, v___x_290_, v___x_291_);
return v___x_292_;
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
