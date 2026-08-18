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
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Std_Sat_AIG_instHashableFanin_hash(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
lean_dec(v_query_2_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
lean_dec(v_query_2_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_43_; lean_object* v_val_44_; uint8_t v___x_45_; 
v___x_43_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
lean_inc(v___x_19_);
v_val_44_ = lean_noption_get(v___x_19_);
lean_inc(v_query_2_);
lean_inc(v_val_44_);
v___x_45_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v___x_43_, v_val_44_, v_query_2_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
lean_dec(v_val_44_);
v___x_46_ = lean_array_get_size(v_keyArray_17_);
v___x_47_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v___x_46_);
if (v___x_48_ == 0)
{
lean_dec(v___x_47_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_47_;
goto _start;
}
}
else
{
lean_object* v_val_51_; lean_object* v___x_52_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_dec(v_query_2_);
lean_inc(v___x_41_);
v_val_51_ = lean_noption_get(v___x_41_);
v___x_52_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_52_, 0, v_x_5_);
lean_ctor_set(v___x_52_, 1, v_val_44_);
lean_ctor_set(v___x_52_, 2, v_val_51_);
return v___x_52_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_m_53_, lean_object* v_query_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_m_53_, v_query_54_, v_x_55_, v_x_56_, v_x_57_);
lean_dec_ref(v_m_53_);
return v_res_58_;
}
}
LEAN_EXPORT uint64_t l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__3(lean_object* v_x_59_){
_start:
{
switch(lean_obj_tag(v_x_59_))
{
case 0:
{
uint64_t v___x_60_; 
v___x_60_ = 0ULL;
return v___x_60_;
}
case 1:
{
lean_object* v_idx_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; 
v_idx_61_ = lean_ctor_get(v_x_59_, 0);
v___x_62_ = 1ULL;
v___x_63_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_61_);
v___x_64_ = lean_uint64_mix_hash(v___x_62_, v___x_63_);
return v___x_64_;
}
default: 
{
lean_object* v_l_65_; lean_object* v_r_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v___x_71_; 
v_l_65_ = lean_ctor_get(v_x_59_, 0);
v_r_66_ = lean_ctor_get(v_x_59_, 1);
v___x_67_ = 2ULL;
v___x_68_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_65_);
v___x_69_ = lean_uint64_mix_hash(v___x_67_, v___x_68_);
v___x_70_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_66_);
v___x_71_ = lean_uint64_mix_hash(v___x_69_, v___x_70_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__3___boxed(lean_object* v_x_72_){
_start:
{
uint64_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__3(v_x_72_);
lean_dec(v_x_72_);
v_r_74_ = lean_box_uint64(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(lean_object* v_m_75_, lean_object* v_query_76_){
_start:
{
lean_object* v_keyArray_77_; lean_object* v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v_fold_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_keyArray_77_ = lean_ctor_get(v_m_75_, 1);
v___x_78_ = lean_array_get_size(v_keyArray_77_);
v___x_79_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__3(v_query_76_);
v___x_80_ = 32ULL;
v___x_81_ = lean_uint64_shift_right(v___x_79_, v___x_80_);
v_fold_82_ = lean_uint64_xor(v___x_79_, v___x_81_);
v___x_83_ = 16ULL;
v___x_84_ = lean_uint64_shift_right(v_fold_82_, v___x_83_);
v___x_85_ = lean_uint64_xor(v_fold_82_, v___x_84_);
v___x_86_ = lean_uint64_to_usize(v___x_85_);
v___x_87_ = lean_usize_of_nat(v___x_78_);
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_sub(v___x_87_, v___x_88_);
v___x_90_ = lean_usize_land(v___x_86_, v___x_89_);
v___x_91_ = lean_usize_to_nat(v___x_90_);
v___x_92_ = lean_box(0);
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_m_75_, v_query_76_, v___x_92_, v___x_78_, v___x_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg___boxed(lean_object* v_m_94_, lean_object* v_query_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_m_94_, v_query_95_);
lean_dec_ref(v_m_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___redArg(lean_object* v_b_97_, lean_object* v_acc_98_, lean_object* v_i_99_){
_start:
{
lean_object* v___y_101_; lean_object* v_keyArray_109_; lean_object* v_valueArray_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_keyArray_109_ = lean_ctor_get(v_b_97_, 1);
v_valueArray_110_ = lean_ctor_get(v_b_97_, 2);
v___x_111_ = lean_array_get_size(v_keyArray_109_);
v___x_112_ = lean_nat_dec_lt(v_i_99_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec(v_i_99_);
return v_acc_98_;
}
else
{
lean_object* v___x_113_; uint8_t v_isSome_114_; 
v___x_113_ = lean_array_fget_borrowed(v_keyArray_109_, v_i_99_);
v_isSome_114_ = lean_noption_is_some(v___x_113_);
if (v_isSome_114_ == 0)
{
goto v___jp_105_;
}
else
{
lean_object* v___x_115_; uint8_t v_isSome_116_; 
v___x_115_ = lean_array_fget_borrowed(v_valueArray_110_, v_i_99_);
v_isSome_116_ = lean_noption_is_some(v___x_115_);
if (v_isSome_116_ == 0)
{
goto v___jp_105_;
}
else
{
lean_object* v_val_117_; lean_object* v_val_118_; lean_object* v_i_120_; lean_object* v___x_125_; 
lean_inc(v___x_113_);
v_val_117_ = lean_noption_get(v___x_113_);
lean_inc(v___x_115_);
v_val_118_ = lean_noption_get(v___x_115_);
lean_inc(v_val_117_);
v___x_125_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_acc_98_, v_val_117_);
switch(lean_obj_tag(v___x_125_))
{
case 0:
{
lean_object* v_index_126_; lean_object* v_size_127_; lean_object* v___x_128_; 
v_index_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_index_126_);
lean_dec_ref_known(v___x_125_, 3);
v_size_127_ = lean_ctor_get(v_acc_98_, 0);
lean_inc(v_size_127_);
v___x_128_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_98_, v_size_127_, v_index_126_, v_val_117_, v_val_118_);
lean_dec(v_index_126_);
v___y_101_ = v___x_128_;
goto v___jp_100_;
}
case 1:
{
lean_object* v_index_129_; 
v_index_129_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_index_129_);
lean_dec_ref_known(v___x_125_, 1);
v_i_120_ = v_index_129_;
goto v___jp_119_;
}
default: 
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_98_, v___x_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_index_132_; 
v_index_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_index_132_);
lean_dec_ref_known(v___x_131_, 1);
v_i_120_ = v_index_132_;
goto v___jp_119_;
}
else
{
lean_dec(v_val_118_);
lean_dec(v_val_117_);
v___y_101_ = v_acc_98_;
goto v___jp_100_;
}
}
}
v___jp_119_:
{
lean_object* v_size_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_size_121_ = lean_ctor_get(v_acc_98_, 0);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v_size_121_, v___x_122_);
v___x_124_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_98_, v___x_123_, v_i_120_, v_val_117_, v_val_118_);
lean_dec(v_i_120_);
v___y_101_ = v___x_124_;
goto v___jp_100_;
}
}
}
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_i_99_, v___x_102_);
lean_dec(v_i_99_);
v_acc_98_ = v___y_101_;
v_i_99_ = v___x_103_;
goto _start;
}
v___jp_105_:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_i_99_, v___x_106_);
lean_dec(v_i_99_);
v_i_99_ = v___x_107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_b_133_, lean_object* v_acc_134_, lean_object* v_i_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___redArg(v_b_133_, v_acc_134_, v_i_135_);
lean_dec_ref(v_b_133_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___redArg(lean_object* v_init_137_, lean_object* v_b_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___redArg(v_b_138_, v_init_137_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_init_141_, lean_object* v_b_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___redArg(v_init_141_, v_b_142_);
lean_dec_ref(v_b_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg(lean_object* v_m_144_){
_start:
{
lean_object* v_keyArray_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_cellCount_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_target_152_; lean_object* v___x_153_; 
v_keyArray_145_ = lean_ctor_get(v_m_144_, 1);
v___x_146_ = lean_array_get_size(v_keyArray_145_);
v___x_147_ = lean_unsigned_to_nat(2u);
v_cellCount_148_ = lean_nat_mul(v___x_146_, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_148_);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_148_);
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_148_);
v_target_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_152_, 0, v___x_149_);
lean_ctor_set(v_target_152_, 1, v___x_150_);
lean_ctor_set(v_target_152_, 2, v___x_151_);
v___x_153_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___redArg(v_target_152_, v_m_144_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg___boxed(lean_object* v_m_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg(v_m_154_);
lean_dec_ref(v_m_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_156_, lean_object* v_query_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_m_156_, v_query_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_index_159_; lean_object* v_key_160_; lean_object* v_value_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_index_159_ = lean_ctor_get(v___x_158_, 0);
v_key_160_ = lean_ctor_get(v___x_158_, 1);
v_value_161_ = lean_ctor_get(v___x_158_, 2);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_158_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_value_161_);
lean_inc(v_key_160_);
lean_inc(v_index_159_);
lean_dec(v___x_158_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_index_159_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_key_160_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_value_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v___x_169_; 
lean_dec(v___x_158_);
v___x_169_ = lean_box(1);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_170_, lean_object* v_query_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___redArg(v_m_170_, v_query_171_);
lean_dec_ref(v_m_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(lean_object* v_m_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___redArg(v_m_173_, v_a_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_value_176_; lean_object* v___x_177_; 
v_value_176_ = lean_ctor_get(v___x_175_, 2);
lean_inc(v_value_176_);
lean_dec_ref_known(v___x_175_, 3);
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v_value_176_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_179_, v_a_180_);
lean_dec_ref(v_m_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(lean_object* v_aig_182_, lean_object* v_n_183_){
_start:
{
lean_object* v_decls_184_; lean_object* v_cache_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_272_; 
v_decls_184_ = lean_ctor_get(v_aig_182_, 0);
v_cache_185_ = lean_ctor_get(v_aig_182_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_aig_182_);
if (v_isSharedCheck_272_ == 0)
{
v___x_187_ = v_aig_182_;
v_isShared_188_ = v_isSharedCheck_272_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_cache_185_);
lean_inc(v_decls_184_);
lean_dec(v_aig_182_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_272_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_decl_189_; lean_object* v___x_190_; 
v_decl_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_189_, 0, v_n_183_);
lean_inc_ref(v_decl_189_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_cache_185_, v_decl_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_g_191_; lean_object* v___y_193_; lean_object* v___y_202_; lean_object* v_i_203_; lean_object* v___y_209_; lean_object* v___y_219_; lean_object* v_i_220_; lean_object* v___x_235_; 
v_g_191_ = lean_array_get_size(v_decls_184_);
lean_inc_ref(v_decl_189_);
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_cache_185_, v_decl_189_);
switch(lean_obj_tag(v___x_235_))
{
case 0:
{
lean_object* v_index_236_; lean_object* v_size_237_; lean_object* v___x_238_; 
v_index_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_index_236_);
lean_dec_ref_known(v___x_235_, 3);
v_size_237_ = lean_ctor_get(v_cache_185_, 0);
lean_inc(v_size_237_);
lean_inc_ref(v_decl_189_);
v___x_238_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_185_, v_size_237_, v_index_236_, v_decl_189_, v_g_191_);
lean_dec(v_index_236_);
v___y_193_ = v___x_238_;
goto v___jp_192_;
}
case 1:
{
lean_object* v_index_239_; lean_object* v_size_240_; lean_object* v_keyArray_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_index_239_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_index_239_);
lean_dec_ref_known(v___x_235_, 1);
v_size_240_ = lean_ctor_get(v_cache_185_, 0);
v_keyArray_241_ = lean_ctor_get(v_cache_185_, 1);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_size_240_, v___x_242_);
v___x_244_ = lean_array_get_size(v_keyArray_241_);
v___x_245_ = lean_nat_dec_lt(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v___x_243_);
lean_dec(v_index_239_);
goto v___jp_225_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_246_ = lean_unsigned_to_nat(4u);
v___x_247_ = lean_nat_mul(v___x_243_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(3u);
v___x_249_ = lean_nat_mul(v___x_244_, v___x_248_);
v___x_250_ = lean_nat_dec_le(v___x_247_, v___x_249_);
lean_dec(v___x_249_);
lean_dec(v___x_247_);
if (v___x_250_ == 0)
{
lean_dec(v___x_243_);
lean_dec(v_index_239_);
goto v___jp_225_;
}
else
{
lean_object* v___x_251_; 
lean_inc_ref(v_decl_189_);
v___x_251_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_185_, v___x_243_, v_index_239_, v_decl_189_, v_g_191_);
lean_dec(v_index_239_);
v___y_193_ = v___x_251_;
goto v___jp_192_;
}
}
}
default: 
{
lean_object* v_size_252_; lean_object* v_keyArray_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_size_252_ = lean_ctor_get(v_cache_185_, 0);
v_keyArray_253_ = lean_ctor_get(v_cache_185_, 1);
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_nat_add(v_size_252_, v___x_254_);
v___x_256_ = lean_array_get_size(v_keyArray_253_);
v___x_257_ = lean_nat_dec_lt(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec(v___x_255_);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg(v_cache_185_);
lean_dec_ref(v_cache_185_);
v___y_209_ = v___x_258_;
goto v___jp_208_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_259_ = lean_unsigned_to_nat(4u);
v___x_260_ = lean_nat_mul(v___x_255_, v___x_259_);
lean_dec(v___x_255_);
v___x_261_ = lean_unsigned_to_nat(3u);
v___x_262_ = lean_nat_mul(v___x_256_, v___x_261_);
v___x_263_ = lean_nat_dec_le(v___x_260_, v___x_262_);
lean_dec(v___x_262_);
lean_dec(v___x_260_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg(v_cache_185_);
lean_dec_ref(v_cache_185_);
v___y_209_ = v___x_264_;
goto v___jp_208_;
}
else
{
v___y_209_ = v_cache_185_;
goto v___jp_208_;
}
}
}
}
v___jp_192_:
{
lean_object* v_decls_194_; lean_object* v___x_196_; 
v_decls_194_ = lean_array_push(v_decls_184_, v_decl_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___y_193_);
lean_ctor_set(v___x_187_, 0, v_decls_194_);
v___x_196_ = v___x_187_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_decls_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___y_193_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = 0;
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v_g_191_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_196_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
}
v___jp_201_:
{
lean_object* v_size_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_size_204_ = lean_ctor_get(v___y_202_, 0);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_add(v_size_204_, v___x_205_);
lean_inc_ref(v_decl_189_);
v___x_207_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_202_, v___x_206_, v_i_203_, v_decl_189_, v_g_191_);
lean_dec(v_i_203_);
v___y_193_ = v___x_207_;
goto v___jp_192_;
}
v___jp_208_:
{
lean_object* v___x_210_; 
lean_inc_ref(v_decl_189_);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v___y_209_, v_decl_189_);
switch(lean_obj_tag(v___x_210_))
{
case 0:
{
lean_object* v_index_211_; lean_object* v_size_212_; lean_object* v___x_213_; 
v_index_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_210_, 3);
v_size_212_ = lean_ctor_get(v___y_209_, 0);
lean_inc(v_size_212_);
lean_inc_ref(v_decl_189_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_209_, v_size_212_, v_index_211_, v_decl_189_, v_g_191_);
lean_dec(v_index_211_);
v___y_193_ = v___x_213_;
goto v___jp_192_;
}
case 1:
{
lean_object* v_index_214_; 
v_index_214_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_214_);
lean_dec_ref_known(v___x_210_, 1);
v___y_202_ = v___y_209_;
v_i_203_ = v_index_214_;
goto v___jp_201_;
}
default: 
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_209_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_index_217_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_217_);
lean_dec_ref_known(v___x_216_, 1);
v___y_202_ = v___y_209_;
v_i_203_ = v_index_217_;
goto v___jp_201_;
}
else
{
v___y_193_ = v___y_209_;
goto v___jp_192_;
}
}
}
}
v___jp_218_:
{
lean_object* v_size_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_size_221_ = lean_ctor_get(v___y_219_, 0);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_size_221_, v___x_222_);
lean_inc_ref(v_decl_189_);
v___x_224_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_219_, v___x_223_, v_i_220_, v_decl_189_, v_g_191_);
lean_dec(v_i_220_);
v___y_193_ = v___x_224_;
goto v___jp_192_;
}
v___jp_225_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg(v_cache_185_);
lean_dec_ref(v_cache_185_);
lean_inc_ref(v_decl_189_);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v___x_226_, v_decl_189_);
switch(lean_obj_tag(v___x_227_))
{
case 0:
{
lean_object* v_index_228_; lean_object* v_size_229_; lean_object* v___x_230_; 
v_index_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_index_228_);
lean_dec_ref_known(v___x_227_, 3);
v_size_229_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_size_229_);
lean_inc_ref(v_decl_189_);
v___x_230_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_226_, v_size_229_, v_index_228_, v_decl_189_, v_g_191_);
lean_dec(v_index_228_);
v___y_193_ = v___x_230_;
goto v___jp_192_;
}
case 1:
{
lean_object* v_index_231_; 
v_index_231_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_index_231_);
lean_dec_ref_known(v___x_227_, 1);
v___y_219_ = v___x_226_;
v_i_220_ = v_index_231_;
goto v___jp_218_;
}
default: 
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_226_, v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_index_234_; 
v_index_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_index_234_);
lean_dec_ref_known(v___x_233_, 1);
v___y_219_ = v___x_226_;
v_i_220_ = v_index_234_;
goto v___jp_218_;
}
else
{
v___y_193_ = v___x_226_;
goto v___jp_192_;
}
}
}
}
}
else
{
lean_object* v_val_265_; lean_object* v___x_267_; 
lean_dec_ref_known(v_decl_189_, 1);
v_val_265_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v___x_190_, 1);
if (v_isShared_188_ == 0)
{
v___x_267_ = v___x_187_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_decls_184_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_cache_185_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = 0;
v___x_269_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_269_, 0, v_val_265_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*1, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_267_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
return v___x_270_;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_273_; lean_object* v___x_274_; 
v___x_273_ = 0;
v___x_274_ = l_Bool_toNat(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(lean_object* v_aig_275_, lean_object* v_w_276_, lean_object* v_a_277_, lean_object* v_curr_278_, lean_object* v_s_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_nat_dec_lt(v_curr_278_, v_w_276_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
lean_dec(v_curr_278_);
lean_dec(v_a_277_);
lean_dec(v_w_276_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_aig_275_);
lean_ctor_set(v___x_281_, 1, v_s_279_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v_res_283_; lean_object* v_ref_284_; lean_object* v_aig_285_; lean_object* v_gate_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_s_293_; 
lean_inc(v_curr_278_);
lean_inc(v_w_276_);
lean_inc(v_a_277_);
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v_a_277_);
lean_ctor_set(v___x_282_, 1, v_w_276_);
lean_ctor_set(v___x_282_, 2, v_curr_278_);
v_res_283_ = l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(v_aig_275_, v___x_282_);
v_ref_284_ = lean_ctor_get(v_res_283_, 1);
lean_inc_ref(v_ref_284_);
v_aig_285_ = lean_ctor_get(v_res_283_, 0);
lean_inc_ref(v_aig_285_);
lean_dec_ref(v_res_283_);
v_gate_286_ = lean_ctor_get(v_ref_284_, 0);
lean_inc(v_gate_286_);
lean_dec_ref(v_ref_284_);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_curr_278_, v___x_287_);
lean_dec(v_curr_278_);
v___x_289_ = lean_unsigned_to_nat(2u);
v___x_290_ = lean_nat_mul(v_gate_286_, v___x_289_);
lean_dec(v_gate_286_);
v___x_291_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0);
v___x_292_ = lean_nat_lor(v___x_290_, v___x_291_);
lean_dec(v___x_290_);
v_s_293_ = lean_array_push(v_s_279_, v___x_292_);
v_aig_275_ = v_aig_285_;
v_curr_278_ = v___x_288_;
v_s_279_ = v_s_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(lean_object* v_aig_295_, lean_object* v_w_296_, lean_object* v_a_297_, lean_object* v_curr_298_, lean_object* v_s_299_, lean_object* v_hcurr_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_295_, v_w_296_, v_a_297_, v_curr_298_, v_s_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(lean_object* v_00_u03b2_302_, lean_object* v_m_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_303_, v_a_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_306_, lean_object* v_m_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(v_00_u03b2_306_, v_m_307_, v_a_308_);
lean_dec_ref(v_m_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(lean_object* v_00_u03b2_310_, lean_object* v_m_311_, lean_object* v_query_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_m_311_, v_query_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___boxed(lean_object* v_00_u03b2_314_, lean_object* v_m_315_, lean_object* v_query_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(v_00_u03b2_314_, v_m_315_, v_query_316_);
lean_dec_ref(v_m_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2(lean_object* v_00_u03b2_318_, lean_object* v_m_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___redArg(v_m_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2___boxed(lean_object* v_00_u03b2_321_, lean_object* v_m_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2(v_00_u03b2_321_, v_m_322_);
lean_dec_ref(v_m_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_324_, lean_object* v_m_325_, lean_object* v_query_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___redArg(v_m_325_, v_query_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_328_, lean_object* v_m_329_, lean_object* v_query_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_00_u03b2_328_, v_m_329_, v_query_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_332_, lean_object* v_m_333_, lean_object* v_query_334_, lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_m_333_, v_query_334_, v_x_335_, v_x_336_, v_x_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_340_, lean_object* v_m_341_, lean_object* v_query_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(v_00_u03b2_340_, v_m_341_, v_query_342_, v_x_343_, v_x_344_, v_x_345_, v_x_346_);
lean_dec_ref(v_m_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_348_, lean_object* v_init_349_, lean_object* v_b_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___redArg(v_init_349_, v_b_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_352_, lean_object* v_init_353_, lean_object* v_b_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6(v_00_u03b2_352_, v_init_353_, v_b_354_);
lean_dec_ref(v_b_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7(lean_object* v_00_u03b2_356_, lean_object* v_b_357_, lean_object* v_acc_358_, lean_object* v_i_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___redArg(v_b_357_, v_acc_358_, v_i_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7___boxed(lean_object* v_00_u03b2_361_, lean_object* v_b_362_, lean_object* v_acc_363_, lean_object* v_i_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__2_spec__6_spec__7(v_00_u03b2_361_, v_b_362_, v_acc_363_, v_i_364_);
lean_dec_ref(v_b_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(lean_object* v_c_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_mk_empty_array_with_capacity(v_c_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg___boxed(lean_object* v_c_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(v_c_368_);
lean_dec(v_c_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(lean_object* v_aig_370_, lean_object* v_c_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_mk_empty_array_with_capacity(v_c_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___boxed(lean_object* v_aig_373_, lean_object* v_c_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(v_aig_373_, v_c_374_);
lean_dec(v_c_374_);
lean_dec_ref(v_aig_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(lean_object* v_w_376_, lean_object* v_aig_377_, lean_object* v_var_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_mk_empty_array_with_capacity(v_w_376_);
v___x_381_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(v_aig_377_, v_w_376_, v_var_378_, v___x_379_, v___x_380_);
return v___x_381_;
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
