// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend public import Std.Sat.AIG.If import Init.Omega
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(lean_object* v_w_1_, lean_object* v_aig_2_, lean_object* v_input_3_){
_start:
{
lean_object* v_bit_4_; lean_object* v_lhs_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_25_; 
v_bit_4_ = lean_ctor_get(v_input_3_, 1);
v_lhs_5_ = lean_ctor_get(v_input_3_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v_input_3_);
if (v_isSharedCheck_25_ == 0)
{
v___x_7_ = v_input_3_;
v_isShared_8_ = v_isSharedCheck_25_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_bit_4_);
lean_inc(v_lhs_5_);
lean_dec(v_input_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_25_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_gate_9_; uint8_t v_invert_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_refs_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_new_20_; lean_object* v___x_22_; 
v_gate_9_ = lean_ctor_get(v_bit_4_, 0);
lean_inc(v_gate_9_);
v_invert_10_ = lean_ctor_get_uint8(v_bit_4_, sizeof(void*)*1);
lean_dec_ref(v_bit_4_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_w_1_, v___x_11_);
v_refs_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_unsigned_to_nat(2u);
v___x_15_ = lean_nat_mul(v_gate_9_, v___x_14_);
lean_dec(v_gate_9_);
v___x_16_ = l_Bool_toNat(v_invert_10_);
v___x_17_ = lean_nat_lor(v___x_15_, v___x_16_);
lean_dec(v___x_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_array_push(v_refs_13_, v___x_17_);
v___x_19_ = lean_nat_add(v___x_11_, v_w_1_);
v_new_20_ = l_Array_append___redArg(v___x_18_, v_lhs_5_);
lean_dec_ref(v_lhs_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_new_20_);
lean_ctor_set(v___x_7_, 0, v___x_19_);
v___x_22_ = v___x_7_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_new_20_);
v___x_22_ = v_reuseFailAlloc_24_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(v_w_1_, v_aig_2_, v___x_22_);
lean_dec_ref(v___x_22_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg___boxed(lean_object* v_w_26_, lean_object* v_aig_27_, lean_object* v_input_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_26_, v_aig_27_, v_input_28_);
lean_dec(v_w_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_w_33_, lean_object* v_aig_34_, lean_object* v_input_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_33_, v_aig_34_, v_input_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_w_40_, lean_object* v_aig_41_, lean_object* v_input_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(v_00_u03b1_37_, v_inst_38_, v_inst_39_, v_w_40_, v_aig_41_, v_input_42_);
lean_dec(v_w_40_);
lean_dec_ref(v_inst_39_);
lean_dec_ref(v_inst_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat_match__1_splitter___redArg(lean_object* v_input_44_, lean_object* v_h__1_45_){
_start:
{
lean_object* v_lhs_46_; lean_object* v_bit_47_; lean_object* v___x_48_; 
v_lhs_46_ = lean_ctor_get(v_input_44_, 0);
lean_inc_ref(v_lhs_46_);
v_bit_47_ = lean_ctor_get(v_input_44_, 1);
lean_inc_ref(v_bit_47_);
lean_dec_ref(v_input_44_);
v___x_48_ = lean_apply_2(v_h__1_45_, v_lhs_46_, v_bit_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat_match__1_splitter(lean_object* v_00_u03b1_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_w_52_, lean_object* v_aig_53_, lean_object* v_motive_54_, lean_object* v_input_55_, lean_object* v_h__1_56_){
_start:
{
lean_object* v_lhs_57_; lean_object* v_bit_58_; lean_object* v___x_59_; 
v_lhs_57_ = lean_ctor_get(v_input_55_, 0);
lean_inc_ref(v_lhs_57_);
v_bit_58_ = lean_ctor_get(v_input_55_, 1);
lean_inc_ref(v_bit_58_);
lean_dec_ref(v_input_55_);
v___x_59_ = lean_apply_2(v_h__1_56_, v_lhs_57_, v_bit_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat_match__1_splitter___boxed(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_w_63_, lean_object* v_aig_64_, lean_object* v_motive_65_, lean_object* v_input_66_, lean_object* v_h__1_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat_match__1_splitter(v_00_u03b1_60_, v_inst_61_, v_inst_62_, v_w_63_, v_aig_64_, v_motive_65_, v_input_66_, v_h__1_67_);
lean_dec_ref(v_aig_64_);
lean_dec(v_w_63_);
lean_dec_ref(v_inst_62_);
lean_dec_ref(v_inst_61_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_w_77_, lean_object* v_aig_78_, lean_object* v_n_79_, lean_object* v_d_80_, lean_object* v_wn_81_, lean_object* v_wr_82_, lean_object* v_q_83_, lean_object* v_r_84_){
_start:
{
lean_object* v___x_85_; lean_object* v_wn_86_; lean_object* v_wr_87_; uint8_t v___x_88_; lean_object* v___y_90_; uint8_t v___x_148_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v_wn_86_ = lean_nat_sub(v_wn_81_, v___x_85_);
v_wr_87_ = lean_nat_add(v_wr_82_, v___x_85_);
v___x_88_ = 0;
v___x_148_ = lean_nat_dec_lt(v_wn_86_, v_w_77_);
if (v___x_148_ == 0)
{
lean_object* v_falseRef_149_; 
v_falseRef_149_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0));
v___y_90_ = v_falseRef_149_;
goto v___jp_89_;
}
else
{
lean_object* v_ref_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_ref_150_ = lean_array_fget_borrowed(v_n_79_, v_wn_86_);
v___x_151_ = lean_nat_shiftr(v_ref_150_, v___x_85_);
v___x_152_ = lean_nat_land(v___x_85_, v_ref_150_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_nat_dec_eq(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_148_);
v___y_90_ = v___x_155_;
goto v___jp_89_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_88_);
v___y_90_ = v___x_156_;
goto v___jp_89_;
}
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v_res_92_; lean_object* v_aig_93_; lean_object* v_vec_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_147_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_r_84_);
lean_ctor_set(v___x_91_, 1, v___y_90_);
v_res_92_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_77_, v_aig_78_, v___x_91_);
v_aig_93_ = lean_ctor_get(v_res_92_, 0);
v_vec_94_ = lean_ctor_get(v_res_92_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_res_92_);
if (v_isSharedCheck_147_ == 0)
{
v___x_96_ = v_res_92_;
v_isShared_97_ = v_isSharedCheck_147_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_vec_94_);
lean_inc(v_aig_93_);
lean_dec(v_res_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_147_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v_falseRef_98_; lean_object* v___x_100_; 
v_falseRef_98_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0));
lean_inc_ref(v_q_83_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v_falseRef_98_);
lean_ctor_set(v___x_96_, 0, v_q_83_);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_q_83_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_falseRef_98_);
v___x_100_ = v_reuseFailAlloc_146_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v_res_101_; lean_object* v_aig_102_; lean_object* v_vec_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_145_; 
v_res_101_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_77_, v_aig_93_, v___x_100_);
v_aig_102_ = lean_ctor_get(v_res_101_, 0);
v_vec_103_ = lean_ctor_get(v_res_101_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_res_101_);
if (v_isSharedCheck_145_ == 0)
{
v___x_105_ = v_res_101_;
v_isShared_106_ = v_isSharedCheck_145_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_vec_103_);
lean_inc(v_aig_102_);
lean_dec(v_res_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_145_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_trueRef_107_; lean_object* v___x_109_; 
v_trueRef_107_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1));
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_trueRef_107_);
lean_ctor_set(v___x_105_, 0, v_q_83_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_q_83_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_trueRef_107_);
v___x_109_ = v_reuseFailAlloc_144_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v_res_110_; lean_object* v_aig_111_; lean_object* v_vec_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_143_; 
v_res_110_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_77_, v_aig_102_, v___x_109_);
v_aig_111_ = lean_ctor_get(v_res_110_, 0);
v_vec_112_ = lean_ctor_get(v_res_110_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_res_110_);
if (v_isSharedCheck_143_ == 0)
{
v___x_114_ = v_res_110_;
v_isShared_115_ = v_isSharedCheck_143_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_vec_112_);
lean_inc(v_aig_111_);
lean_dec(v_res_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_143_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
lean_inc_ref(v_vec_94_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v_d_80_);
lean_ctor_set(v___x_114_, 0, v_vec_94_);
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_vec_94_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_d_80_);
v___x_117_ = v_reuseFailAlloc_142_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v_res_118_; lean_object* v_aig_119_; lean_object* v_vec_120_; lean_object* v_res_121_; lean_object* v_aig_122_; lean_object* v_ref_123_; lean_object* v___x_124_; lean_object* v_res_125_; lean_object* v_aig_126_; lean_object* v_vec_127_; lean_object* v_gate_128_; uint8_t v_invert_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_141_; 
lean_inc_ref(v___x_117_);
lean_inc_ref_n(v_inst_76_, 3);
lean_inc_ref_n(v_inst_75_, 3);
v_res_118_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_111_, v___x_117_);
v_aig_119_ = lean_ctor_get(v_res_118_, 0);
lean_inc_ref(v_aig_119_);
v_vec_120_ = lean_ctor_get(v_res_118_, 1);
lean_inc_ref(v_vec_120_);
lean_dec_ref(v_res_118_);
lean_inc(v_w_77_);
v_res_121_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_119_, v___x_117_);
v_aig_122_ = lean_ctor_get(v_res_121_, 0);
lean_inc_ref(v_aig_122_);
v_ref_123_ = lean_ctor_get(v_res_121_, 1);
lean_inc_ref_n(v_ref_123_, 2);
lean_dec_ref(v_res_121_);
v___x_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_124_, 0, v_ref_123_);
lean_ctor_set(v___x_124_, 1, v_vec_103_);
lean_ctor_set(v___x_124_, 2, v_vec_112_);
v_res_125_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_122_, v___x_124_);
v_aig_126_ = lean_ctor_get(v_res_125_, 0);
lean_inc_ref(v_aig_126_);
v_vec_127_ = lean_ctor_get(v_res_125_, 1);
lean_inc_ref(v_vec_127_);
lean_dec_ref(v_res_125_);
v_gate_128_ = lean_ctor_get(v_ref_123_, 0);
v_invert_129_ = lean_ctor_get_uint8(v_ref_123_, sizeof(void*)*1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_ref_123_);
if (v_isSharedCheck_141_ == 0)
{
v___x_131_ = v_ref_123_;
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_gate_128_);
lean_dec(v_ref_123_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_discr_134_; 
if (v_isShared_132_ == 0)
{
v_discr_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_gate_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_140_, sizeof(void*)*1, v_invert_129_);
v_discr_134_ = v_reuseFailAlloc_140_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v_res_136_; lean_object* v_aig_137_; lean_object* v_vec_138_; lean_object* v___x_139_; 
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v_discr_134_);
lean_ctor_set(v___x_135_, 1, v_vec_94_);
lean_ctor_set(v___x_135_, 2, v_vec_120_);
v_res_136_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_126_, v___x_135_);
lean_dec(v_w_77_);
v_aig_137_ = lean_ctor_get(v_res_136_, 0);
lean_inc_ref(v_aig_137_);
v_vec_138_ = lean_ctor_get(v_res_136_, 1);
lean_inc_ref(v_vec_138_);
lean_dec_ref(v_res_136_);
v___x_139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_139_, 0, v_aig_137_);
lean_ctor_set(v___x_139_, 1, v_wn_86_);
lean_ctor_set(v___x_139_, 2, v_wr_87_);
lean_ctor_set(v___x_139_, 3, v_vec_127_);
lean_ctor_set(v___x_139_, 4, v_vec_138_);
return v___x_139_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___boxed(lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_w_159_, lean_object* v_aig_160_, lean_object* v_n_161_, lean_object* v_d_162_, lean_object* v_wn_163_, lean_object* v_wr_164_, lean_object* v_q_165_, lean_object* v_r_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_157_, v_inst_158_, v_w_159_, v_aig_160_, v_n_161_, v_d_162_, v_wn_163_, v_wr_164_, v_q_165_, v_r_166_);
lean_dec(v_wr_164_);
lean_dec(v_wn_163_);
lean_dec_ref(v_n_161_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object* v_00_u03b1_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_w_171_, lean_object* v_aig_172_, lean_object* v_n_173_, lean_object* v_d_174_, lean_object* v_wn_175_, lean_object* v_wr_176_, lean_object* v_q_177_, lean_object* v_r_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_169_, v_inst_170_, v_w_171_, v_aig_172_, v_n_173_, v_d_174_, v_wn_175_, v_wr_176_, v_q_177_, v_r_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___boxed(lean_object* v_00_u03b1_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_w_183_, lean_object* v_aig_184_, lean_object* v_n_185_, lean_object* v_d_186_, lean_object* v_wn_187_, lean_object* v_wr_188_, lean_object* v_q_189_, lean_object* v_r_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(v_00_u03b1_180_, v_inst_181_, v_inst_182_, v_w_183_, v_aig_184_, v_n_185_, v_d_186_, v_wn_187_, v_wr_188_, v_q_189_, v_r_190_);
lean_dec(v_wr_188_);
lean_dec(v_wn_187_);
lean_dec_ref(v_n_185_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_w_194_, lean_object* v_aig_195_, lean_object* v_curr_196_, lean_object* v_n_197_, lean_object* v_d_198_, lean_object* v_wn_199_, lean_object* v_wr_200_, lean_object* v_q_201_, lean_object* v_r_202_){
_start:
{
lean_object* v_zero_203_; uint8_t v_isZero_204_; 
v_zero_203_ = lean_unsigned_to_nat(0u);
v_isZero_204_ = lean_nat_dec_eq(v_curr_196_, v_zero_203_);
if (v_isZero_204_ == 1)
{
lean_object* v___x_205_; 
lean_dec_ref(v_d_198_);
lean_dec(v_w_194_);
lean_dec_ref(v_inst_193_);
lean_dec_ref(v_inst_192_);
v___x_205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_205_, 0, v_aig_195_);
lean_ctor_set(v___x_205_, 1, v_q_201_);
lean_ctor_set(v___x_205_, 2, v_r_202_);
return v___x_205_;
}
else
{
lean_object* v_res_206_; lean_object* v_aig_207_; lean_object* v_wn_208_; lean_object* v_wr_209_; lean_object* v_q_210_; lean_object* v_r_211_; lean_object* v_one_212_; lean_object* v_n_213_; lean_object* v_res_214_; lean_object* v_aig_215_; lean_object* v_q_216_; lean_object* v_r_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_inc_ref(v_d_198_);
lean_inc(v_w_194_);
lean_inc_ref(v_inst_193_);
lean_inc_ref(v_inst_192_);
v_res_206_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_192_, v_inst_193_, v_w_194_, v_aig_195_, v_n_197_, v_d_198_, v_wn_199_, v_wr_200_, v_q_201_, v_r_202_);
v_aig_207_ = lean_ctor_get(v_res_206_, 0);
lean_inc_ref(v_aig_207_);
v_wn_208_ = lean_ctor_get(v_res_206_, 1);
lean_inc(v_wn_208_);
v_wr_209_ = lean_ctor_get(v_res_206_, 2);
lean_inc(v_wr_209_);
v_q_210_ = lean_ctor_get(v_res_206_, 3);
lean_inc_ref(v_q_210_);
v_r_211_ = lean_ctor_get(v_res_206_, 4);
lean_inc_ref(v_r_211_);
lean_dec_ref(v_res_206_);
v_one_212_ = lean_unsigned_to_nat(1u);
v_n_213_ = lean_nat_sub(v_curr_196_, v_one_212_);
v_res_214_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_192_, v_inst_193_, v_w_194_, v_aig_207_, v_n_213_, v_n_197_, v_d_198_, v_wn_208_, v_wr_209_, v_q_210_, v_r_211_);
lean_dec(v_wr_209_);
lean_dec(v_wn_208_);
lean_dec(v_n_213_);
v_aig_215_ = lean_ctor_get(v_res_214_, 0);
v_q_216_ = lean_ctor_get(v_res_214_, 1);
v_r_217_ = lean_ctor_get(v_res_214_, 2);
v_isSharedCheck_224_ = !lean_is_exclusive(v_res_214_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v_res_214_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_r_217_);
lean_inc(v_q_216_);
lean_inc(v_aig_215_);
lean_dec(v_res_214_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_aig_215_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_q_216_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_r_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg___boxed(lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_w_227_, lean_object* v_aig_228_, lean_object* v_curr_229_, lean_object* v_n_230_, lean_object* v_d_231_, lean_object* v_wn_232_, lean_object* v_wr_233_, lean_object* v_q_234_, lean_object* v_r_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_225_, v_inst_226_, v_w_227_, v_aig_228_, v_curr_229_, v_n_230_, v_d_231_, v_wn_232_, v_wr_233_, v_q_234_, v_r_235_);
lean_dec(v_wr_233_);
lean_dec(v_wn_232_);
lean_dec_ref(v_n_230_);
lean_dec(v_curr_229_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object* v_00_u03b1_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_w_240_, lean_object* v_aig_241_, lean_object* v_curr_242_, lean_object* v_n_243_, lean_object* v_d_244_, lean_object* v_wn_245_, lean_object* v_wr_246_, lean_object* v_q_247_, lean_object* v_r_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_238_, v_inst_239_, v_w_240_, v_aig_241_, v_curr_242_, v_n_243_, v_d_244_, v_wn_245_, v_wr_246_, v_q_247_, v_r_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___boxed(lean_object* v_00_u03b1_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_w_253_, lean_object* v_aig_254_, lean_object* v_curr_255_, lean_object* v_n_256_, lean_object* v_d_257_, lean_object* v_wn_258_, lean_object* v_wr_259_, lean_object* v_q_260_, lean_object* v_r_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(v_00_u03b1_250_, v_inst_251_, v_inst_252_, v_w_253_, v_aig_254_, v_curr_255_, v_n_256_, v_d_257_, v_wn_258_, v_wr_259_, v_q_260_, v_r_261_);
lean_dec(v_wr_259_);
lean_dec(v_wn_258_);
lean_dec_ref(v_n_256_);
lean_dec(v_curr_255_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(lean_object* v_curr_263_, lean_object* v_h__1_264_, lean_object* v_h__2_265_){
_start:
{
lean_object* v_zero_266_; uint8_t v_isZero_267_; 
v_zero_266_ = lean_unsigned_to_nat(0u);
v_isZero_267_ = lean_nat_dec_eq(v_curr_263_, v_zero_266_);
if (v_isZero_267_ == 1)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_h__2_265_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_apply_1(v_h__1_264_, v___x_268_);
return v___x_269_;
}
else
{
lean_object* v_one_270_; lean_object* v_n_271_; lean_object* v___x_272_; 
lean_dec(v_h__1_264_);
v_one_270_ = lean_unsigned_to_nat(1u);
v_n_271_ = lean_nat_sub(v_curr_263_, v_one_270_);
v___x_272_ = lean_apply_1(v_h__2_265_, v_n_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(lean_object* v_curr_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(v_curr_273_, v_h__1_274_, v_h__2_275_);
lean_dec(v_curr_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object* v_motive_277_, lean_object* v_curr_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
lean_object* v_zero_281_; uint8_t v_isZero_282_; 
v_zero_281_ = lean_unsigned_to_nat(0u);
v_isZero_282_ = lean_nat_dec_eq(v_curr_278_, v_zero_281_);
if (v_isZero_282_ == 1)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_h__2_280_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_apply_1(v_h__1_279_, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v_one_285_; lean_object* v_n_286_; lean_object* v___x_287_; 
lean_dec(v_h__1_279_);
v_one_285_ = lean_unsigned_to_nat(1u);
v_n_286_ = lean_nat_sub(v_curr_278_, v_one_285_);
v___x_287_ = lean_apply_1(v_h__2_280_, v_n_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(lean_object* v_motive_288_, lean_object* v_curr_289_, lean_object* v_h__1_290_, lean_object* v_h__2_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(v_motive_288_, v_curr_289_, v_h__1_290_, v_h__2_291_);
lean_dec(v_curr_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_w_295_, lean_object* v_aig_296_, lean_object* v_input_297_){
_start:
{
lean_object* v_lhs_298_; lean_object* v_rhs_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_333_; 
v_lhs_298_ = lean_ctor_get(v_input_297_, 0);
v_rhs_299_ = lean_ctor_get(v_input_297_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_input_297_);
if (v_isSharedCheck_333_ == 0)
{
v___x_301_ = v_input_297_;
v_isShared_302_ = v_isSharedCheck_333_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_rhs_299_);
lean_inc(v_lhs_298_);
lean_dec(v_input_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_333_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_zero_305_; lean_object* v___x_307_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = l_BitVec_ofNat(v_w_295_, v___x_303_);
v_zero_305_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_295_, v___x_304_);
lean_dec(v___x_304_);
lean_inc_ref(v_zero_305_);
lean_inc_ref(v_rhs_299_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_zero_305_);
lean_ctor_set(v___x_301_, 0, v_rhs_299_);
v___x_307_ = v___x_301_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_rhs_299_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_zero_305_);
v___x_307_ = v_reuseFailAlloc_332_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v_res_308_; lean_object* v_aig_309_; lean_object* v_ref_310_; lean_object* v_res_311_; lean_object* v_aig_312_; lean_object* v_q_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_330_; 
lean_inc_ref_n(v_inst_294_, 2);
lean_inc_ref_n(v_inst_293_, 2);
v_res_308_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(v_inst_293_, v_inst_294_, v_w_295_, v_aig_296_, v___x_307_);
lean_dec_ref(v___x_307_);
v_aig_309_ = lean_ctor_get(v_res_308_, 0);
lean_inc_ref(v_aig_309_);
v_ref_310_ = lean_ctor_get(v_res_308_, 1);
lean_inc_ref(v_ref_310_);
lean_dec_ref(v_res_308_);
lean_inc_ref_n(v_zero_305_, 2);
lean_inc(v_w_295_);
v_res_311_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_293_, v_inst_294_, v_w_295_, v_aig_309_, v_w_295_, v_lhs_298_, v_rhs_299_, v_w_295_, v___x_303_, v_zero_305_, v_zero_305_);
lean_dec_ref(v_lhs_298_);
v_aig_312_ = lean_ctor_get(v_res_311_, 0);
v_q_313_ = lean_ctor_get(v_res_311_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_res_311_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_res_311_, 2);
lean_dec(v_unused_331_);
v___x_315_ = v_res_311_;
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_q_313_);
lean_inc(v_aig_312_);
lean_dec(v_res_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_gate_317_; uint8_t v_invert_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_329_; 
v_gate_317_ = lean_ctor_get(v_ref_310_, 0);
v_invert_318_ = lean_ctor_get_uint8(v_ref_310_, sizeof(void*)*1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_ref_310_);
if (v_isSharedCheck_329_ == 0)
{
v___x_320_ = v_ref_310_;
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_gate_317_);
lean_dec(v_ref_310_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_discr_323_; 
if (v_isShared_321_ == 0)
{
v_discr_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_gate_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_328_, sizeof(void*)*1, v_invert_318_);
v_discr_323_ = v_reuseFailAlloc_328_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 2, v_q_313_);
lean_ctor_set(v___x_315_, 1, v_zero_305_);
lean_ctor_set(v___x_315_, 0, v_discr_323_);
v___x_325_ = v___x_315_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_discr_323_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_zero_305_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_q_313_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_293_, v_inst_294_, v_w_295_, v_aig_312_, v___x_325_);
lean_dec(v_w_295_);
return v___x_326_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object* v_00_u03b1_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_w_337_, lean_object* v_aig_338_, lean_object* v_input_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(v_inst_335_, v_inst_336_, v_w_337_, v_aig_338_, v_input_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter___redArg(lean_object* v_input_341_, lean_object* v_h__1_342_){
_start:
{
lean_object* v_lhs_343_; lean_object* v_rhs_344_; lean_object* v___x_345_; 
v_lhs_343_ = lean_ctor_get(v_input_341_, 0);
lean_inc_ref(v_lhs_343_);
v_rhs_344_ = lean_ctor_get(v_input_341_, 1);
lean_inc_ref(v_rhs_344_);
lean_dec_ref(v_input_341_);
v___x_345_ = lean_apply_2(v_h__1_342_, v_lhs_343_, v_rhs_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter(lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_w_349_, lean_object* v_aig_350_, lean_object* v_motive_351_, lean_object* v_input_352_, lean_object* v_h__1_353_){
_start:
{
lean_object* v_lhs_354_; lean_object* v_rhs_355_; lean_object* v___x_356_; 
v_lhs_354_ = lean_ctor_get(v_input_352_, 0);
lean_inc_ref(v_lhs_354_);
v_rhs_355_ = lean_ctor_get(v_input_352_, 1);
lean_inc_ref(v_rhs_355_);
lean_dec_ref(v_input_352_);
v___x_356_ = lean_apply_2(v_h__1_353_, v_lhs_354_, v_rhs_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter___boxed(lean_object* v_00_u03b1_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_w_360_, lean_object* v_aig_361_, lean_object* v_motive_362_, lean_object* v_input_363_, lean_object* v_h__1_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter(v_00_u03b1_357_, v_inst_358_, v_inst_359_, v_w_360_, v_aig_361_, v_motive_362_, v_input_363_, v_h__1_364_);
lean_dec_ref(v_aig_361_);
lean_dec(v_w_360_);
lean_dec_ref(v_inst_359_);
lean_dec_ref(v_inst_358_);
return v_res_365_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
}
#ifdef __cplusplus
}
#endif
