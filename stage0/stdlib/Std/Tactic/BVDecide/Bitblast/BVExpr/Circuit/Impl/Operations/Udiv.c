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
lean_object* lean_bool_to_nat(uint8_t);
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
uint8_t lean_bool_not(uint8_t);
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
v___x_16_ = lean_bool_to_nat(v_invert_10_);
v___x_17_ = lean_nat_lor(v___x_15_, v___x_16_);
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
lean_object* v___x_85_; lean_object* v_wn_86_; lean_object* v_wr_87_; lean_object* v___y_89_; uint8_t v___x_147_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v_wn_86_ = lean_nat_sub(v_wn_81_, v___x_85_);
v_wr_87_ = lean_nat_add(v_wr_82_, v___x_85_);
v___x_147_ = lean_nat_dec_lt(v_wn_86_, v_w_77_);
if (v___x_147_ == 0)
{
lean_object* v_falseRef_148_; 
v_falseRef_148_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0));
v___y_89_ = v_falseRef_148_;
goto v___jp_88_;
}
else
{
lean_object* v_ref_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; 
v_ref_149_ = lean_array_fget_borrowed(v_n_79_, v_wn_86_);
v___x_150_ = lean_nat_shiftr(v_ref_149_, v___x_85_);
v___x_151_ = lean_nat_land(v___x_85_, v_ref_149_);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_nat_dec_eq(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_bool_not(v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_154_);
v___y_89_ = v___x_155_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v_res_91_; lean_object* v_aig_92_; lean_object* v_vec_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_146_; 
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_r_84_);
lean_ctor_set(v___x_90_, 1, v___y_89_);
v_res_91_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_77_, v_aig_78_, v___x_90_);
v_aig_92_ = lean_ctor_get(v_res_91_, 0);
v_vec_93_ = lean_ctor_get(v_res_91_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_res_91_);
if (v_isSharedCheck_146_ == 0)
{
v___x_95_ = v_res_91_;
v_isShared_96_ = v_isSharedCheck_146_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_vec_93_);
lean_inc(v_aig_92_);
lean_dec(v_res_91_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_146_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v_falseRef_97_; lean_object* v___x_99_; 
v_falseRef_97_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0));
lean_inc_ref(v_q_83_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v_falseRef_97_);
lean_ctor_set(v___x_95_, 0, v_q_83_);
v___x_99_ = v___x_95_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_q_83_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_falseRef_97_);
v___x_99_ = v_reuseFailAlloc_145_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v_res_100_; lean_object* v_aig_101_; lean_object* v_vec_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_144_; 
v_res_100_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_77_, v_aig_92_, v___x_99_);
v_aig_101_ = lean_ctor_get(v_res_100_, 0);
v_vec_102_ = lean_ctor_get(v_res_100_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_res_100_);
if (v_isSharedCheck_144_ == 0)
{
v___x_104_ = v_res_100_;
v_isShared_105_ = v_isSharedCheck_144_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_vec_102_);
lean_inc(v_aig_101_);
lean_dec(v_res_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_144_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_trueRef_106_; lean_object* v___x_108_; 
v_trueRef_106_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1));
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_trueRef_106_);
lean_ctor_set(v___x_104_, 0, v_q_83_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_q_83_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_trueRef_106_);
v___x_108_ = v_reuseFailAlloc_143_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v_res_109_; lean_object* v_aig_110_; lean_object* v_vec_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_142_; 
v_res_109_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_77_, v_aig_101_, v___x_108_);
v_aig_110_ = lean_ctor_get(v_res_109_, 0);
v_vec_111_ = lean_ctor_get(v_res_109_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_res_109_);
if (v_isSharedCheck_142_ == 0)
{
v___x_113_ = v_res_109_;
v_isShared_114_ = v_isSharedCheck_142_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_vec_111_);
lean_inc(v_aig_110_);
lean_dec(v_res_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_142_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
lean_inc_ref(v_vec_93_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_d_80_);
lean_ctor_set(v___x_113_, 0, v_vec_93_);
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_vec_93_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_d_80_);
v___x_116_ = v_reuseFailAlloc_141_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v_res_117_; lean_object* v_aig_118_; lean_object* v_vec_119_; lean_object* v_res_120_; lean_object* v_aig_121_; lean_object* v_ref_122_; lean_object* v___x_123_; lean_object* v_res_124_; lean_object* v_aig_125_; lean_object* v_vec_126_; lean_object* v_gate_127_; uint8_t v_invert_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_140_; 
lean_inc_ref(v___x_116_);
lean_inc_ref_n(v_inst_76_, 3);
lean_inc_ref_n(v_inst_75_, 3);
v_res_117_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_110_, v___x_116_);
v_aig_118_ = lean_ctor_get(v_res_117_, 0);
lean_inc_ref(v_aig_118_);
v_vec_119_ = lean_ctor_get(v_res_117_, 1);
lean_inc_ref(v_vec_119_);
lean_dec_ref(v_res_117_);
lean_inc(v_w_77_);
v_res_120_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_118_, v___x_116_);
v_aig_121_ = lean_ctor_get(v_res_120_, 0);
lean_inc_ref(v_aig_121_);
v_ref_122_ = lean_ctor_get(v_res_120_, 1);
lean_inc_ref_n(v_ref_122_, 2);
lean_dec_ref(v_res_120_);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_ref_122_);
lean_ctor_set(v___x_123_, 1, v_vec_102_);
lean_ctor_set(v___x_123_, 2, v_vec_111_);
v_res_124_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_121_, v___x_123_);
v_aig_125_ = lean_ctor_get(v_res_124_, 0);
lean_inc_ref(v_aig_125_);
v_vec_126_ = lean_ctor_get(v_res_124_, 1);
lean_inc_ref(v_vec_126_);
lean_dec_ref(v_res_124_);
v_gate_127_ = lean_ctor_get(v_ref_122_, 0);
v_invert_128_ = lean_ctor_get_uint8(v_ref_122_, sizeof(void*)*1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_ref_122_);
if (v_isSharedCheck_140_ == 0)
{
v___x_130_ = v_ref_122_;
v_isShared_131_ = v_isSharedCheck_140_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_gate_127_);
lean_dec(v_ref_122_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_140_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_discr_133_; 
if (v_isShared_131_ == 0)
{
v_discr_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_gate_127_);
lean_ctor_set_uint8(v_reuseFailAlloc_139_, sizeof(void*)*1, v_invert_128_);
v_discr_133_ = v_reuseFailAlloc_139_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v_res_135_; lean_object* v_aig_136_; lean_object* v_vec_137_; lean_object* v___x_138_; 
v___x_134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_134_, 0, v_discr_133_);
lean_ctor_set(v___x_134_, 1, v_vec_93_);
lean_ctor_set(v___x_134_, 2, v_vec_119_);
v_res_135_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_75_, v_inst_76_, v_w_77_, v_aig_125_, v___x_134_);
lean_dec(v_w_77_);
v_aig_136_ = lean_ctor_get(v_res_135_, 0);
lean_inc_ref(v_aig_136_);
v_vec_137_ = lean_ctor_get(v_res_135_, 1);
lean_inc_ref(v_vec_137_);
lean_dec_ref(v_res_135_);
v___x_138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_138_, 0, v_aig_136_);
lean_ctor_set(v___x_138_, 1, v_wn_86_);
lean_ctor_set(v___x_138_, 2, v_wr_87_);
lean_ctor_set(v___x_138_, 3, v_vec_126_);
lean_ctor_set(v___x_138_, 4, v_vec_137_);
return v___x_138_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___boxed(lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_w_158_, lean_object* v_aig_159_, lean_object* v_n_160_, lean_object* v_d_161_, lean_object* v_wn_162_, lean_object* v_wr_163_, lean_object* v_q_164_, lean_object* v_r_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_156_, v_inst_157_, v_w_158_, v_aig_159_, v_n_160_, v_d_161_, v_wn_162_, v_wr_163_, v_q_164_, v_r_165_);
lean_dec(v_wr_163_);
lean_dec(v_wn_162_);
lean_dec_ref(v_n_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object* v_00_u03b1_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_w_170_, lean_object* v_aig_171_, lean_object* v_n_172_, lean_object* v_d_173_, lean_object* v_wn_174_, lean_object* v_wr_175_, lean_object* v_q_176_, lean_object* v_r_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_168_, v_inst_169_, v_w_170_, v_aig_171_, v_n_172_, v_d_173_, v_wn_174_, v_wr_175_, v_q_176_, v_r_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___boxed(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_w_182_, lean_object* v_aig_183_, lean_object* v_n_184_, lean_object* v_d_185_, lean_object* v_wn_186_, lean_object* v_wr_187_, lean_object* v_q_188_, lean_object* v_r_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(v_00_u03b1_179_, v_inst_180_, v_inst_181_, v_w_182_, v_aig_183_, v_n_184_, v_d_185_, v_wn_186_, v_wr_187_, v_q_188_, v_r_189_);
lean_dec(v_wr_187_);
lean_dec(v_wn_186_);
lean_dec_ref(v_n_184_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_w_193_, lean_object* v_aig_194_, lean_object* v_curr_195_, lean_object* v_n_196_, lean_object* v_d_197_, lean_object* v_wn_198_, lean_object* v_wr_199_, lean_object* v_q_200_, lean_object* v_r_201_){
_start:
{
lean_object* v_zero_202_; uint8_t v_isZero_203_; 
v_zero_202_ = lean_unsigned_to_nat(0u);
v_isZero_203_ = lean_nat_dec_eq(v_curr_195_, v_zero_202_);
if (v_isZero_203_ == 1)
{
lean_object* v___x_204_; 
lean_dec_ref(v_d_197_);
lean_dec(v_w_193_);
lean_dec_ref(v_inst_192_);
lean_dec_ref(v_inst_191_);
v___x_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_204_, 0, v_aig_194_);
lean_ctor_set(v___x_204_, 1, v_q_200_);
lean_ctor_set(v___x_204_, 2, v_r_201_);
return v___x_204_;
}
else
{
lean_object* v_res_205_; lean_object* v_aig_206_; lean_object* v_wn_207_; lean_object* v_wr_208_; lean_object* v_q_209_; lean_object* v_r_210_; lean_object* v_one_211_; lean_object* v_n_212_; lean_object* v_res_213_; lean_object* v_aig_214_; lean_object* v_q_215_; lean_object* v_r_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_inc_ref(v_d_197_);
lean_inc(v_w_193_);
lean_inc_ref(v_inst_192_);
lean_inc_ref(v_inst_191_);
v_res_205_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_191_, v_inst_192_, v_w_193_, v_aig_194_, v_n_196_, v_d_197_, v_wn_198_, v_wr_199_, v_q_200_, v_r_201_);
v_aig_206_ = lean_ctor_get(v_res_205_, 0);
lean_inc_ref(v_aig_206_);
v_wn_207_ = lean_ctor_get(v_res_205_, 1);
lean_inc(v_wn_207_);
v_wr_208_ = lean_ctor_get(v_res_205_, 2);
lean_inc(v_wr_208_);
v_q_209_ = lean_ctor_get(v_res_205_, 3);
lean_inc_ref(v_q_209_);
v_r_210_ = lean_ctor_get(v_res_205_, 4);
lean_inc_ref(v_r_210_);
lean_dec_ref(v_res_205_);
v_one_211_ = lean_unsigned_to_nat(1u);
v_n_212_ = lean_nat_sub(v_curr_195_, v_one_211_);
v_res_213_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_191_, v_inst_192_, v_w_193_, v_aig_206_, v_n_212_, v_n_196_, v_d_197_, v_wn_207_, v_wr_208_, v_q_209_, v_r_210_);
lean_dec(v_wr_208_);
lean_dec(v_wn_207_);
lean_dec(v_n_212_);
v_aig_214_ = lean_ctor_get(v_res_213_, 0);
v_q_215_ = lean_ctor_get(v_res_213_, 1);
v_r_216_ = lean_ctor_get(v_res_213_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v_res_213_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v_res_213_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_r_216_);
lean_inc(v_q_215_);
lean_inc(v_aig_214_);
lean_dec(v_res_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_aig_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_q_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_r_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg___boxed(lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_w_226_, lean_object* v_aig_227_, lean_object* v_curr_228_, lean_object* v_n_229_, lean_object* v_d_230_, lean_object* v_wn_231_, lean_object* v_wr_232_, lean_object* v_q_233_, lean_object* v_r_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_224_, v_inst_225_, v_w_226_, v_aig_227_, v_curr_228_, v_n_229_, v_d_230_, v_wn_231_, v_wr_232_, v_q_233_, v_r_234_);
lean_dec(v_wr_232_);
lean_dec(v_wn_231_);
lean_dec_ref(v_n_229_);
lean_dec(v_curr_228_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object* v_00_u03b1_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_w_239_, lean_object* v_aig_240_, lean_object* v_curr_241_, lean_object* v_n_242_, lean_object* v_d_243_, lean_object* v_wn_244_, lean_object* v_wr_245_, lean_object* v_q_246_, lean_object* v_r_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_237_, v_inst_238_, v_w_239_, v_aig_240_, v_curr_241_, v_n_242_, v_d_243_, v_wn_244_, v_wr_245_, v_q_246_, v_r_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___boxed(lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_w_252_, lean_object* v_aig_253_, lean_object* v_curr_254_, lean_object* v_n_255_, lean_object* v_d_256_, lean_object* v_wn_257_, lean_object* v_wr_258_, lean_object* v_q_259_, lean_object* v_r_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(v_00_u03b1_249_, v_inst_250_, v_inst_251_, v_w_252_, v_aig_253_, v_curr_254_, v_n_255_, v_d_256_, v_wn_257_, v_wr_258_, v_q_259_, v_r_260_);
lean_dec(v_wr_258_);
lean_dec(v_wn_257_);
lean_dec_ref(v_n_255_);
lean_dec(v_curr_254_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(lean_object* v_curr_262_, lean_object* v_h__1_263_, lean_object* v_h__2_264_){
_start:
{
lean_object* v_zero_265_; uint8_t v_isZero_266_; 
v_zero_265_ = lean_unsigned_to_nat(0u);
v_isZero_266_ = lean_nat_dec_eq(v_curr_262_, v_zero_265_);
if (v_isZero_266_ == 1)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_h__2_264_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_apply_1(v_h__1_263_, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v_one_269_; lean_object* v_n_270_; lean_object* v___x_271_; 
lean_dec(v_h__1_263_);
v_one_269_ = lean_unsigned_to_nat(1u);
v_n_270_ = lean_nat_sub(v_curr_262_, v_one_269_);
v___x_271_ = lean_apply_1(v_h__2_264_, v_n_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(lean_object* v_curr_272_, lean_object* v_h__1_273_, lean_object* v_h__2_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(v_curr_272_, v_h__1_273_, v_h__2_274_);
lean_dec(v_curr_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object* v_motive_276_, lean_object* v_curr_277_, lean_object* v_h__1_278_, lean_object* v_h__2_279_){
_start:
{
lean_object* v_zero_280_; uint8_t v_isZero_281_; 
v_zero_280_ = lean_unsigned_to_nat(0u);
v_isZero_281_ = lean_nat_dec_eq(v_curr_277_, v_zero_280_);
if (v_isZero_281_ == 1)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_h__2_279_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_apply_1(v_h__1_278_, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v_one_284_; lean_object* v_n_285_; lean_object* v___x_286_; 
lean_dec(v_h__1_278_);
v_one_284_ = lean_unsigned_to_nat(1u);
v_n_285_ = lean_nat_sub(v_curr_277_, v_one_284_);
v___x_286_ = lean_apply_1(v_h__2_279_, v_n_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(lean_object* v_motive_287_, lean_object* v_curr_288_, lean_object* v_h__1_289_, lean_object* v_h__2_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(v_motive_287_, v_curr_288_, v_h__1_289_, v_h__2_290_);
lean_dec(v_curr_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_w_294_, lean_object* v_aig_295_, lean_object* v_input_296_){
_start:
{
lean_object* v_lhs_297_; lean_object* v_rhs_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_332_; 
v_lhs_297_ = lean_ctor_get(v_input_296_, 0);
v_rhs_298_ = lean_ctor_get(v_input_296_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_input_296_);
if (v_isSharedCheck_332_ == 0)
{
v___x_300_ = v_input_296_;
v_isShared_301_ = v_isSharedCheck_332_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_rhs_298_);
lean_inc(v_lhs_297_);
lean_dec(v_input_296_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_332_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_zero_304_; lean_object* v___x_306_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = l_BitVec_ofNat(v_w_294_, v___x_302_);
v_zero_304_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_294_, v___x_303_);
lean_dec(v___x_303_);
lean_inc_ref(v_zero_304_);
lean_inc_ref(v_rhs_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_zero_304_);
lean_ctor_set(v___x_300_, 0, v_rhs_298_);
v___x_306_ = v___x_300_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_rhs_298_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_zero_304_);
v___x_306_ = v_reuseFailAlloc_331_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v_res_307_; lean_object* v_aig_308_; lean_object* v_ref_309_; lean_object* v_res_310_; lean_object* v_aig_311_; lean_object* v_q_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_329_; 
lean_inc_ref_n(v_inst_293_, 2);
lean_inc_ref_n(v_inst_292_, 2);
v_res_307_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(v_inst_292_, v_inst_293_, v_w_294_, v_aig_295_, v___x_306_);
lean_dec_ref(v___x_306_);
v_aig_308_ = lean_ctor_get(v_res_307_, 0);
lean_inc_ref(v_aig_308_);
v_ref_309_ = lean_ctor_get(v_res_307_, 1);
lean_inc_ref(v_ref_309_);
lean_dec_ref(v_res_307_);
lean_inc_ref_n(v_zero_304_, 2);
lean_inc(v_w_294_);
v_res_310_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_292_, v_inst_293_, v_w_294_, v_aig_308_, v_w_294_, v_lhs_297_, v_rhs_298_, v_w_294_, v___x_302_, v_zero_304_, v_zero_304_);
lean_dec_ref(v_lhs_297_);
v_aig_311_ = lean_ctor_get(v_res_310_, 0);
v_q_312_ = lean_ctor_get(v_res_310_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_res_310_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_res_310_, 2);
lean_dec(v_unused_330_);
v___x_314_ = v_res_310_;
v_isShared_315_ = v_isSharedCheck_329_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_q_312_);
lean_inc(v_aig_311_);
lean_dec(v_res_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_329_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_gate_316_; uint8_t v_invert_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_328_; 
v_gate_316_ = lean_ctor_get(v_ref_309_, 0);
v_invert_317_ = lean_ctor_get_uint8(v_ref_309_, sizeof(void*)*1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_ref_309_);
if (v_isSharedCheck_328_ == 0)
{
v___x_319_ = v_ref_309_;
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_gate_316_);
lean_dec(v_ref_309_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_discr_322_; 
if (v_isShared_320_ == 0)
{
v_discr_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_gate_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*1, v_invert_317_);
v_discr_322_ = v_reuseFailAlloc_327_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 2, v_q_312_);
lean_ctor_set(v___x_314_, 1, v_zero_304_);
lean_ctor_set(v___x_314_, 0, v_discr_322_);
v___x_324_ = v___x_314_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_discr_322_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_zero_304_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_q_312_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_292_, v_inst_293_, v_w_294_, v_aig_311_, v___x_324_);
lean_dec(v_w_294_);
return v___x_325_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object* v_00_u03b1_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_w_336_, lean_object* v_aig_337_, lean_object* v_input_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(v_inst_334_, v_inst_335_, v_w_336_, v_aig_337_, v_input_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter___redArg(lean_object* v_input_340_, lean_object* v_h__1_341_){
_start:
{
lean_object* v_lhs_342_; lean_object* v_rhs_343_; lean_object* v___x_344_; 
v_lhs_342_ = lean_ctor_get(v_input_340_, 0);
lean_inc_ref(v_lhs_342_);
v_rhs_343_ = lean_ctor_get(v_input_340_, 1);
lean_inc_ref(v_rhs_343_);
lean_dec_ref(v_input_340_);
v___x_344_ = lean_apply_2(v_h__1_341_, v_lhs_342_, v_rhs_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter(lean_object* v_00_u03b1_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_w_348_, lean_object* v_aig_349_, lean_object* v_motive_350_, lean_object* v_input_351_, lean_object* v_h__1_352_){
_start:
{
lean_object* v_lhs_353_; lean_object* v_rhs_354_; lean_object* v___x_355_; 
v_lhs_353_ = lean_ctor_get(v_input_351_, 0);
lean_inc_ref(v_lhs_353_);
v_rhs_354_ = lean_ctor_get(v_input_351_, 1);
lean_inc_ref(v_rhs_354_);
lean_dec_ref(v_input_351_);
v___x_355_ = lean_apply_2(v_h__1_352_, v_lhs_353_, v_rhs_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter___boxed(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_w_359_, lean_object* v_aig_360_, lean_object* v_motive_361_, lean_object* v_input_362_, lean_object* v_h__1_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_match__1_splitter(v_00_u03b1_356_, v_inst_357_, v_inst_358_, v_w_359_, v_aig_360_, v_motive_361_, v_input_362_, v_h__1_363_);
lean_dec_ref(v_aig_360_);
lean_dec(v_w_359_);
lean_dec_ref(v_inst_358_);
lean_dec_ref(v_inst_357_);
return v_res_364_;
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
