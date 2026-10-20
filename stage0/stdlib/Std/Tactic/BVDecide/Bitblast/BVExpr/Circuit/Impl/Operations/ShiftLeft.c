// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.If import Init.Omega
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(lean_object* v_w_1_, lean_object* v_aig_2_, lean_object* v_input_3_, lean_object* v_distance_4_, lean_object* v_curr_5_, lean_object* v_s_6_){
_start:
{
lean_object* v_gate_8_; uint8_t v_invert_9_; uint8_t v___x_18_; 
v___x_18_ = lean_nat_dec_lt(v_curr_5_, v_w_1_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
lean_dec(v_curr_5_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v_aig_2_);
lean_ctor_set(v___x_19_, 1, v_s_6_);
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
v___x_20_ = lean_nat_dec_lt(v_curr_5_, v_distance_4_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v_ref_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_21_ = lean_nat_sub(v_curr_5_, v_distance_4_);
v_ref_22_ = lean_array_fget_borrowed(v_input_3_, v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_shiftr(v_ref_22_, v___x_23_);
v___x_25_ = lean_nat_land(v___x_23_, v_ref_22_);
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_nat_dec_eq(v___x_25_, v___x_26_);
lean_dec(v___x_25_);
if (v___x_27_ == 0)
{
v_gate_8_ = v___x_24_;
v_invert_9_ = v___x_18_;
goto v___jp_7_;
}
else
{
v_gate_8_ = v___x_24_;
v_invert_9_ = v___x_20_;
goto v___jp_7_;
}
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_s_31_; 
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_add(v_curr_5_, v___x_28_);
lean_dec(v_curr_5_);
v___x_30_ = lean_unsigned_to_nat(0u);
v_s_31_ = lean_array_push(v_s_6_, v___x_30_);
v_curr_5_ = v___x_29_;
v_s_6_ = v_s_31_;
goto _start;
}
}
v___jp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_s_16_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_curr_5_, v___x_10_);
lean_dec(v_curr_5_);
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lean_nat_mul(v_gate_8_, v___x_12_);
lean_dec(v_gate_8_);
v___x_14_ = l_Bool_toNat(v_invert_9_);
v___x_15_ = lean_nat_lor(v___x_13_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_13_);
v_s_16_ = lean_array_push(v_s_6_, v___x_15_);
v_curr_5_ = v___x_11_;
v_s_6_ = v_s_16_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___boxed(lean_object* v_w_33_, lean_object* v_aig_34_, lean_object* v_input_35_, lean_object* v_distance_36_, lean_object* v_curr_37_, lean_object* v_s_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_33_, v_aig_34_, v_input_35_, v_distance_36_, v_curr_37_, v_s_38_);
lean_dec(v_distance_36_);
lean_dec_ref(v_input_35_);
lean_dec(v_w_33_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_w_43_, lean_object* v_aig_44_, lean_object* v_input_45_, lean_object* v_distance_46_, lean_object* v_curr_47_, lean_object* v_hcurr_48_, lean_object* v_s_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_43_, v_aig_44_, v_input_45_, v_distance_46_, v_curr_47_, v_s_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___boxed(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_w_54_, lean_object* v_aig_55_, lean_object* v_input_56_, lean_object* v_distance_57_, lean_object* v_curr_58_, lean_object* v_hcurr_59_, lean_object* v_s_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(v_00_u03b1_51_, v_inst_52_, v_inst_53_, v_w_54_, v_aig_55_, v_input_56_, v_distance_57_, v_curr_58_, v_hcurr_59_, v_s_60_);
lean_dec(v_distance_57_);
lean_dec_ref(v_input_56_);
lean_dec(v_w_54_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_52_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object* v_w_62_, lean_object* v_aig_63_, lean_object* v_target_64_){
_start:
{
lean_object* v_vec_65_; lean_object* v_distance_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_vec_65_ = lean_ctor_get(v_target_64_, 0);
v_distance_66_ = lean_ctor_get(v_target_64_, 1);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_mk_empty_array_with_capacity(v_w_62_);
v___x_69_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_62_, v_aig_63_, v_vec_65_, v_distance_66_, v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg___boxed(lean_object* v_w_70_, lean_object* v_aig_71_, lean_object* v_target_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_70_, v_aig_71_, v_target_72_);
lean_dec_ref(v_target_72_);
lean_dec(v_w_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_w_77_, lean_object* v_aig_78_, lean_object* v_target_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_77_, v_aig_78_, v_target_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___boxed(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_w_84_, lean_object* v_aig_85_, lean_object* v_target_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(v_00_u03b1_81_, v_inst_82_, v_inst_83_, v_w_84_, v_aig_85_, v_target_86_);
lean_dec_ref(v_target_86_);
lean_dec(v_w_84_);
lean_dec_ref(v_inst_83_);
lean_dec_ref(v_inst_82_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_w_90_, lean_object* v_aig_91_, lean_object* v_target_92_){
_start:
{
lean_object* v_n_93_; lean_object* v_lhs_94_; lean_object* v_rhs_95_; lean_object* v_pow_96_; uint8_t v___x_97_; 
v_n_93_ = lean_ctor_get(v_target_92_, 0);
v_lhs_94_ = lean_ctor_get(v_target_92_, 1);
v_rhs_95_ = lean_ctor_get(v_target_92_, 2);
v_pow_96_ = lean_ctor_get(v_target_92_, 3);
v___x_97_ = lean_nat_dec_lt(v_pow_96_, v_n_93_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec_ref(v_inst_89_);
lean_dec_ref(v_inst_88_);
lean_inc_ref(v_lhs_94_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v_aig_91_);
lean_ctor_set(v___x_98_, 1, v_lhs_94_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_res_102_; lean_object* v_aig_103_; lean_object* v_vec_104_; lean_object* v___y_106_; lean_object* v_ref_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_99_ = lean_unsigned_to_nat(2u);
v___x_100_ = lean_nat_pow(v___x_99_, v_pow_96_);
lean_inc_ref(v_lhs_94_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_lhs_94_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v_res_102_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_90_, v_aig_91_, v___x_101_);
lean_dec_ref_known(v___x_101_, 2);
v_aig_103_ = lean_ctor_get(v_res_102_, 0);
lean_inc_ref(v_aig_103_);
v_vec_104_ = lean_ctor_get(v_res_102_, 1);
lean_inc_ref(v_vec_104_);
lean_dec_ref(v_res_102_);
v_ref_109_ = lean_array_fget_borrowed(v_rhs_95_, v_pow_96_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_shiftr(v_ref_109_, v___x_110_);
v___x_112_ = lean_nat_land(v___x_110_, v_ref_109_);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_nat_dec_eq(v___x_112_, v___x_113_);
lean_dec(v___x_112_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_97_);
v___y_106_ = v___x_115_;
goto v___jp_105_;
}
else
{
uint8_t v___x_116_; lean_object* v___x_117_; 
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___y_106_ = v___x_117_;
goto v___jp_105_;
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_inc_ref(v_lhs_94_);
v___x_107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_107_, 0, v___y_106_);
lean_ctor_set(v___x_107_, 1, v_vec_104_);
lean_ctor_set(v___x_107_, 2, v_lhs_94_);
v___x_108_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_88_, v_inst_89_, v_w_90_, v_aig_103_, v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg___boxed(lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_w_120_, lean_object* v_aig_121_, lean_object* v_target_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_118_, v_inst_119_, v_w_120_, v_aig_121_, v_target_122_);
lean_dec_ref(v_target_122_);
lean_dec(v_w_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(lean_object* v_00_u03b1_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_w_127_, lean_object* v_aig_128_, lean_object* v_target_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_125_, v_inst_126_, v_w_127_, v_aig_128_, v_target_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___boxed(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_w_134_, lean_object* v_aig_135_, lean_object* v_target_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(v_00_u03b1_131_, v_inst_132_, v_inst_133_, v_w_134_, v_aig_135_, v_target_136_);
lean_dec_ref(v_target_136_);
lean_dec(v_w_134_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_w_140_, lean_object* v_n_141_, lean_object* v_aig_142_, lean_object* v_distance_143_, lean_object* v_curr_144_, lean_object* v_acc_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_sub(v_n_141_, v___x_146_);
v___x_148_ = lean_nat_dec_lt(v_curr_144_, v___x_147_);
lean_dec(v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_dec(v_curr_144_);
lean_dec_ref(v_distance_143_);
lean_dec(v_n_141_);
lean_dec_ref(v_inst_139_);
lean_dec_ref(v_inst_138_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_aig_142_);
lean_ctor_set(v___x_149_, 1, v_acc_145_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_res_152_; lean_object* v_aig_153_; lean_object* v_vec_154_; 
v___x_150_ = lean_nat_add(v_curr_144_, v___x_146_);
lean_dec(v_curr_144_);
lean_inc(v___x_150_);
lean_inc_ref(v_distance_143_);
lean_inc(v_n_141_);
v___x_151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_151_, 0, v_n_141_);
lean_ctor_set(v___x_151_, 1, v_acc_145_);
lean_ctor_set(v___x_151_, 2, v_distance_143_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
lean_inc_ref(v_inst_139_);
lean_inc_ref(v_inst_138_);
v_res_152_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_138_, v_inst_139_, v_w_140_, v_aig_142_, v___x_151_);
lean_dec_ref_known(v___x_151_, 4);
v_aig_153_ = lean_ctor_get(v_res_152_, 0);
lean_inc_ref(v_aig_153_);
v_vec_154_ = lean_ctor_get(v_res_152_, 1);
lean_inc_ref(v_vec_154_);
lean_dec_ref(v_res_152_);
v_aig_142_ = v_aig_153_;
v_curr_144_ = v___x_150_;
v_acc_145_ = v_vec_154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg___boxed(lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_w_158_, lean_object* v_n_159_, lean_object* v_aig_160_, lean_object* v_distance_161_, lean_object* v_curr_162_, lean_object* v_acc_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_156_, v_inst_157_, v_w_158_, v_n_159_, v_aig_160_, v_distance_161_, v_curr_162_, v_acc_163_);
lean_dec(v_w_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_w_168_, lean_object* v_n_169_, lean_object* v_aig_170_, lean_object* v_distance_171_, lean_object* v_curr_172_, lean_object* v_acc_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_166_, v_inst_167_, v_w_168_, v_n_169_, v_aig_170_, v_distance_171_, v_curr_172_, v_acc_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___boxed(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_w_178_, lean_object* v_n_179_, lean_object* v_aig_180_, lean_object* v_distance_181_, lean_object* v_curr_182_, lean_object* v_acc_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(v_00_u03b1_175_, v_inst_176_, v_inst_177_, v_w_178_, v_n_179_, v_aig_180_, v_distance_181_, v_curr_182_, v_acc_183_);
lean_dec(v_w_178_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_w_187_, lean_object* v_aig_188_, lean_object* v_target_189_){
_start:
{
lean_object* v_n_190_; lean_object* v_target_191_; lean_object* v_distance_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_n_190_ = lean_ctor_get(v_target_189_, 0);
lean_inc(v_n_190_);
v_target_191_ = lean_ctor_get(v_target_189_, 1);
lean_inc_ref(v_target_191_);
v_distance_192_ = lean_ctor_get(v_target_189_, 2);
lean_inc_ref(v_distance_192_);
lean_dec_ref(v_target_189_);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_dec_eq(v_n_190_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v_res_196_; lean_object* v_aig_197_; lean_object* v_vec_198_; lean_object* v___x_199_; 
lean_inc_ref(v_distance_192_);
lean_inc(v_n_190_);
v___x_195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_195_, 0, v_n_190_);
lean_ctor_set(v___x_195_, 1, v_target_191_);
lean_ctor_set(v___x_195_, 2, v_distance_192_);
lean_ctor_set(v___x_195_, 3, v___x_193_);
lean_inc_ref(v_inst_186_);
lean_inc_ref(v_inst_185_);
v_res_196_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_185_, v_inst_186_, v_w_187_, v_aig_188_, v___x_195_);
lean_dec_ref_known(v___x_195_, 4);
v_aig_197_ = lean_ctor_get(v_res_196_, 0);
lean_inc_ref(v_aig_197_);
v_vec_198_ = lean_ctor_get(v_res_196_, 1);
lean_inc_ref(v_vec_198_);
lean_dec_ref(v_res_196_);
v___x_199_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_185_, v_inst_186_, v_w_187_, v_n_190_, v_aig_197_, v_distance_192_, v___x_193_, v_vec_198_);
return v___x_199_;
}
else
{
lean_object* v___x_200_; 
lean_dec_ref(v_distance_192_);
lean_dec(v_n_190_);
lean_dec_ref(v_inst_186_);
lean_dec_ref(v_inst_185_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_aig_188_);
lean_ctor_set(v___x_200_, 1, v_target_191_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg___boxed(lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_w_203_, lean_object* v_aig_204_, lean_object* v_target_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_201_, v_inst_202_, v_w_203_, v_aig_204_, v_target_205_);
lean_dec(v_w_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(lean_object* v_00_u03b1_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_w_210_, lean_object* v_aig_211_, lean_object* v_target_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_208_, v_inst_209_, v_w_210_, v_aig_211_, v_target_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___boxed(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_w_217_, lean_object* v_aig_218_, lean_object* v_target_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(v_00_u03b1_214_, v_inst_215_, v_inst_216_, v_w_217_, v_aig_218_, v_target_219_);
lean_dec(v_w_217_);
return v_res_220_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin);
}
#ifdef __cplusplus
}
#endif
