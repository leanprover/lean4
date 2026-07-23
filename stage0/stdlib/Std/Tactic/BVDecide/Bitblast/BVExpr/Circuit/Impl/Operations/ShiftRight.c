// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(lean_object* v_w_1_, lean_object* v_aig_2_, lean_object* v_input_3_, lean_object* v_distance_4_, lean_object* v_curr_5_, lean_object* v_s_6_){
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
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_nat_add(v_distance_4_, v_curr_5_);
v___x_21_ = lean_nat_dec_lt(v___x_20_, v_w_1_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_s_25_; 
lean_dec(v___x_20_);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_add(v_curr_5_, v___x_22_);
lean_dec(v_curr_5_);
v___x_24_ = l_Bool_toNat(v___x_21_);
v_s_25_ = lean_array_push(v_s_6_, v___x_24_);
v_curr_5_ = v___x_23_;
v_s_6_ = v_s_25_;
goto _start;
}
else
{
lean_object* v_ref_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_ref_27_ = lean_array_fget_borrowed(v_input_3_, v___x_20_);
lean_dec(v___x_20_);
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_shiftr(v_ref_27_, v___x_28_);
v___x_30_ = lean_nat_land(v___x_28_, v_ref_27_);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_nat_dec_eq(v___x_30_, v___x_31_);
lean_dec(v___x_30_);
if (v___x_32_ == 0)
{
v_gate_8_ = v___x_29_;
v_invert_9_ = v___x_21_;
goto v___jp_7_;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = 0;
v_gate_8_ = v___x_29_;
v_invert_9_ = v___x_33_;
goto v___jp_7_;
}
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg___boxed(lean_object* v_w_34_, lean_object* v_aig_35_, lean_object* v_input_36_, lean_object* v_distance_37_, lean_object* v_curr_38_, lean_object* v_s_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_34_, v_aig_35_, v_input_36_, v_distance_37_, v_curr_38_, v_s_39_);
lean_dec(v_distance_37_);
lean_dec_ref(v_input_36_);
lean_dec(v_w_34_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_w_44_, lean_object* v_aig_45_, lean_object* v_input_46_, lean_object* v_distance_47_, lean_object* v_curr_48_, lean_object* v_hcurr_49_, lean_object* v_s_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_44_, v_aig_45_, v_input_46_, v_distance_47_, v_curr_48_, v_s_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___boxed(lean_object* v_00_u03b1_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_w_55_, lean_object* v_aig_56_, lean_object* v_input_57_, lean_object* v_distance_58_, lean_object* v_curr_59_, lean_object* v_hcurr_60_, lean_object* v_s_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(v_00_u03b1_52_, v_inst_53_, v_inst_54_, v_w_55_, v_aig_56_, v_input_57_, v_distance_58_, v_curr_59_, v_hcurr_60_, v_s_61_);
lean_dec(v_distance_58_);
lean_dec_ref(v_input_57_);
lean_dec(v_w_55_);
lean_dec_ref(v_inst_54_);
lean_dec_ref(v_inst_53_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(lean_object* v_w_63_, lean_object* v_aig_64_, lean_object* v_target_65_){
_start:
{
lean_object* v_vec_66_; lean_object* v_distance_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_vec_66_ = lean_ctor_get(v_target_65_, 0);
v_distance_67_ = lean_ctor_get(v_target_65_, 1);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_mk_empty_array_with_capacity(v_w_63_);
v___x_70_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_63_, v_aig_64_, v_vec_66_, v_distance_67_, v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg___boxed(lean_object* v_w_71_, lean_object* v_aig_72_, lean_object* v_target_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_71_, v_aig_72_, v_target_73_);
lean_dec_ref(v_target_73_);
lean_dec(v_w_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(lean_object* v_00_u03b1_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_w_78_, lean_object* v_aig_79_, lean_object* v_target_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_78_, v_aig_79_, v_target_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___boxed(lean_object* v_00_u03b1_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_w_85_, lean_object* v_aig_86_, lean_object* v_target_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(v_00_u03b1_82_, v_inst_83_, v_inst_84_, v_w_85_, v_aig_86_, v_target_87_);
lean_dec_ref(v_target_87_);
lean_dec(v_w_85_);
lean_dec_ref(v_inst_84_);
lean_dec_ref(v_inst_83_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(lean_object* v_w_89_, lean_object* v_input_90_, lean_object* v_distance_91_, lean_object* v_curr_92_, lean_object* v_s_93_){
_start:
{
lean_object* v_gate_95_; uint8_t v_invert_96_; uint8_t v___x_105_; 
v___x_105_ = lean_nat_dec_lt(v_curr_92_, v_w_89_);
if (v___x_105_ == 0)
{
lean_dec(v_curr_92_);
return v_s_93_;
}
else
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_nat_add(v_distance_91_, v_curr_92_);
v___x_107_ = lean_nat_dec_lt(v___x_106_, v_w_89_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v_gate_110_; uint8_t v_invert_111_; lean_object* v___x_119_; lean_object* v_ref_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
lean_dec(v___x_106_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_sub(v_w_89_, v___x_108_);
v_ref_120_ = lean_array_fget_borrowed(v_input_90_, v___x_119_);
lean_dec(v___x_119_);
v___x_121_ = lean_nat_shiftr(v_ref_120_, v___x_108_);
v___x_122_ = lean_nat_land(v___x_108_, v_ref_120_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_nat_dec_eq(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
if (v___x_124_ == 0)
{
v_gate_110_ = v___x_121_;
v_invert_111_ = v___x_105_;
goto v___jp_109_;
}
else
{
v_gate_110_ = v___x_121_;
v_invert_111_ = v___x_107_;
goto v___jp_109_;
}
v___jp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_s_117_; 
v___x_112_ = lean_nat_add(v_curr_92_, v___x_108_);
lean_dec(v_curr_92_);
v___x_113_ = lean_unsigned_to_nat(2u);
v___x_114_ = lean_nat_mul(v_gate_110_, v___x_113_);
lean_dec(v_gate_110_);
v___x_115_ = l_Bool_toNat(v_invert_111_);
v___x_116_ = lean_nat_lor(v___x_114_, v___x_115_);
lean_dec(v___x_115_);
lean_dec(v___x_114_);
v_s_117_ = lean_array_push(v_s_93_, v___x_116_);
v_curr_92_ = v___x_112_;
v_s_93_ = v_s_117_;
goto _start;
}
}
else
{
lean_object* v_ref_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_ref_125_ = lean_array_fget_borrowed(v_input_90_, v___x_106_);
lean_dec(v___x_106_);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_shiftr(v_ref_125_, v___x_126_);
v___x_128_ = lean_nat_land(v___x_126_, v_ref_125_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_nat_dec_eq(v___x_128_, v___x_129_);
lean_dec(v___x_128_);
if (v___x_130_ == 0)
{
v_gate_95_ = v___x_127_;
v_invert_96_ = v___x_107_;
goto v___jp_94_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
v_gate_95_ = v___x_127_;
v_invert_96_ = v___x_131_;
goto v___jp_94_;
}
}
}
v___jp_94_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_s_103_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_curr_92_, v___x_97_);
lean_dec(v_curr_92_);
v___x_99_ = lean_unsigned_to_nat(2u);
v___x_100_ = lean_nat_mul(v_gate_95_, v___x_99_);
lean_dec(v_gate_95_);
v___x_101_ = l_Bool_toNat(v_invert_96_);
v___x_102_ = lean_nat_lor(v___x_100_, v___x_101_);
lean_dec(v___x_101_);
lean_dec(v___x_100_);
v_s_103_ = lean_array_push(v_s_93_, v___x_102_);
v_curr_92_ = v___x_98_;
v_s_93_ = v_s_103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg___boxed(lean_object* v_w_132_, lean_object* v_input_133_, lean_object* v_distance_134_, lean_object* v_curr_135_, lean_object* v_s_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_132_, v_input_133_, v_distance_134_, v_curr_135_, v_s_136_);
lean_dec(v_distance_134_);
lean_dec_ref(v_input_133_);
lean_dec(v_w_132_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(lean_object* v_00_u03b1_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_w_141_, lean_object* v_aig_142_, lean_object* v_input_143_, lean_object* v_distance_144_, lean_object* v_curr_145_, lean_object* v_hcurr_146_, lean_object* v_s_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_141_, v_input_143_, v_distance_144_, v_curr_145_, v_s_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___boxed(lean_object* v_00_u03b1_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_w_152_, lean_object* v_aig_153_, lean_object* v_input_154_, lean_object* v_distance_155_, lean_object* v_curr_156_, lean_object* v_hcurr_157_, lean_object* v_s_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(v_00_u03b1_149_, v_inst_150_, v_inst_151_, v_w_152_, v_aig_153_, v_input_154_, v_distance_155_, v_curr_156_, v_hcurr_157_, v_s_158_);
lean_dec(v_distance_155_);
lean_dec_ref(v_input_154_);
lean_dec_ref(v_aig_153_);
lean_dec(v_w_152_);
lean_dec_ref(v_inst_151_);
lean_dec_ref(v_inst_150_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(lean_object* v_w_160_, lean_object* v_aig_161_, lean_object* v_target_162_){
_start:
{
lean_object* v_vec_163_; lean_object* v_distance_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_174_; 
v_vec_163_ = lean_ctor_get(v_target_162_, 0);
v_distance_164_ = lean_ctor_get(v_target_162_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_target_162_);
if (v_isSharedCheck_174_ == 0)
{
v___x_166_ = v_target_162_;
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_distance_164_);
lean_inc(v_vec_163_);
lean_dec(v_target_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_mk_empty_array_with_capacity(v_w_160_);
v___x_170_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_160_, v_vec_163_, v_distance_164_, v___x_168_, v___x_169_);
lean_dec(v_distance_164_);
lean_dec_ref(v_vec_163_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_170_);
lean_ctor_set(v___x_166_, 0, v_aig_161_);
v___x_172_ = v___x_166_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_aig_161_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg___boxed(lean_object* v_w_175_, lean_object* v_aig_176_, lean_object* v_target_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_175_, v_aig_176_, v_target_177_);
lean_dec(v_w_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_w_182_, lean_object* v_aig_183_, lean_object* v_target_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_182_, v_aig_183_, v_target_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___boxed(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_w_189_, lean_object* v_aig_190_, lean_object* v_target_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(v_00_u03b1_186_, v_inst_187_, v_inst_188_, v_w_189_, v_aig_190_, v_target_191_);
lean_dec(v_w_189_);
lean_dec_ref(v_inst_188_);
lean_dec_ref(v_inst_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_w_195_, lean_object* v_aig_196_, lean_object* v_target_197_){
_start:
{
lean_object* v_n_198_; lean_object* v_lhs_199_; lean_object* v_rhs_200_; lean_object* v_pow_201_; uint8_t v___x_202_; 
v_n_198_ = lean_ctor_get(v_target_197_, 0);
v_lhs_199_ = lean_ctor_get(v_target_197_, 1);
v_rhs_200_ = lean_ctor_get(v_target_197_, 2);
v_pow_201_ = lean_ctor_get(v_target_197_, 3);
v___x_202_ = lean_nat_dec_lt(v_pow_201_, v_n_198_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec_ref(v_inst_194_);
lean_dec_ref(v_inst_193_);
lean_inc_ref(v_lhs_199_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_aig_196_);
lean_ctor_set(v___x_203_, 1, v_lhs_199_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_res_207_; lean_object* v_aig_208_; lean_object* v_vec_209_; lean_object* v___y_211_; lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_204_ = lean_unsigned_to_nat(2u);
v___x_205_ = lean_nat_pow(v___x_204_, v_pow_201_);
lean_inc_ref(v_lhs_199_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_lhs_199_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v_res_207_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_195_, v_aig_196_, v___x_206_);
lean_dec_ref_known(v___x_206_, 2);
v_aig_208_ = lean_ctor_get(v_res_207_, 0);
lean_inc_ref(v_aig_208_);
v_vec_209_ = lean_ctor_get(v_res_207_, 1);
lean_inc_ref(v_vec_209_);
lean_dec_ref(v_res_207_);
v_ref_214_ = lean_array_fget_borrowed(v_rhs_200_, v_pow_201_);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_shiftr(v_ref_214_, v___x_215_);
v___x_217_ = lean_nat_land(v___x_215_, v_ref_214_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_dec_eq(v___x_217_, v___x_218_);
lean_dec(v___x_217_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_220_, 0, v___x_216_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1, v___x_202_);
v___y_211_ = v___x_220_;
goto v___jp_210_;
}
else
{
uint8_t v___x_221_; lean_object* v___x_222_; 
v___x_221_ = 0;
v___x_222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_222_, 0, v___x_216_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_221_);
v___y_211_ = v___x_222_;
goto v___jp_210_;
}
v___jp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_inc_ref(v_lhs_199_);
v___x_212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_212_, 0, v___y_211_);
lean_ctor_set(v___x_212_, 1, v_vec_209_);
lean_ctor_set(v___x_212_, 2, v_lhs_199_);
v___x_213_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_193_, v_inst_194_, v_w_195_, v_aig_208_, v___x_212_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg___boxed(lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_w_225_, lean_object* v_aig_226_, lean_object* v_target_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_223_, v_inst_224_, v_w_225_, v_aig_226_, v_target_227_);
lean_dec_ref(v_target_227_);
lean_dec(v_w_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(lean_object* v_00_u03b1_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_w_232_, lean_object* v_aig_233_, lean_object* v_target_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_230_, v_inst_231_, v_w_232_, v_aig_233_, v_target_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___boxed(lean_object* v_00_u03b1_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_w_239_, lean_object* v_aig_240_, lean_object* v_target_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(v_00_u03b1_236_, v_inst_237_, v_inst_238_, v_w_239_, v_aig_240_, v_target_241_);
lean_dec_ref(v_target_241_);
lean_dec(v_w_239_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_w_245_, lean_object* v_n_246_, lean_object* v_aig_247_, lean_object* v_distance_248_, lean_object* v_curr_249_, lean_object* v_acc_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_nat_sub(v_n_246_, v___x_251_);
v___x_253_ = lean_nat_dec_lt(v_curr_249_, v___x_252_);
lean_dec(v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_curr_249_);
lean_dec_ref(v_distance_248_);
lean_dec(v_n_246_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_aig_247_);
lean_ctor_set(v___x_254_, 1, v_acc_250_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_res_257_; lean_object* v_aig_258_; lean_object* v_vec_259_; 
v___x_255_ = lean_nat_add(v_curr_249_, v___x_251_);
lean_dec(v_curr_249_);
lean_inc(v___x_255_);
lean_inc_ref(v_distance_248_);
lean_inc(v_n_246_);
v___x_256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_256_, 0, v_n_246_);
lean_ctor_set(v___x_256_, 1, v_acc_250_);
lean_ctor_set(v___x_256_, 2, v_distance_248_);
lean_ctor_set(v___x_256_, 3, v___x_255_);
lean_inc_ref(v_inst_244_);
lean_inc_ref(v_inst_243_);
v_res_257_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_243_, v_inst_244_, v_w_245_, v_aig_247_, v___x_256_);
lean_dec_ref_known(v___x_256_, 4);
v_aig_258_ = lean_ctor_get(v_res_257_, 0);
lean_inc_ref(v_aig_258_);
v_vec_259_ = lean_ctor_get(v_res_257_, 1);
lean_inc_ref(v_vec_259_);
lean_dec_ref(v_res_257_);
v_aig_247_ = v_aig_258_;
v_curr_249_ = v___x_255_;
v_acc_250_ = v_vec_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg___boxed(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_w_263_, lean_object* v_n_264_, lean_object* v_aig_265_, lean_object* v_distance_266_, lean_object* v_curr_267_, lean_object* v_acc_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_261_, v_inst_262_, v_w_263_, v_n_264_, v_aig_265_, v_distance_266_, v_curr_267_, v_acc_268_);
lean_dec(v_w_263_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(lean_object* v_00_u03b1_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_w_273_, lean_object* v_n_274_, lean_object* v_aig_275_, lean_object* v_distance_276_, lean_object* v_curr_277_, lean_object* v_acc_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_271_, v_inst_272_, v_w_273_, v_n_274_, v_aig_275_, v_distance_276_, v_curr_277_, v_acc_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___boxed(lean_object* v_00_u03b1_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_w_283_, lean_object* v_n_284_, lean_object* v_aig_285_, lean_object* v_distance_286_, lean_object* v_curr_287_, lean_object* v_acc_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(v_00_u03b1_280_, v_inst_281_, v_inst_282_, v_w_283_, v_n_284_, v_aig_285_, v_distance_286_, v_curr_287_, v_acc_288_);
lean_dec(v_w_283_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_w_292_, lean_object* v_aig_293_, lean_object* v_target_294_){
_start:
{
lean_object* v_n_295_; lean_object* v_target_296_; lean_object* v_distance_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_n_295_ = lean_ctor_get(v_target_294_, 0);
lean_inc(v_n_295_);
v_target_296_ = lean_ctor_get(v_target_294_, 1);
lean_inc_ref(v_target_296_);
v_distance_297_ = lean_ctor_get(v_target_294_, 2);
lean_inc_ref(v_distance_297_);
lean_dec_ref(v_target_294_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v_n_295_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v_res_301_; lean_object* v_aig_302_; lean_object* v_vec_303_; lean_object* v___x_304_; 
lean_inc_ref(v_distance_297_);
lean_inc(v_n_295_);
v___x_300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_300_, 0, v_n_295_);
lean_ctor_set(v___x_300_, 1, v_target_296_);
lean_ctor_set(v___x_300_, 2, v_distance_297_);
lean_ctor_set(v___x_300_, 3, v___x_298_);
lean_inc_ref(v_inst_291_);
lean_inc_ref(v_inst_290_);
v_res_301_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_290_, v_inst_291_, v_w_292_, v_aig_293_, v___x_300_);
lean_dec_ref_known(v___x_300_, 4);
v_aig_302_ = lean_ctor_get(v_res_301_, 0);
lean_inc_ref(v_aig_302_);
v_vec_303_ = lean_ctor_get(v_res_301_, 1);
lean_inc_ref(v_vec_303_);
lean_dec_ref(v_res_301_);
v___x_304_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_290_, v_inst_291_, v_w_292_, v_n_295_, v_aig_302_, v_distance_297_, v___x_298_, v_vec_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
lean_dec_ref(v_distance_297_);
lean_dec(v_n_295_);
lean_dec_ref(v_inst_291_);
lean_dec_ref(v_inst_290_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_aig_293_);
lean_ctor_set(v___x_305_, 1, v_target_296_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg___boxed(lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_w_308_, lean_object* v_aig_309_, lean_object* v_target_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(v_inst_306_, v_inst_307_, v_w_308_, v_aig_309_, v_target_310_);
lean_dec(v_w_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(lean_object* v_00_u03b1_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_w_315_, lean_object* v_aig_316_, lean_object* v_target_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(v_inst_313_, v_inst_314_, v_w_315_, v_aig_316_, v_target_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___boxed(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_w_322_, lean_object* v_aig_323_, lean_object* v_target_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(v_00_u03b1_319_, v_inst_320_, v_inst_321_, v_w_322_, v_aig_323_, v_target_324_);
lean_dec(v_w_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_w_328_, lean_object* v_aig_329_, lean_object* v_target_330_){
_start:
{
lean_object* v_n_331_; lean_object* v_lhs_332_; lean_object* v_rhs_333_; lean_object* v_pow_334_; uint8_t v___x_335_; 
v_n_331_ = lean_ctor_get(v_target_330_, 0);
v_lhs_332_ = lean_ctor_get(v_target_330_, 1);
v_rhs_333_ = lean_ctor_get(v_target_330_, 2);
v_pow_334_ = lean_ctor_get(v_target_330_, 3);
v___x_335_ = lean_nat_dec_lt(v_pow_334_, v_n_331_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v_inst_327_);
lean_dec_ref(v_inst_326_);
lean_inc_ref(v_lhs_332_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_aig_329_);
lean_ctor_set(v___x_336_, 1, v_lhs_332_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_res_340_; lean_object* v_aig_341_; lean_object* v_vec_342_; lean_object* v___y_344_; lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = lean_nat_pow(v___x_337_, v_pow_334_);
lean_inc_ref(v_lhs_332_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_lhs_332_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v_res_340_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_328_, v_aig_329_, v___x_339_);
v_aig_341_ = lean_ctor_get(v_res_340_, 0);
lean_inc_ref(v_aig_341_);
v_vec_342_ = lean_ctor_get(v_res_340_, 1);
lean_inc_ref(v_vec_342_);
lean_dec_ref(v_res_340_);
v_ref_347_ = lean_array_fget_borrowed(v_rhs_333_, v_pow_334_);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_shiftr(v_ref_347_, v___x_348_);
v___x_350_ = lean_nat_land(v___x_348_, v_ref_347_);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_nat_dec_eq(v___x_350_, v___x_351_);
lean_dec(v___x_350_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_353_, 0, v___x_349_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*1, v___x_335_);
v___y_344_ = v___x_353_;
goto v___jp_343_;
}
else
{
uint8_t v___x_354_; lean_object* v___x_355_; 
v___x_354_ = 0;
v___x_355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_355_, 0, v___x_349_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_354_);
v___y_344_ = v___x_355_;
goto v___jp_343_;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_inc_ref(v_lhs_332_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v___y_344_);
lean_ctor_set(v___x_345_, 1, v_vec_342_);
lean_ctor_set(v___x_345_, 2, v_lhs_332_);
v___x_346_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_326_, v_inst_327_, v_w_328_, v_aig_341_, v___x_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg___boxed(lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_w_358_, lean_object* v_aig_359_, lean_object* v_target_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_356_, v_inst_357_, v_w_358_, v_aig_359_, v_target_360_);
lean_dec_ref(v_target_360_);
lean_dec(v_w_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(lean_object* v_00_u03b1_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_w_365_, lean_object* v_aig_366_, lean_object* v_target_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_363_, v_inst_364_, v_w_365_, v_aig_366_, v_target_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___boxed(lean_object* v_00_u03b1_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_w_372_, lean_object* v_aig_373_, lean_object* v_target_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(v_00_u03b1_369_, v_inst_370_, v_inst_371_, v_w_372_, v_aig_373_, v_target_374_);
lean_dec_ref(v_target_374_);
lean_dec(v_w_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_w_378_, lean_object* v_n_379_, lean_object* v_aig_380_, lean_object* v_distance_381_, lean_object* v_curr_382_, lean_object* v_acc_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_sub(v_n_379_, v___x_384_);
v___x_386_ = lean_nat_dec_lt(v_curr_382_, v___x_385_);
lean_dec(v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_curr_382_);
lean_dec_ref(v_distance_381_);
lean_dec(v_n_379_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_aig_380_);
lean_ctor_set(v___x_387_, 1, v_acc_383_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_res_390_; lean_object* v_aig_391_; lean_object* v_vec_392_; 
v___x_388_ = lean_nat_add(v_curr_382_, v___x_384_);
lean_dec(v_curr_382_);
lean_inc(v___x_388_);
lean_inc_ref(v_distance_381_);
lean_inc(v_n_379_);
v___x_389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_389_, 0, v_n_379_);
lean_ctor_set(v___x_389_, 1, v_acc_383_);
lean_ctor_set(v___x_389_, 2, v_distance_381_);
lean_ctor_set(v___x_389_, 3, v___x_388_);
lean_inc_ref(v_inst_377_);
lean_inc_ref(v_inst_376_);
v_res_390_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_376_, v_inst_377_, v_w_378_, v_aig_380_, v___x_389_);
lean_dec_ref_known(v___x_389_, 4);
v_aig_391_ = lean_ctor_get(v_res_390_, 0);
lean_inc_ref(v_aig_391_);
v_vec_392_ = lean_ctor_get(v_res_390_, 1);
lean_inc_ref(v_vec_392_);
lean_dec_ref(v_res_390_);
v_aig_380_ = v_aig_391_;
v_curr_382_ = v___x_388_;
v_acc_383_ = v_vec_392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg___boxed(lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_w_396_, lean_object* v_n_397_, lean_object* v_aig_398_, lean_object* v_distance_399_, lean_object* v_curr_400_, lean_object* v_acc_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_394_, v_inst_395_, v_w_396_, v_n_397_, v_aig_398_, v_distance_399_, v_curr_400_, v_acc_401_);
lean_dec(v_w_396_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_w_406_, lean_object* v_n_407_, lean_object* v_aig_408_, lean_object* v_distance_409_, lean_object* v_curr_410_, lean_object* v_acc_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_404_, v_inst_405_, v_w_406_, v_n_407_, v_aig_408_, v_distance_409_, v_curr_410_, v_acc_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___boxed(lean_object* v_00_u03b1_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_w_416_, lean_object* v_n_417_, lean_object* v_aig_418_, lean_object* v_distance_419_, lean_object* v_curr_420_, lean_object* v_acc_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(v_00_u03b1_413_, v_inst_414_, v_inst_415_, v_w_416_, v_n_417_, v_aig_418_, v_distance_419_, v_curr_420_, v_acc_421_);
lean_dec(v_w_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_w_425_, lean_object* v_aig_426_, lean_object* v_target_427_){
_start:
{
lean_object* v_n_428_; lean_object* v_target_429_; lean_object* v_distance_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_n_428_ = lean_ctor_get(v_target_427_, 0);
lean_inc(v_n_428_);
v_target_429_ = lean_ctor_get(v_target_427_, 1);
lean_inc_ref(v_target_429_);
v_distance_430_ = lean_ctor_get(v_target_427_, 2);
lean_inc_ref(v_distance_430_);
lean_dec_ref(v_target_427_);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_nat_dec_eq(v_n_428_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v_res_434_; lean_object* v_aig_435_; lean_object* v_vec_436_; lean_object* v___x_437_; 
lean_inc_ref(v_distance_430_);
lean_inc(v_n_428_);
v___x_433_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_433_, 0, v_n_428_);
lean_ctor_set(v___x_433_, 1, v_target_429_);
lean_ctor_set(v___x_433_, 2, v_distance_430_);
lean_ctor_set(v___x_433_, 3, v___x_431_);
lean_inc_ref(v_inst_424_);
lean_inc_ref(v_inst_423_);
v_res_434_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_423_, v_inst_424_, v_w_425_, v_aig_426_, v___x_433_);
lean_dec_ref_known(v___x_433_, 4);
v_aig_435_ = lean_ctor_get(v_res_434_, 0);
lean_inc_ref(v_aig_435_);
v_vec_436_ = lean_ctor_get(v_res_434_, 1);
lean_inc_ref(v_vec_436_);
lean_dec_ref(v_res_434_);
v___x_437_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_423_, v_inst_424_, v_w_425_, v_n_428_, v_aig_435_, v_distance_430_, v___x_431_, v_vec_436_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; 
lean_dec_ref(v_distance_430_);
lean_dec(v_n_428_);
lean_dec_ref(v_inst_424_);
lean_dec_ref(v_inst_423_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v_aig_426_);
lean_ctor_set(v___x_438_, 1, v_target_429_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg___boxed(lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_w_441_, lean_object* v_aig_442_, lean_object* v_target_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(v_inst_439_, v_inst_440_, v_w_441_, v_aig_442_, v_target_443_);
lean_dec(v_w_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(lean_object* v_00_u03b1_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_w_448_, lean_object* v_aig_449_, lean_object* v_target_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(v_inst_446_, v_inst_447_, v_w_448_, v_aig_449_, v_target_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___boxed(lean_object* v_00_u03b1_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_w_455_, lean_object* v_aig_456_, lean_object* v_target_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(v_00_u03b1_452_, v_inst_453_, v_inst_454_, v_w_455_, v_aig_456_, v_target_457_);
lean_dec(v_w_455_);
return v_res_458_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(uint8_t builtin) {
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
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(builtin);
}
#ifdef __cplusplus
}
#endif
