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
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v_s_27_; 
lean_dec(v___x_20_);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_add(v_curr_5_, v___x_22_);
lean_dec(v_curr_5_);
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = l_Bool_toNat(v___x_21_);
v___x_26_ = lean_nat_lor(v___x_24_, v___x_25_);
lean_dec(v___x_25_);
v_s_27_ = lean_array_push(v_s_6_, v___x_26_);
v_curr_5_ = v___x_23_;
v_s_6_ = v_s_27_;
goto _start;
}
else
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_ref_29_ = lean_array_fget_borrowed(v_input_3_, v___x_20_);
lean_dec(v___x_20_);
v___x_30_ = lean_unsigned_to_nat(1u);
v___x_31_ = lean_nat_shiftr(v_ref_29_, v___x_30_);
v___x_32_ = lean_nat_land(v___x_30_, v_ref_29_);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_nat_dec_eq(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
if (v___x_34_ == 0)
{
v_gate_8_ = v___x_31_;
v_invert_9_ = v___x_21_;
goto v___jp_7_;
}
else
{
uint8_t v___x_35_; 
v___x_35_ = 0;
v_gate_8_ = v___x_31_;
v_invert_9_ = v___x_35_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg___boxed(lean_object* v_w_36_, lean_object* v_aig_37_, lean_object* v_input_38_, lean_object* v_distance_39_, lean_object* v_curr_40_, lean_object* v_s_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_36_, v_aig_37_, v_input_38_, v_distance_39_, v_curr_40_, v_s_41_);
lean_dec(v_distance_39_);
lean_dec_ref(v_input_38_);
lean_dec(v_w_36_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_w_46_, lean_object* v_aig_47_, lean_object* v_input_48_, lean_object* v_distance_49_, lean_object* v_curr_50_, lean_object* v_hcurr_51_, lean_object* v_s_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_46_, v_aig_47_, v_input_48_, v_distance_49_, v_curr_50_, v_s_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___boxed(lean_object* v_00_u03b1_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_w_57_, lean_object* v_aig_58_, lean_object* v_input_59_, lean_object* v_distance_60_, lean_object* v_curr_61_, lean_object* v_hcurr_62_, lean_object* v_s_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(v_00_u03b1_54_, v_inst_55_, v_inst_56_, v_w_57_, v_aig_58_, v_input_59_, v_distance_60_, v_curr_61_, v_hcurr_62_, v_s_63_);
lean_dec(v_distance_60_);
lean_dec_ref(v_input_59_);
lean_dec(v_w_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_inst_55_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(lean_object* v_w_65_, lean_object* v_aig_66_, lean_object* v_target_67_){
_start:
{
lean_object* v_vec_68_; lean_object* v_distance_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_vec_68_ = lean_ctor_get(v_target_67_, 0);
v_distance_69_ = lean_ctor_get(v_target_67_, 1);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_mk_empty_array_with_capacity(v_w_65_);
v___x_72_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_65_, v_aig_66_, v_vec_68_, v_distance_69_, v___x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg___boxed(lean_object* v_w_73_, lean_object* v_aig_74_, lean_object* v_target_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_73_, v_aig_74_, v_target_75_);
lean_dec_ref(v_target_75_);
lean_dec(v_w_73_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(lean_object* v_00_u03b1_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_w_80_, lean_object* v_aig_81_, lean_object* v_target_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_80_, v_aig_81_, v_target_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___boxed(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_w_87_, lean_object* v_aig_88_, lean_object* v_target_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(v_00_u03b1_84_, v_inst_85_, v_inst_86_, v_w_87_, v_aig_88_, v_target_89_);
lean_dec_ref(v_target_89_);
lean_dec(v_w_87_);
lean_dec_ref(v_inst_86_);
lean_dec_ref(v_inst_85_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(lean_object* v_w_91_, lean_object* v_input_92_, lean_object* v_distance_93_, lean_object* v_curr_94_, lean_object* v_s_95_){
_start:
{
lean_object* v_gate_97_; uint8_t v_invert_98_; uint8_t v___x_107_; 
v___x_107_ = lean_nat_dec_lt(v_curr_94_, v_w_91_);
if (v___x_107_ == 0)
{
lean_dec(v_curr_94_);
return v_s_95_;
}
else
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_nat_add(v_distance_93_, v_curr_94_);
v___x_109_ = lean_nat_dec_lt(v___x_108_, v_w_91_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v_gate_112_; uint8_t v_invert_113_; lean_object* v___x_121_; lean_object* v_ref_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
lean_dec(v___x_108_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_sub(v_w_91_, v___x_110_);
v_ref_122_ = lean_array_fget_borrowed(v_input_92_, v___x_121_);
lean_dec(v___x_121_);
v___x_123_ = lean_nat_shiftr(v_ref_122_, v___x_110_);
v___x_124_ = lean_nat_land(v___x_110_, v_ref_122_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_nat_dec_eq(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
v_gate_112_ = v___x_123_;
v_invert_113_ = v___x_107_;
goto v___jp_111_;
}
else
{
v_gate_112_ = v___x_123_;
v_invert_113_ = v___x_109_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_s_119_; 
v___x_114_ = lean_nat_add(v_curr_94_, v___x_110_);
lean_dec(v_curr_94_);
v___x_115_ = lean_unsigned_to_nat(2u);
v___x_116_ = lean_nat_mul(v_gate_112_, v___x_115_);
lean_dec(v_gate_112_);
v___x_117_ = l_Bool_toNat(v_invert_113_);
v___x_118_ = lean_nat_lor(v___x_116_, v___x_117_);
lean_dec(v___x_117_);
lean_dec(v___x_116_);
v_s_119_ = lean_array_push(v_s_95_, v___x_118_);
v_curr_94_ = v___x_114_;
v_s_95_ = v_s_119_;
goto _start;
}
}
else
{
lean_object* v_ref_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_ref_127_ = lean_array_fget_borrowed(v_input_92_, v___x_108_);
lean_dec(v___x_108_);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_shiftr(v_ref_127_, v___x_128_);
v___x_130_ = lean_nat_land(v___x_128_, v_ref_127_);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_nat_dec_eq(v___x_130_, v___x_131_);
lean_dec(v___x_130_);
if (v___x_132_ == 0)
{
v_gate_97_ = v___x_129_;
v_invert_98_ = v___x_109_;
goto v___jp_96_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
v_gate_97_ = v___x_129_;
v_invert_98_ = v___x_133_;
goto v___jp_96_;
}
}
}
v___jp_96_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_s_105_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_curr_94_, v___x_99_);
lean_dec(v_curr_94_);
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_mul(v_gate_97_, v___x_101_);
lean_dec(v_gate_97_);
v___x_103_ = l_Bool_toNat(v_invert_98_);
v___x_104_ = lean_nat_lor(v___x_102_, v___x_103_);
lean_dec(v___x_103_);
lean_dec(v___x_102_);
v_s_105_ = lean_array_push(v_s_95_, v___x_104_);
v_curr_94_ = v___x_100_;
v_s_95_ = v_s_105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg___boxed(lean_object* v_w_134_, lean_object* v_input_135_, lean_object* v_distance_136_, lean_object* v_curr_137_, lean_object* v_s_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_134_, v_input_135_, v_distance_136_, v_curr_137_, v_s_138_);
lean_dec(v_distance_136_);
lean_dec_ref(v_input_135_);
lean_dec(v_w_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_w_143_, lean_object* v_aig_144_, lean_object* v_input_145_, lean_object* v_distance_146_, lean_object* v_curr_147_, lean_object* v_hcurr_148_, lean_object* v_s_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_143_, v_input_145_, v_distance_146_, v_curr_147_, v_s_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___boxed(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_w_154_, lean_object* v_aig_155_, lean_object* v_input_156_, lean_object* v_distance_157_, lean_object* v_curr_158_, lean_object* v_hcurr_159_, lean_object* v_s_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(v_00_u03b1_151_, v_inst_152_, v_inst_153_, v_w_154_, v_aig_155_, v_input_156_, v_distance_157_, v_curr_158_, v_hcurr_159_, v_s_160_);
lean_dec(v_distance_157_);
lean_dec_ref(v_input_156_);
lean_dec_ref(v_aig_155_);
lean_dec(v_w_154_);
lean_dec_ref(v_inst_153_);
lean_dec_ref(v_inst_152_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(lean_object* v_w_162_, lean_object* v_aig_163_, lean_object* v_target_164_){
_start:
{
lean_object* v_vec_165_; lean_object* v_distance_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_176_; 
v_vec_165_ = lean_ctor_get(v_target_164_, 0);
v_distance_166_ = lean_ctor_get(v_target_164_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_target_164_);
if (v_isSharedCheck_176_ == 0)
{
v___x_168_ = v_target_164_;
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_distance_166_);
lean_inc(v_vec_165_);
lean_dec(v_target_164_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_mk_empty_array_with_capacity(v_w_162_);
v___x_172_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_162_, v_vec_165_, v_distance_166_, v___x_170_, v___x_171_);
lean_dec(v_distance_166_);
lean_dec_ref(v_vec_165_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_172_);
lean_ctor_set(v___x_168_, 0, v_aig_163_);
v___x_174_ = v___x_168_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_aig_163_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg___boxed(lean_object* v_w_177_, lean_object* v_aig_178_, lean_object* v_target_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_177_, v_aig_178_, v_target_179_);
lean_dec(v_w_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(lean_object* v_00_u03b1_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_w_184_, lean_object* v_aig_185_, lean_object* v_target_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_184_, v_aig_185_, v_target_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___boxed(lean_object* v_00_u03b1_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_w_191_, lean_object* v_aig_192_, lean_object* v_target_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(v_00_u03b1_188_, v_inst_189_, v_inst_190_, v_w_191_, v_aig_192_, v_target_193_);
lean_dec(v_w_191_);
lean_dec_ref(v_inst_190_);
lean_dec_ref(v_inst_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_w_197_, lean_object* v_aig_198_, lean_object* v_target_199_){
_start:
{
lean_object* v_n_200_; lean_object* v_lhs_201_; lean_object* v_rhs_202_; lean_object* v_pow_203_; uint8_t v___x_204_; 
v_n_200_ = lean_ctor_get(v_target_199_, 0);
v_lhs_201_ = lean_ctor_get(v_target_199_, 1);
v_rhs_202_ = lean_ctor_get(v_target_199_, 2);
v_pow_203_ = lean_ctor_get(v_target_199_, 3);
v___x_204_ = lean_nat_dec_lt(v_pow_203_, v_n_200_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec_ref(v_inst_196_);
lean_dec_ref(v_inst_195_);
lean_inc_ref(v_lhs_201_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v_aig_198_);
lean_ctor_set(v___x_205_, 1, v_lhs_201_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_res_209_; lean_object* v_aig_210_; lean_object* v_vec_211_; lean_object* v___y_213_; lean_object* v_ref_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_206_ = lean_unsigned_to_nat(2u);
v___x_207_ = lean_nat_pow(v___x_206_, v_pow_203_);
lean_inc_ref(v_lhs_201_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_lhs_201_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v_res_209_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_197_, v_aig_198_, v___x_208_);
lean_dec_ref(v___x_208_);
v_aig_210_ = lean_ctor_get(v_res_209_, 0);
lean_inc_ref(v_aig_210_);
v_vec_211_ = lean_ctor_get(v_res_209_, 1);
lean_inc_ref(v_vec_211_);
lean_dec_ref(v_res_209_);
v_ref_216_ = lean_array_fget_borrowed(v_rhs_202_, v_pow_203_);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_shiftr(v_ref_216_, v___x_217_);
v___x_219_ = lean_nat_land(v___x_217_, v_ref_216_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_nat_dec_eq(v___x_219_, v___x_220_);
lean_dec(v___x_219_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_222_, 0, v___x_218_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_204_);
v___y_213_ = v___x_222_;
goto v___jp_212_;
}
else
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_224_, 0, v___x_218_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_223_);
v___y_213_ = v___x_224_;
goto v___jp_212_;
}
v___jp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_inc_ref(v_lhs_201_);
v___x_214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_214_, 0, v___y_213_);
lean_ctor_set(v___x_214_, 1, v_vec_211_);
lean_ctor_set(v___x_214_, 2, v_lhs_201_);
v___x_215_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_195_, v_inst_196_, v_w_197_, v_aig_210_, v___x_214_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg___boxed(lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_w_227_, lean_object* v_aig_228_, lean_object* v_target_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_225_, v_inst_226_, v_w_227_, v_aig_228_, v_target_229_);
lean_dec_ref(v_target_229_);
lean_dec(v_w_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_w_234_, lean_object* v_aig_235_, lean_object* v_target_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_232_, v_inst_233_, v_w_234_, v_aig_235_, v_target_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___boxed(lean_object* v_00_u03b1_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_w_241_, lean_object* v_aig_242_, lean_object* v_target_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(v_00_u03b1_238_, v_inst_239_, v_inst_240_, v_w_241_, v_aig_242_, v_target_243_);
lean_dec_ref(v_target_243_);
lean_dec(v_w_241_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_w_247_, lean_object* v_n_248_, lean_object* v_aig_249_, lean_object* v_distance_250_, lean_object* v_curr_251_, lean_object* v_acc_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_sub(v_n_248_, v___x_253_);
v___x_255_ = lean_nat_dec_lt(v_curr_251_, v___x_254_);
lean_dec(v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_curr_251_);
lean_dec_ref(v_distance_250_);
lean_dec(v_n_248_);
lean_dec_ref(v_inst_246_);
lean_dec_ref(v_inst_245_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_aig_249_);
lean_ctor_set(v___x_256_, 1, v_acc_252_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_res_259_; lean_object* v_aig_260_; lean_object* v_vec_261_; 
v___x_257_ = lean_nat_add(v_curr_251_, v___x_253_);
lean_dec(v_curr_251_);
lean_inc(v___x_257_);
lean_inc_ref(v_distance_250_);
lean_inc(v_n_248_);
v___x_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_258_, 0, v_n_248_);
lean_ctor_set(v___x_258_, 1, v_acc_252_);
lean_ctor_set(v___x_258_, 2, v_distance_250_);
lean_ctor_set(v___x_258_, 3, v___x_257_);
lean_inc_ref(v_inst_246_);
lean_inc_ref(v_inst_245_);
v_res_259_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_245_, v_inst_246_, v_w_247_, v_aig_249_, v___x_258_);
lean_dec_ref(v___x_258_);
v_aig_260_ = lean_ctor_get(v_res_259_, 0);
lean_inc_ref(v_aig_260_);
v_vec_261_ = lean_ctor_get(v_res_259_, 1);
lean_inc_ref(v_vec_261_);
lean_dec_ref(v_res_259_);
v_aig_249_ = v_aig_260_;
v_curr_251_ = v___x_257_;
v_acc_252_ = v_vec_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg___boxed(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_w_265_, lean_object* v_n_266_, lean_object* v_aig_267_, lean_object* v_distance_268_, lean_object* v_curr_269_, lean_object* v_acc_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_263_, v_inst_264_, v_w_265_, v_n_266_, v_aig_267_, v_distance_268_, v_curr_269_, v_acc_270_);
lean_dec(v_w_265_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_w_275_, lean_object* v_n_276_, lean_object* v_aig_277_, lean_object* v_distance_278_, lean_object* v_curr_279_, lean_object* v_acc_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_273_, v_inst_274_, v_w_275_, v_n_276_, v_aig_277_, v_distance_278_, v_curr_279_, v_acc_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___boxed(lean_object* v_00_u03b1_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_w_285_, lean_object* v_n_286_, lean_object* v_aig_287_, lean_object* v_distance_288_, lean_object* v_curr_289_, lean_object* v_acc_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(v_00_u03b1_282_, v_inst_283_, v_inst_284_, v_w_285_, v_n_286_, v_aig_287_, v_distance_288_, v_curr_289_, v_acc_290_);
lean_dec(v_w_285_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_w_294_, lean_object* v_aig_295_, lean_object* v_target_296_){
_start:
{
lean_object* v_n_297_; lean_object* v_target_298_; lean_object* v_distance_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_n_297_ = lean_ctor_get(v_target_296_, 0);
lean_inc(v_n_297_);
v_target_298_ = lean_ctor_get(v_target_296_, 1);
lean_inc_ref(v_target_298_);
v_distance_299_ = lean_ctor_get(v_target_296_, 2);
lean_inc_ref(v_distance_299_);
lean_dec_ref(v_target_296_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_eq(v_n_297_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v_res_303_; lean_object* v_aig_304_; lean_object* v_vec_305_; lean_object* v___x_306_; 
lean_inc_ref(v_distance_299_);
lean_inc(v_n_297_);
v___x_302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_302_, 0, v_n_297_);
lean_ctor_set(v___x_302_, 1, v_target_298_);
lean_ctor_set(v___x_302_, 2, v_distance_299_);
lean_ctor_set(v___x_302_, 3, v___x_300_);
lean_inc_ref(v_inst_293_);
lean_inc_ref(v_inst_292_);
v_res_303_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_292_, v_inst_293_, v_w_294_, v_aig_295_, v___x_302_);
lean_dec_ref(v___x_302_);
v_aig_304_ = lean_ctor_get(v_res_303_, 0);
lean_inc_ref(v_aig_304_);
v_vec_305_ = lean_ctor_get(v_res_303_, 1);
lean_inc_ref(v_vec_305_);
lean_dec_ref(v_res_303_);
v___x_306_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_292_, v_inst_293_, v_w_294_, v_n_297_, v_aig_304_, v_distance_299_, v___x_300_, v_vec_305_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; 
lean_dec_ref(v_distance_299_);
lean_dec(v_n_297_);
lean_dec_ref(v_inst_293_);
lean_dec_ref(v_inst_292_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_aig_295_);
lean_ctor_set(v___x_307_, 1, v_target_298_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg___boxed(lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_w_310_, lean_object* v_aig_311_, lean_object* v_target_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(v_inst_308_, v_inst_309_, v_w_310_, v_aig_311_, v_target_312_);
lean_dec(v_w_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(lean_object* v_00_u03b1_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_w_317_, lean_object* v_aig_318_, lean_object* v_target_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(v_inst_315_, v_inst_316_, v_w_317_, v_aig_318_, v_target_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___boxed(lean_object* v_00_u03b1_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_w_324_, lean_object* v_aig_325_, lean_object* v_target_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(v_00_u03b1_321_, v_inst_322_, v_inst_323_, v_w_324_, v_aig_325_, v_target_326_);
lean_dec(v_w_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_w_330_, lean_object* v_aig_331_, lean_object* v_target_332_){
_start:
{
lean_object* v_n_333_; lean_object* v_lhs_334_; lean_object* v_rhs_335_; lean_object* v_pow_336_; uint8_t v___x_337_; 
v_n_333_ = lean_ctor_get(v_target_332_, 0);
v_lhs_334_ = lean_ctor_get(v_target_332_, 1);
v_rhs_335_ = lean_ctor_get(v_target_332_, 2);
v_pow_336_ = lean_ctor_get(v_target_332_, 3);
v___x_337_ = lean_nat_dec_lt(v_pow_336_, v_n_333_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_dec_ref(v_inst_329_);
lean_dec_ref(v_inst_328_);
lean_inc_ref(v_lhs_334_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_aig_331_);
lean_ctor_set(v___x_338_, 1, v_lhs_334_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_res_342_; lean_object* v_aig_343_; lean_object* v_vec_344_; lean_object* v___y_346_; lean_object* v_ref_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_339_ = lean_unsigned_to_nat(2u);
v___x_340_ = lean_nat_pow(v___x_339_, v_pow_336_);
lean_inc_ref(v_lhs_334_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_lhs_334_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v_res_342_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_330_, v_aig_331_, v___x_341_);
v_aig_343_ = lean_ctor_get(v_res_342_, 0);
lean_inc_ref(v_aig_343_);
v_vec_344_ = lean_ctor_get(v_res_342_, 1);
lean_inc_ref(v_vec_344_);
lean_dec_ref(v_res_342_);
v_ref_349_ = lean_array_fget_borrowed(v_rhs_335_, v_pow_336_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_shiftr(v_ref_349_, v___x_350_);
v___x_352_ = lean_nat_land(v___x_350_, v_ref_349_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_nat_dec_eq(v___x_352_, v___x_353_);
lean_dec(v___x_352_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_355_, 0, v___x_351_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_337_);
v___y_346_ = v___x_355_;
goto v___jp_345_;
}
else
{
uint8_t v___x_356_; lean_object* v___x_357_; 
v___x_356_ = 0;
v___x_357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_357_, 0, v___x_351_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1, v___x_356_);
v___y_346_ = v___x_357_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_inc_ref(v_lhs_334_);
v___x_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_347_, 0, v___y_346_);
lean_ctor_set(v___x_347_, 1, v_vec_344_);
lean_ctor_set(v___x_347_, 2, v_lhs_334_);
v___x_348_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_328_, v_inst_329_, v_w_330_, v_aig_343_, v___x_347_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg___boxed(lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_w_360_, lean_object* v_aig_361_, lean_object* v_target_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_358_, v_inst_359_, v_w_360_, v_aig_361_, v_target_362_);
lean_dec_ref(v_target_362_);
lean_dec(v_w_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(lean_object* v_00_u03b1_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_w_367_, lean_object* v_aig_368_, lean_object* v_target_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_365_, v_inst_366_, v_w_367_, v_aig_368_, v_target_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___boxed(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_w_374_, lean_object* v_aig_375_, lean_object* v_target_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(v_00_u03b1_371_, v_inst_372_, v_inst_373_, v_w_374_, v_aig_375_, v_target_376_);
lean_dec_ref(v_target_376_);
lean_dec(v_w_374_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_w_380_, lean_object* v_n_381_, lean_object* v_aig_382_, lean_object* v_distance_383_, lean_object* v_curr_384_, lean_object* v_acc_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_sub(v_n_381_, v___x_386_);
v___x_388_ = lean_nat_dec_lt(v_curr_384_, v___x_387_);
lean_dec(v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec(v_curr_384_);
lean_dec_ref(v_distance_383_);
lean_dec(v_n_381_);
lean_dec_ref(v_inst_379_);
lean_dec_ref(v_inst_378_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_aig_382_);
lean_ctor_set(v___x_389_, 1, v_acc_385_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_res_392_; lean_object* v_aig_393_; lean_object* v_vec_394_; 
v___x_390_ = lean_nat_add(v_curr_384_, v___x_386_);
lean_dec(v_curr_384_);
lean_inc(v___x_390_);
lean_inc_ref(v_distance_383_);
lean_inc(v_n_381_);
v___x_391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_391_, 0, v_n_381_);
lean_ctor_set(v___x_391_, 1, v_acc_385_);
lean_ctor_set(v___x_391_, 2, v_distance_383_);
lean_ctor_set(v___x_391_, 3, v___x_390_);
lean_inc_ref(v_inst_379_);
lean_inc_ref(v_inst_378_);
v_res_392_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_378_, v_inst_379_, v_w_380_, v_aig_382_, v___x_391_);
lean_dec_ref(v___x_391_);
v_aig_393_ = lean_ctor_get(v_res_392_, 0);
lean_inc_ref(v_aig_393_);
v_vec_394_ = lean_ctor_get(v_res_392_, 1);
lean_inc_ref(v_vec_394_);
lean_dec_ref(v_res_392_);
v_aig_382_ = v_aig_393_;
v_curr_384_ = v___x_390_;
v_acc_385_ = v_vec_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg___boxed(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_w_398_, lean_object* v_n_399_, lean_object* v_aig_400_, lean_object* v_distance_401_, lean_object* v_curr_402_, lean_object* v_acc_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_396_, v_inst_397_, v_w_398_, v_n_399_, v_aig_400_, v_distance_401_, v_curr_402_, v_acc_403_);
lean_dec(v_w_398_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(lean_object* v_00_u03b1_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_w_408_, lean_object* v_n_409_, lean_object* v_aig_410_, lean_object* v_distance_411_, lean_object* v_curr_412_, lean_object* v_acc_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_406_, v_inst_407_, v_w_408_, v_n_409_, v_aig_410_, v_distance_411_, v_curr_412_, v_acc_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___boxed(lean_object* v_00_u03b1_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_w_418_, lean_object* v_n_419_, lean_object* v_aig_420_, lean_object* v_distance_421_, lean_object* v_curr_422_, lean_object* v_acc_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(v_00_u03b1_415_, v_inst_416_, v_inst_417_, v_w_418_, v_n_419_, v_aig_420_, v_distance_421_, v_curr_422_, v_acc_423_);
lean_dec(v_w_418_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_w_427_, lean_object* v_aig_428_, lean_object* v_target_429_){
_start:
{
lean_object* v_n_430_; lean_object* v_target_431_; lean_object* v_distance_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_n_430_ = lean_ctor_get(v_target_429_, 0);
lean_inc(v_n_430_);
v_target_431_ = lean_ctor_get(v_target_429_, 1);
lean_inc_ref(v_target_431_);
v_distance_432_ = lean_ctor_get(v_target_429_, 2);
lean_inc_ref(v_distance_432_);
lean_dec_ref(v_target_429_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_nat_dec_eq(v_n_430_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v_res_436_; lean_object* v_aig_437_; lean_object* v_vec_438_; lean_object* v___x_439_; 
lean_inc_ref(v_distance_432_);
lean_inc(v_n_430_);
v___x_435_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_435_, 0, v_n_430_);
lean_ctor_set(v___x_435_, 1, v_target_431_);
lean_ctor_set(v___x_435_, 2, v_distance_432_);
lean_ctor_set(v___x_435_, 3, v___x_433_);
lean_inc_ref(v_inst_426_);
lean_inc_ref(v_inst_425_);
v_res_436_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_425_, v_inst_426_, v_w_427_, v_aig_428_, v___x_435_);
lean_dec_ref(v___x_435_);
v_aig_437_ = lean_ctor_get(v_res_436_, 0);
lean_inc_ref(v_aig_437_);
v_vec_438_ = lean_ctor_get(v_res_436_, 1);
lean_inc_ref(v_vec_438_);
lean_dec_ref(v_res_436_);
v___x_439_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_425_, v_inst_426_, v_w_427_, v_n_430_, v_aig_437_, v_distance_432_, v___x_433_, v_vec_438_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; 
lean_dec_ref(v_distance_432_);
lean_dec(v_n_430_);
lean_dec_ref(v_inst_426_);
lean_dec_ref(v_inst_425_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_aig_428_);
lean_ctor_set(v___x_440_, 1, v_target_431_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg___boxed(lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_w_443_, lean_object* v_aig_444_, lean_object* v_target_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(v_inst_441_, v_inst_442_, v_w_443_, v_aig_444_, v_target_445_);
lean_dec(v_w_443_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(lean_object* v_00_u03b1_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_w_450_, lean_object* v_aig_451_, lean_object* v_target_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(v_inst_448_, v_inst_449_, v_w_450_, v_aig_451_, v_target_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___boxed(lean_object* v_00_u03b1_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_w_457_, lean_object* v_aig_458_, lean_object* v_target_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(v_00_u03b1_454_, v_inst_455_, v_inst_456_, v_w_457_, v_aig_458_, v_target_459_);
lean_dec(v_w_457_);
return v_res_460_;
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
