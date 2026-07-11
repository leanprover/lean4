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
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
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
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_lt(v_curr_5_, v_w_1_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec(v_curr_5_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_aig_2_);
lean_ctor_set(v___x_8_, 1, v_s_6_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_nat_add(v_distance_4_, v_curr_5_);
v___x_10_ = lean_nat_dec_lt(v___x_9_, v_w_1_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v_s_14_; 
lean_dec(v___x_9_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_curr_5_, v___x_11_);
lean_dec(v_curr_5_);
v___x_13_ = lean_bool_to_nat(v___x_10_);
v_s_14_ = lean_array_push(v_s_6_, v___x_13_);
v_curr_5_ = v___x_12_;
v_s_6_ = v_s_14_;
goto _start;
}
else
{
lean_object* v_ref_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_s_28_; 
v_ref_16_ = lean_array_fget_borrowed(v_input_3_, v___x_9_);
lean_dec(v___x_9_);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_land(v___x_17_, v_ref_16_);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_nat_dec_eq(v___x_18_, v___x_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_nat_shiftr(v_ref_16_, v___x_17_);
v___x_22_ = lean_bool_not(v___x_20_);
v___x_23_ = lean_nat_add(v_curr_5_, v___x_17_);
lean_dec(v_curr_5_);
v___x_24_ = lean_unsigned_to_nat(2u);
v___x_25_ = lean_nat_mul(v___x_21_, v___x_24_);
lean_dec(v___x_21_);
v___x_26_ = lean_bool_to_nat(v___x_22_);
v___x_27_ = lean_nat_lor(v___x_25_, v___x_26_);
lean_dec(v___x_25_);
v_s_28_ = lean_array_push(v_s_6_, v___x_27_);
v_curr_5_ = v___x_23_;
v_s_6_ = v_s_28_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg___boxed(lean_object* v_w_30_, lean_object* v_aig_31_, lean_object* v_input_32_, lean_object* v_distance_33_, lean_object* v_curr_34_, lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_30_, v_aig_31_, v_input_32_, v_distance_33_, v_curr_34_, v_s_35_);
lean_dec(v_distance_33_);
lean_dec_ref(v_input_32_);
lean_dec(v_w_30_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_w_40_, lean_object* v_aig_41_, lean_object* v_input_42_, lean_object* v_distance_43_, lean_object* v_curr_44_, lean_object* v_hcurr_45_, lean_object* v_s_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_40_, v_aig_41_, v_input_42_, v_distance_43_, v_curr_44_, v_s_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___boxed(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_w_51_, lean_object* v_aig_52_, lean_object* v_input_53_, lean_object* v_distance_54_, lean_object* v_curr_55_, lean_object* v_hcurr_56_, lean_object* v_s_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(v_00_u03b1_48_, v_inst_49_, v_inst_50_, v_w_51_, v_aig_52_, v_input_53_, v_distance_54_, v_curr_55_, v_hcurr_56_, v_s_57_);
lean_dec(v_distance_54_);
lean_dec_ref(v_input_53_);
lean_dec(v_w_51_);
lean_dec_ref(v_inst_50_);
lean_dec_ref(v_inst_49_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(lean_object* v_w_59_, lean_object* v_aig_60_, lean_object* v_target_61_){
_start:
{
lean_object* v_vec_62_; lean_object* v_distance_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_vec_62_ = lean_ctor_get(v_target_61_, 0);
v_distance_63_ = lean_ctor_get(v_target_61_, 1);
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_mk_empty_array_with_capacity(v_w_59_);
v___x_66_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(v_w_59_, v_aig_60_, v_vec_62_, v_distance_63_, v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg___boxed(lean_object* v_w_67_, lean_object* v_aig_68_, lean_object* v_target_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_67_, v_aig_68_, v_target_69_);
lean_dec_ref(v_target_69_);
lean_dec(v_w_67_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_w_74_, lean_object* v_aig_75_, lean_object* v_target_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_74_, v_aig_75_, v_target_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___boxed(lean_object* v_00_u03b1_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_w_81_, lean_object* v_aig_82_, lean_object* v_target_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(v_00_u03b1_78_, v_inst_79_, v_inst_80_, v_w_81_, v_aig_82_, v_target_83_);
lean_dec_ref(v_target_83_);
lean_dec(v_w_81_);
lean_dec_ref(v_inst_80_);
lean_dec_ref(v_inst_79_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(lean_object* v_w_85_, lean_object* v_input_86_, lean_object* v_distance_87_, lean_object* v_curr_88_, lean_object* v_s_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_nat_dec_lt(v_curr_88_, v_w_85_);
if (v___x_90_ == 0)
{
lean_dec(v_curr_88_);
return v_s_89_;
}
else
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_nat_add(v_distance_87_, v_curr_88_);
v___x_92_ = lean_nat_dec_lt(v___x_91_, v_w_85_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_ref_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_s_106_; 
lean_dec(v___x_91_);
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_sub(v_w_85_, v___x_93_);
v_ref_95_ = lean_array_fget_borrowed(v_input_86_, v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_nat_land(v___x_93_, v_ref_95_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_nat_dec_eq(v___x_96_, v___x_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_nat_shiftr(v_ref_95_, v___x_93_);
v___x_100_ = lean_bool_not(v___x_98_);
v___x_101_ = lean_nat_add(v_curr_88_, v___x_93_);
lean_dec(v_curr_88_);
v___x_102_ = lean_unsigned_to_nat(2u);
v___x_103_ = lean_nat_mul(v___x_99_, v___x_102_);
lean_dec(v___x_99_);
v___x_104_ = lean_bool_to_nat(v___x_100_);
v___x_105_ = lean_nat_lor(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
v_s_106_ = lean_array_push(v_s_89_, v___x_105_);
v_curr_88_ = v___x_101_;
v_s_89_ = v_s_106_;
goto _start;
}
else
{
lean_object* v_ref_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_s_120_; 
v_ref_108_ = lean_array_fget_borrowed(v_input_86_, v___x_91_);
lean_dec(v___x_91_);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_land(v___x_109_, v_ref_108_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_nat_dec_eq(v___x_110_, v___x_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_nat_shiftr(v_ref_108_, v___x_109_);
v___x_114_ = lean_bool_not(v___x_112_);
v___x_115_ = lean_nat_add(v_curr_88_, v___x_109_);
lean_dec(v_curr_88_);
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = lean_nat_mul(v___x_113_, v___x_116_);
lean_dec(v___x_113_);
v___x_118_ = lean_bool_to_nat(v___x_114_);
v___x_119_ = lean_nat_lor(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
v_s_120_ = lean_array_push(v_s_89_, v___x_119_);
v_curr_88_ = v___x_115_;
v_s_89_ = v_s_120_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg___boxed(lean_object* v_w_122_, lean_object* v_input_123_, lean_object* v_distance_124_, lean_object* v_curr_125_, lean_object* v_s_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_122_, v_input_123_, v_distance_124_, v_curr_125_, v_s_126_);
lean_dec(v_distance_124_);
lean_dec_ref(v_input_123_);
lean_dec(v_w_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_w_131_, lean_object* v_aig_132_, lean_object* v_input_133_, lean_object* v_distance_134_, lean_object* v_curr_135_, lean_object* v_hcurr_136_, lean_object* v_s_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_131_, v_input_133_, v_distance_134_, v_curr_135_, v_s_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___boxed(lean_object* v_00_u03b1_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_w_142_, lean_object* v_aig_143_, lean_object* v_input_144_, lean_object* v_distance_145_, lean_object* v_curr_146_, lean_object* v_hcurr_147_, lean_object* v_s_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(v_00_u03b1_139_, v_inst_140_, v_inst_141_, v_w_142_, v_aig_143_, v_input_144_, v_distance_145_, v_curr_146_, v_hcurr_147_, v_s_148_);
lean_dec(v_distance_145_);
lean_dec_ref(v_input_144_);
lean_dec_ref(v_aig_143_);
lean_dec(v_w_142_);
lean_dec_ref(v_inst_141_);
lean_dec_ref(v_inst_140_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(lean_object* v_w_150_, lean_object* v_aig_151_, lean_object* v_target_152_){
_start:
{
lean_object* v_vec_153_; lean_object* v_distance_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_164_; 
v_vec_153_ = lean_ctor_get(v_target_152_, 0);
v_distance_154_ = lean_ctor_get(v_target_152_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_target_152_);
if (v_isSharedCheck_164_ == 0)
{
v___x_156_ = v_target_152_;
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_distance_154_);
lean_inc(v_vec_153_);
lean_dec(v_target_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_mk_empty_array_with_capacity(v_w_150_);
v___x_160_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(v_w_150_, v_vec_153_, v_distance_154_, v___x_158_, v___x_159_);
lean_dec(v_distance_154_);
lean_dec_ref(v_vec_153_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_160_);
lean_ctor_set(v___x_156_, 0, v_aig_151_);
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_aig_151_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg___boxed(lean_object* v_w_165_, lean_object* v_aig_166_, lean_object* v_target_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_165_, v_aig_166_, v_target_167_);
lean_dec(v_w_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_w_172_, lean_object* v_aig_173_, lean_object* v_target_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_172_, v_aig_173_, v_target_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___boxed(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_w_179_, lean_object* v_aig_180_, lean_object* v_target_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(v_00_u03b1_176_, v_inst_177_, v_inst_178_, v_w_179_, v_aig_180_, v_target_181_);
lean_dec(v_w_179_);
lean_dec_ref(v_inst_178_);
lean_dec_ref(v_inst_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_w_185_, lean_object* v_aig_186_, lean_object* v_target_187_){
_start:
{
lean_object* v_n_188_; lean_object* v_lhs_189_; lean_object* v_rhs_190_; lean_object* v_pow_191_; uint8_t v___x_192_; 
v_n_188_ = lean_ctor_get(v_target_187_, 0);
v_lhs_189_ = lean_ctor_get(v_target_187_, 1);
v_rhs_190_ = lean_ctor_get(v_target_187_, 2);
v_pow_191_ = lean_ctor_get(v_target_187_, 3);
v___x_192_ = lean_nat_dec_lt(v_pow_191_, v_n_188_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_dec_ref(v_inst_184_);
lean_dec_ref(v_inst_183_);
lean_inc_ref(v_lhs_189_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_aig_186_);
lean_ctor_set(v___x_193_, 1, v_lhs_189_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_res_197_; lean_object* v_aig_198_; lean_object* v_vec_199_; lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_194_ = lean_unsigned_to_nat(2u);
v___x_195_ = lean_nat_pow(v___x_194_, v_pow_191_);
lean_inc_ref_n(v_lhs_189_, 2);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_lhs_189_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v_res_197_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(v_w_185_, v_aig_186_, v___x_196_);
lean_dec_ref_known(v___x_196_, 2);
v_aig_198_ = lean_ctor_get(v_res_197_, 0);
lean_inc_ref(v_aig_198_);
v_vec_199_ = lean_ctor_get(v_res_197_, 1);
lean_inc_ref(v_vec_199_);
lean_dec_ref(v_res_197_);
v_ref_200_ = lean_array_fget_borrowed(v_rhs_190_, v_pow_191_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_shiftr(v_ref_200_, v___x_201_);
v___x_203_ = lean_nat_land(v___x_201_, v_ref_200_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_bool_not(v___x_205_);
v___x_207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_207_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*1, v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_vec_199_);
lean_ctor_set(v___x_208_, 2, v_lhs_189_);
v___x_209_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_183_, v_inst_184_, v_w_185_, v_aig_198_, v___x_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg___boxed(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_w_212_, lean_object* v_aig_213_, lean_object* v_target_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_210_, v_inst_211_, v_w_212_, v_aig_213_, v_target_214_);
lean_dec_ref(v_target_214_);
lean_dec(v_w_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_w_219_, lean_object* v_aig_220_, lean_object* v_target_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_217_, v_inst_218_, v_w_219_, v_aig_220_, v_target_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___boxed(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_w_226_, lean_object* v_aig_227_, lean_object* v_target_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(v_00_u03b1_223_, v_inst_224_, v_inst_225_, v_w_226_, v_aig_227_, v_target_228_);
lean_dec_ref(v_target_228_);
lean_dec(v_w_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_w_232_, lean_object* v_n_233_, lean_object* v_aig_234_, lean_object* v_distance_235_, lean_object* v_curr_236_, lean_object* v_acc_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_sub(v_n_233_, v___x_238_);
v___x_240_ = lean_nat_dec_lt(v_curr_236_, v___x_239_);
lean_dec(v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_dec(v_curr_236_);
lean_dec_ref(v_distance_235_);
lean_dec(v_n_233_);
lean_dec_ref(v_inst_231_);
lean_dec_ref(v_inst_230_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_aig_234_);
lean_ctor_set(v___x_241_, 1, v_acc_237_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_res_244_; lean_object* v_aig_245_; lean_object* v_vec_246_; 
v___x_242_ = lean_nat_add(v_curr_236_, v___x_238_);
lean_dec(v_curr_236_);
lean_inc(v___x_242_);
lean_inc_ref(v_distance_235_);
lean_inc(v_n_233_);
v___x_243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_243_, 0, v_n_233_);
lean_ctor_set(v___x_243_, 1, v_acc_237_);
lean_ctor_set(v___x_243_, 2, v_distance_235_);
lean_ctor_set(v___x_243_, 3, v___x_242_);
lean_inc_ref(v_inst_231_);
lean_inc_ref(v_inst_230_);
v_res_244_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_230_, v_inst_231_, v_w_232_, v_aig_234_, v___x_243_);
lean_dec_ref_known(v___x_243_, 4);
v_aig_245_ = lean_ctor_get(v_res_244_, 0);
lean_inc_ref(v_aig_245_);
v_vec_246_ = lean_ctor_get(v_res_244_, 1);
lean_inc_ref(v_vec_246_);
lean_dec_ref(v_res_244_);
v_aig_234_ = v_aig_245_;
v_curr_236_ = v___x_242_;
v_acc_237_ = v_vec_246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg___boxed(lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_w_250_, lean_object* v_n_251_, lean_object* v_aig_252_, lean_object* v_distance_253_, lean_object* v_curr_254_, lean_object* v_acc_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_248_, v_inst_249_, v_w_250_, v_n_251_, v_aig_252_, v_distance_253_, v_curr_254_, v_acc_255_);
lean_dec(v_w_250_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(lean_object* v_00_u03b1_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_w_260_, lean_object* v_n_261_, lean_object* v_aig_262_, lean_object* v_distance_263_, lean_object* v_curr_264_, lean_object* v_acc_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_258_, v_inst_259_, v_w_260_, v_n_261_, v_aig_262_, v_distance_263_, v_curr_264_, v_acc_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___boxed(lean_object* v_00_u03b1_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_w_270_, lean_object* v_n_271_, lean_object* v_aig_272_, lean_object* v_distance_273_, lean_object* v_curr_274_, lean_object* v_acc_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(v_00_u03b1_267_, v_inst_268_, v_inst_269_, v_w_270_, v_n_271_, v_aig_272_, v_distance_273_, v_curr_274_, v_acc_275_);
lean_dec(v_w_270_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_w_279_, lean_object* v_aig_280_, lean_object* v_target_281_){
_start:
{
lean_object* v_n_282_; lean_object* v_target_283_; lean_object* v_distance_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_n_282_ = lean_ctor_get(v_target_281_, 0);
lean_inc(v_n_282_);
v_target_283_ = lean_ctor_get(v_target_281_, 1);
lean_inc_ref(v_target_283_);
v_distance_284_ = lean_ctor_get(v_target_281_, 2);
lean_inc_ref(v_distance_284_);
lean_dec_ref(v_target_281_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_nat_dec_eq(v_n_282_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v_res_288_; lean_object* v_aig_289_; lean_object* v_vec_290_; lean_object* v___x_291_; 
lean_inc_ref(v_distance_284_);
lean_inc(v_n_282_);
v___x_287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_287_, 0, v_n_282_);
lean_ctor_set(v___x_287_, 1, v_target_283_);
lean_ctor_set(v___x_287_, 2, v_distance_284_);
lean_ctor_set(v___x_287_, 3, v___x_285_);
lean_inc_ref(v_inst_278_);
lean_inc_ref(v_inst_277_);
v_res_288_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(v_inst_277_, v_inst_278_, v_w_279_, v_aig_280_, v___x_287_);
lean_dec_ref_known(v___x_287_, 4);
v_aig_289_ = lean_ctor_get(v_res_288_, 0);
lean_inc_ref(v_aig_289_);
v_vec_290_ = lean_ctor_get(v_res_288_, 1);
lean_inc_ref(v_vec_290_);
lean_dec_ref(v_res_288_);
v___x_291_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(v_inst_277_, v_inst_278_, v_w_279_, v_n_282_, v_aig_289_, v_distance_284_, v___x_285_, v_vec_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
lean_dec_ref(v_distance_284_);
lean_dec(v_n_282_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_inst_277_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_aig_280_);
lean_ctor_set(v___x_292_, 1, v_target_283_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg___boxed(lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_w_295_, lean_object* v_aig_296_, lean_object* v_target_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(v_inst_293_, v_inst_294_, v_w_295_, v_aig_296_, v_target_297_);
lean_dec(v_w_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(lean_object* v_00_u03b1_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_w_302_, lean_object* v_aig_303_, lean_object* v_target_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(v_inst_300_, v_inst_301_, v_w_302_, v_aig_303_, v_target_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___boxed(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_w_309_, lean_object* v_aig_310_, lean_object* v_target_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(v_00_u03b1_306_, v_inst_307_, v_inst_308_, v_w_309_, v_aig_310_, v_target_311_);
lean_dec(v_w_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_w_315_, lean_object* v_aig_316_, lean_object* v_target_317_){
_start:
{
lean_object* v_n_318_; lean_object* v_lhs_319_; lean_object* v_rhs_320_; lean_object* v_pow_321_; uint8_t v___x_322_; 
v_n_318_ = lean_ctor_get(v_target_317_, 0);
v_lhs_319_ = lean_ctor_get(v_target_317_, 1);
v_rhs_320_ = lean_ctor_get(v_target_317_, 2);
v_pow_321_ = lean_ctor_get(v_target_317_, 3);
v___x_322_ = lean_nat_dec_lt(v_pow_321_, v_n_318_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_313_);
lean_inc_ref(v_lhs_319_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_aig_316_);
lean_ctor_set(v___x_323_, 1, v_lhs_319_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_res_327_; lean_object* v_aig_328_; lean_object* v_vec_329_; lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_324_ = lean_unsigned_to_nat(2u);
v___x_325_ = lean_nat_pow(v___x_324_, v_pow_321_);
lean_inc_ref_n(v_lhs_319_, 2);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_lhs_319_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v_res_327_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(v_w_315_, v_aig_316_, v___x_326_);
v_aig_328_ = lean_ctor_get(v_res_327_, 0);
lean_inc_ref(v_aig_328_);
v_vec_329_ = lean_ctor_get(v_res_327_, 1);
lean_inc_ref(v_vec_329_);
lean_dec_ref(v_res_327_);
v_ref_330_ = lean_array_fget_borrowed(v_rhs_320_, v_pow_321_);
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_shiftr(v_ref_330_, v___x_331_);
v___x_333_ = lean_nat_land(v___x_331_, v_ref_330_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_nat_dec_eq(v___x_333_, v___x_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_bool_not(v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_337_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*1, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_vec_329_);
lean_ctor_set(v___x_338_, 2, v_lhs_319_);
v___x_339_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_313_, v_inst_314_, v_w_315_, v_aig_328_, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg___boxed(lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_w_342_, lean_object* v_aig_343_, lean_object* v_target_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_340_, v_inst_341_, v_w_342_, v_aig_343_, v_target_344_);
lean_dec_ref(v_target_344_);
lean_dec(v_w_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_w_349_, lean_object* v_aig_350_, lean_object* v_target_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_347_, v_inst_348_, v_w_349_, v_aig_350_, v_target_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___boxed(lean_object* v_00_u03b1_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_w_356_, lean_object* v_aig_357_, lean_object* v_target_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(v_00_u03b1_353_, v_inst_354_, v_inst_355_, v_w_356_, v_aig_357_, v_target_358_);
lean_dec_ref(v_target_358_);
lean_dec(v_w_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_w_362_, lean_object* v_n_363_, lean_object* v_aig_364_, lean_object* v_distance_365_, lean_object* v_curr_366_, lean_object* v_acc_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_sub(v_n_363_, v___x_368_);
v___x_370_ = lean_nat_dec_lt(v_curr_366_, v___x_369_);
lean_dec(v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_curr_366_);
lean_dec_ref(v_distance_365_);
lean_dec(v_n_363_);
lean_dec_ref(v_inst_361_);
lean_dec_ref(v_inst_360_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_aig_364_);
lean_ctor_set(v___x_371_, 1, v_acc_367_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_res_374_; lean_object* v_aig_375_; lean_object* v_vec_376_; 
v___x_372_ = lean_nat_add(v_curr_366_, v___x_368_);
lean_dec(v_curr_366_);
lean_inc(v___x_372_);
lean_inc_ref(v_distance_365_);
lean_inc(v_n_363_);
v___x_373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_373_, 0, v_n_363_);
lean_ctor_set(v___x_373_, 1, v_acc_367_);
lean_ctor_set(v___x_373_, 2, v_distance_365_);
lean_ctor_set(v___x_373_, 3, v___x_372_);
lean_inc_ref(v_inst_361_);
lean_inc_ref(v_inst_360_);
v_res_374_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_360_, v_inst_361_, v_w_362_, v_aig_364_, v___x_373_);
lean_dec_ref_known(v___x_373_, 4);
v_aig_375_ = lean_ctor_get(v_res_374_, 0);
lean_inc_ref(v_aig_375_);
v_vec_376_ = lean_ctor_get(v_res_374_, 1);
lean_inc_ref(v_vec_376_);
lean_dec_ref(v_res_374_);
v_aig_364_ = v_aig_375_;
v_curr_366_ = v___x_372_;
v_acc_367_ = v_vec_376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg___boxed(lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_w_380_, lean_object* v_n_381_, lean_object* v_aig_382_, lean_object* v_distance_383_, lean_object* v_curr_384_, lean_object* v_acc_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_378_, v_inst_379_, v_w_380_, v_n_381_, v_aig_382_, v_distance_383_, v_curr_384_, v_acc_385_);
lean_dec(v_w_380_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(lean_object* v_00_u03b1_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_w_390_, lean_object* v_n_391_, lean_object* v_aig_392_, lean_object* v_distance_393_, lean_object* v_curr_394_, lean_object* v_acc_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_388_, v_inst_389_, v_w_390_, v_n_391_, v_aig_392_, v_distance_393_, v_curr_394_, v_acc_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___boxed(lean_object* v_00_u03b1_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_w_400_, lean_object* v_n_401_, lean_object* v_aig_402_, lean_object* v_distance_403_, lean_object* v_curr_404_, lean_object* v_acc_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(v_00_u03b1_397_, v_inst_398_, v_inst_399_, v_w_400_, v_n_401_, v_aig_402_, v_distance_403_, v_curr_404_, v_acc_405_);
lean_dec(v_w_400_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_w_409_, lean_object* v_aig_410_, lean_object* v_target_411_){
_start:
{
lean_object* v_n_412_; lean_object* v_target_413_; lean_object* v_distance_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_n_412_ = lean_ctor_get(v_target_411_, 0);
lean_inc(v_n_412_);
v_target_413_ = lean_ctor_get(v_target_411_, 1);
lean_inc_ref(v_target_413_);
v_distance_414_ = lean_ctor_get(v_target_411_, 2);
lean_inc_ref(v_distance_414_);
lean_dec_ref(v_target_411_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_nat_dec_eq(v_n_412_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v_res_418_; lean_object* v_aig_419_; lean_object* v_vec_420_; lean_object* v___x_421_; 
lean_inc_ref(v_distance_414_);
lean_inc(v_n_412_);
v___x_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_417_, 0, v_n_412_);
lean_ctor_set(v___x_417_, 1, v_target_413_);
lean_ctor_set(v___x_417_, 2, v_distance_414_);
lean_ctor_set(v___x_417_, 3, v___x_415_);
lean_inc_ref(v_inst_408_);
lean_inc_ref(v_inst_407_);
v_res_418_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_407_, v_inst_408_, v_w_409_, v_aig_410_, v___x_417_);
lean_dec_ref_known(v___x_417_, 4);
v_aig_419_ = lean_ctor_get(v_res_418_, 0);
lean_inc_ref(v_aig_419_);
v_vec_420_ = lean_ctor_get(v_res_418_, 1);
lean_inc_ref(v_vec_420_);
lean_dec_ref(v_res_418_);
v___x_421_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(v_inst_407_, v_inst_408_, v_w_409_, v_n_412_, v_aig_419_, v_distance_414_, v___x_415_, v_vec_420_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; 
lean_dec_ref(v_distance_414_);
lean_dec(v_n_412_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_407_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_aig_410_);
lean_ctor_set(v___x_422_, 1, v_target_413_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg___boxed(lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_w_425_, lean_object* v_aig_426_, lean_object* v_target_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(v_inst_423_, v_inst_424_, v_w_425_, v_aig_426_, v_target_427_);
lean_dec(v_w_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(lean_object* v_00_u03b1_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_w_432_, lean_object* v_aig_433_, lean_object* v_target_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(v_inst_430_, v_inst_431_, v_w_432_, v_aig_433_, v_target_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___boxed(lean_object* v_00_u03b1_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_w_439_, lean_object* v_aig_440_, lean_object* v_target_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(v_00_u03b1_436_, v_inst_437_, v_inst_438_, v_w_439_, v_aig_440_, v_target_441_);
lean_dec(v_w_439_);
return v_res_442_;
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
