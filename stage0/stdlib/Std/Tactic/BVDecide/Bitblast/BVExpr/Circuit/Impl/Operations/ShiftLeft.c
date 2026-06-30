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
static lean_once_cell_t l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0;
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
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0(void){
_start:
{
uint8_t v___x_1_; lean_object* v___x_2_; 
v___x_1_ = 0;
v___x_2_ = l_Bool_toNat(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_input_5_, lean_object* v_distance_6_, lean_object* v_curr_7_, lean_object* v_s_8_){
_start:
{
lean_object* v_gate_10_; uint8_t v_invert_11_; uint8_t v___x_20_; 
v___x_20_ = lean_nat_dec_lt(v_curr_7_, v_w_3_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec(v_curr_7_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_aig_4_);
lean_ctor_set(v___x_21_, 1, v_s_8_);
return v___x_21_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = lean_nat_dec_lt(v_curr_7_, v_distance_6_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v_ref_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_23_ = lean_nat_sub(v_curr_7_, v_distance_6_);
v_ref_24_ = lean_array_fget_borrowed(v_input_5_, v___x_23_);
lean_dec(v___x_23_);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_shiftr(v_ref_24_, v___x_25_);
v___x_27_ = lean_nat_land(v___x_25_, v_ref_24_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_dec_eq(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
if (v___x_29_ == 0)
{
v_gate_10_ = v___x_26_;
v_invert_11_ = v___x_20_;
goto v___jp_9_;
}
else
{
v_gate_10_ = v___x_26_;
v_invert_11_ = v___x_22_;
goto v___jp_9_;
}
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v_s_33_; 
v___x_30_ = lean_unsigned_to_nat(1u);
v___x_31_ = lean_nat_add(v_curr_7_, v___x_30_);
lean_dec(v_curr_7_);
v___x_32_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0);
v_s_33_ = lean_array_push(v_s_8_, v___x_32_);
v_curr_7_ = v___x_31_;
v_s_8_ = v_s_33_;
goto _start;
}
}
v___jp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_s_18_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_add(v_curr_7_, v___x_12_);
lean_dec(v_curr_7_);
v___x_14_ = lean_unsigned_to_nat(2u);
v___x_15_ = lean_nat_mul(v_gate_10_, v___x_14_);
lean_dec(v_gate_10_);
v___x_16_ = l_Bool_toNat(v_invert_11_);
v___x_17_ = lean_nat_lor(v___x_15_, v___x_16_);
lean_dec(v___x_16_);
lean_dec(v___x_15_);
v_s_18_ = lean_array_push(v_s_8_, v___x_17_);
v_curr_7_ = v___x_13_;
v_s_8_ = v_s_18_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___boxed(lean_object* v_w_35_, lean_object* v_aig_36_, lean_object* v_input_37_, lean_object* v_distance_38_, lean_object* v_curr_39_, lean_object* v_s_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_35_, v_aig_36_, v_input_37_, v_distance_38_, v_curr_39_, v_s_40_);
lean_dec(v_distance_38_);
lean_dec_ref(v_input_37_);
lean_dec(v_w_35_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_w_45_, lean_object* v_aig_46_, lean_object* v_input_47_, lean_object* v_distance_48_, lean_object* v_curr_49_, lean_object* v_hcurr_50_, lean_object* v_s_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_45_, v_aig_46_, v_input_47_, v_distance_48_, v_curr_49_, v_s_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___boxed(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_w_56_, lean_object* v_aig_57_, lean_object* v_input_58_, lean_object* v_distance_59_, lean_object* v_curr_60_, lean_object* v_hcurr_61_, lean_object* v_s_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(v_00_u03b1_53_, v_inst_54_, v_inst_55_, v_w_56_, v_aig_57_, v_input_58_, v_distance_59_, v_curr_60_, v_hcurr_61_, v_s_62_);
lean_dec(v_distance_59_);
lean_dec_ref(v_input_58_);
lean_dec(v_w_56_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_inst_54_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object* v_w_64_, lean_object* v_aig_65_, lean_object* v_target_66_){
_start:
{
lean_object* v_vec_67_; lean_object* v_distance_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_vec_67_ = lean_ctor_get(v_target_66_, 0);
v_distance_68_ = lean_ctor_get(v_target_66_, 1);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_mk_empty_array_with_capacity(v_w_64_);
v___x_71_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_64_, v_aig_65_, v_vec_67_, v_distance_68_, v___x_69_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg___boxed(lean_object* v_w_72_, lean_object* v_aig_73_, lean_object* v_target_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_72_, v_aig_73_, v_target_74_);
lean_dec_ref(v_target_74_);
lean_dec(v_w_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_w_79_, lean_object* v_aig_80_, lean_object* v_target_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_79_, v_aig_80_, v_target_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___boxed(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_w_86_, lean_object* v_aig_87_, lean_object* v_target_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(v_00_u03b1_83_, v_inst_84_, v_inst_85_, v_w_86_, v_aig_87_, v_target_88_);
lean_dec_ref(v_target_88_);
lean_dec(v_w_86_);
lean_dec_ref(v_inst_85_);
lean_dec_ref(v_inst_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_w_92_, lean_object* v_aig_93_, lean_object* v_target_94_){
_start:
{
lean_object* v_n_95_; lean_object* v_lhs_96_; lean_object* v_rhs_97_; lean_object* v_pow_98_; uint8_t v___x_99_; 
v_n_95_ = lean_ctor_get(v_target_94_, 0);
v_lhs_96_ = lean_ctor_get(v_target_94_, 1);
v_rhs_97_ = lean_ctor_get(v_target_94_, 2);
v_pow_98_ = lean_ctor_get(v_target_94_, 3);
v___x_99_ = lean_nat_dec_lt(v_pow_98_, v_n_95_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v_inst_91_);
lean_dec_ref(v_inst_90_);
lean_inc_ref(v_lhs_96_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_aig_93_);
lean_ctor_set(v___x_100_, 1, v_lhs_96_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_res_104_; lean_object* v_aig_105_; lean_object* v_vec_106_; lean_object* v___y_108_; lean_object* v_ref_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_pow(v___x_101_, v_pow_98_);
lean_inc_ref(v_lhs_96_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_lhs_96_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v_res_104_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_92_, v_aig_93_, v___x_103_);
lean_dec_ref_known(v___x_103_, 2);
v_aig_105_ = lean_ctor_get(v_res_104_, 0);
lean_inc_ref(v_aig_105_);
v_vec_106_ = lean_ctor_get(v_res_104_, 1);
lean_inc_ref(v_vec_106_);
lean_dec_ref(v_res_104_);
v_ref_111_ = lean_array_fget_borrowed(v_rhs_97_, v_pow_98_);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_shiftr(v_ref_111_, v___x_112_);
v___x_114_ = lean_nat_land(v___x_112_, v_ref_111_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_nat_dec_eq(v___x_114_, v___x_115_);
lean_dec(v___x_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_99_);
v___y_108_ = v___x_117_;
goto v___jp_107_;
}
else
{
uint8_t v___x_118_; lean_object* v___x_119_; 
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___y_108_ = v___x_119_;
goto v___jp_107_;
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_inc_ref(v_lhs_96_);
v___x_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_109_, 0, v___y_108_);
lean_ctor_set(v___x_109_, 1, v_vec_106_);
lean_ctor_set(v___x_109_, 2, v_lhs_96_);
v___x_110_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_90_, v_inst_91_, v_w_92_, v_aig_105_, v___x_109_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg___boxed(lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_w_122_, lean_object* v_aig_123_, lean_object* v_target_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_120_, v_inst_121_, v_w_122_, v_aig_123_, v_target_124_);
lean_dec_ref(v_target_124_);
lean_dec(v_w_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(lean_object* v_00_u03b1_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_w_129_, lean_object* v_aig_130_, lean_object* v_target_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_127_, v_inst_128_, v_w_129_, v_aig_130_, v_target_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___boxed(lean_object* v_00_u03b1_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_w_136_, lean_object* v_aig_137_, lean_object* v_target_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(v_00_u03b1_133_, v_inst_134_, v_inst_135_, v_w_136_, v_aig_137_, v_target_138_);
lean_dec_ref(v_target_138_);
lean_dec(v_w_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_w_142_, lean_object* v_n_143_, lean_object* v_aig_144_, lean_object* v_distance_145_, lean_object* v_curr_146_, lean_object* v_acc_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_sub(v_n_143_, v___x_148_);
v___x_150_ = lean_nat_dec_lt(v_curr_146_, v___x_149_);
lean_dec(v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec(v_curr_146_);
lean_dec_ref(v_distance_145_);
lean_dec(v_n_143_);
lean_dec_ref(v_inst_141_);
lean_dec_ref(v_inst_140_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_aig_144_);
lean_ctor_set(v___x_151_, 1, v_acc_147_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_res_154_; lean_object* v_aig_155_; lean_object* v_vec_156_; 
v___x_152_ = lean_nat_add(v_curr_146_, v___x_148_);
lean_dec(v_curr_146_);
lean_inc(v___x_152_);
lean_inc_ref(v_distance_145_);
lean_inc(v_n_143_);
v___x_153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_153_, 0, v_n_143_);
lean_ctor_set(v___x_153_, 1, v_acc_147_);
lean_ctor_set(v___x_153_, 2, v_distance_145_);
lean_ctor_set(v___x_153_, 3, v___x_152_);
lean_inc_ref(v_inst_141_);
lean_inc_ref(v_inst_140_);
v_res_154_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_140_, v_inst_141_, v_w_142_, v_aig_144_, v___x_153_);
lean_dec_ref_known(v___x_153_, 4);
v_aig_155_ = lean_ctor_get(v_res_154_, 0);
lean_inc_ref(v_aig_155_);
v_vec_156_ = lean_ctor_get(v_res_154_, 1);
lean_inc_ref(v_vec_156_);
lean_dec_ref(v_res_154_);
v_aig_144_ = v_aig_155_;
v_curr_146_ = v___x_152_;
v_acc_147_ = v_vec_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg___boxed(lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_w_160_, lean_object* v_n_161_, lean_object* v_aig_162_, lean_object* v_distance_163_, lean_object* v_curr_164_, lean_object* v_acc_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_158_, v_inst_159_, v_w_160_, v_n_161_, v_aig_162_, v_distance_163_, v_curr_164_, v_acc_165_);
lean_dec(v_w_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(lean_object* v_00_u03b1_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_w_170_, lean_object* v_n_171_, lean_object* v_aig_172_, lean_object* v_distance_173_, lean_object* v_curr_174_, lean_object* v_acc_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_168_, v_inst_169_, v_w_170_, v_n_171_, v_aig_172_, v_distance_173_, v_curr_174_, v_acc_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___boxed(lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_w_180_, lean_object* v_n_181_, lean_object* v_aig_182_, lean_object* v_distance_183_, lean_object* v_curr_184_, lean_object* v_acc_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(v_00_u03b1_177_, v_inst_178_, v_inst_179_, v_w_180_, v_n_181_, v_aig_182_, v_distance_183_, v_curr_184_, v_acc_185_);
lean_dec(v_w_180_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_w_189_, lean_object* v_aig_190_, lean_object* v_target_191_){
_start:
{
lean_object* v_n_192_; lean_object* v_target_193_; lean_object* v_distance_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_n_192_ = lean_ctor_get(v_target_191_, 0);
lean_inc(v_n_192_);
v_target_193_ = lean_ctor_get(v_target_191_, 1);
lean_inc_ref(v_target_193_);
v_distance_194_ = lean_ctor_get(v_target_191_, 2);
lean_inc_ref(v_distance_194_);
lean_dec_ref(v_target_191_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_dec_eq(v_n_192_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v_res_198_; lean_object* v_aig_199_; lean_object* v_vec_200_; lean_object* v___x_201_; 
lean_inc_ref(v_distance_194_);
lean_inc(v_n_192_);
v___x_197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_197_, 0, v_n_192_);
lean_ctor_set(v___x_197_, 1, v_target_193_);
lean_ctor_set(v___x_197_, 2, v_distance_194_);
lean_ctor_set(v___x_197_, 3, v___x_195_);
lean_inc_ref(v_inst_188_);
lean_inc_ref(v_inst_187_);
v_res_198_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_187_, v_inst_188_, v_w_189_, v_aig_190_, v___x_197_);
lean_dec_ref_known(v___x_197_, 4);
v_aig_199_ = lean_ctor_get(v_res_198_, 0);
lean_inc_ref(v_aig_199_);
v_vec_200_ = lean_ctor_get(v_res_198_, 1);
lean_inc_ref(v_vec_200_);
lean_dec_ref(v_res_198_);
v___x_201_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_187_, v_inst_188_, v_w_189_, v_n_192_, v_aig_199_, v_distance_194_, v___x_195_, v_vec_200_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
lean_dec_ref(v_distance_194_);
lean_dec(v_n_192_);
lean_dec_ref(v_inst_188_);
lean_dec_ref(v_inst_187_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_aig_190_);
lean_ctor_set(v___x_202_, 1, v_target_193_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg___boxed(lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_w_205_, lean_object* v_aig_206_, lean_object* v_target_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_203_, v_inst_204_, v_w_205_, v_aig_206_, v_target_207_);
lean_dec(v_w_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_w_212_, lean_object* v_aig_213_, lean_object* v_target_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_210_, v_inst_211_, v_w_212_, v_aig_213_, v_target_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___boxed(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_w_219_, lean_object* v_aig_220_, lean_object* v_target_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(v_00_u03b1_216_, v_inst_217_, v_inst_218_, v_w_219_, v_aig_220_, v_target_221_);
lean_dec(v_w_219_);
return v_res_222_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin) {
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
