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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
v___x_2_ = lean_bool_to_nat(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_input_5_, lean_object* v_distance_6_, lean_object* v_curr_7_, lean_object* v_s_8_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_lt(v_curr_7_, v_w_3_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_curr_7_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_aig_4_);
lean_ctor_set(v___x_10_, 1, v_s_8_);
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_lt(v_curr_7_, v_distance_6_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v_ref_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_s_25_; 
v___x_12_ = lean_nat_sub(v_curr_7_, v_distance_6_);
v_ref_13_ = lean_array_fget_borrowed(v_input_5_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_land(v___x_14_, v_ref_13_);
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_nat_dec_eq(v___x_15_, v___x_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_nat_shiftr(v_ref_13_, v___x_14_);
v___x_19_ = lean_bool_not(v___x_17_);
v___x_20_ = lean_nat_add(v_curr_7_, v___x_14_);
lean_dec(v_curr_7_);
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = lean_nat_mul(v___x_18_, v___x_21_);
lean_dec(v___x_18_);
v___x_23_ = lean_bool_to_nat(v___x_19_);
v___x_24_ = lean_nat_lor(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
v_s_25_ = lean_array_push(v_s_8_, v___x_24_);
v_curr_7_ = v___x_20_;
v_s_8_ = v_s_25_;
goto _start;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_s_30_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_curr_7_, v___x_27_);
lean_dec(v_curr_7_);
v___x_29_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0);
v_s_30_ = lean_array_push(v_s_8_, v___x_29_);
v_curr_7_ = v___x_28_;
v_s_8_ = v_s_30_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___boxed(lean_object* v_w_32_, lean_object* v_aig_33_, lean_object* v_input_34_, lean_object* v_distance_35_, lean_object* v_curr_36_, lean_object* v_s_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_32_, v_aig_33_, v_input_34_, v_distance_35_, v_curr_36_, v_s_37_);
lean_dec(v_distance_35_);
lean_dec_ref(v_input_34_);
lean_dec(v_w_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_w_42_, lean_object* v_aig_43_, lean_object* v_input_44_, lean_object* v_distance_45_, lean_object* v_curr_46_, lean_object* v_hcurr_47_, lean_object* v_s_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_42_, v_aig_43_, v_input_44_, v_distance_45_, v_curr_46_, v_s_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___boxed(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_w_53_, lean_object* v_aig_54_, lean_object* v_input_55_, lean_object* v_distance_56_, lean_object* v_curr_57_, lean_object* v_hcurr_58_, lean_object* v_s_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(v_00_u03b1_50_, v_inst_51_, v_inst_52_, v_w_53_, v_aig_54_, v_input_55_, v_distance_56_, v_curr_57_, v_hcurr_58_, v_s_59_);
lean_dec(v_distance_56_);
lean_dec_ref(v_input_55_);
lean_dec(v_w_53_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object* v_w_61_, lean_object* v_aig_62_, lean_object* v_target_63_){
_start:
{
lean_object* v_vec_64_; lean_object* v_distance_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_vec_64_ = lean_ctor_get(v_target_63_, 0);
v_distance_65_ = lean_ctor_get(v_target_63_, 1);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_mk_empty_array_with_capacity(v_w_61_);
v___x_68_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_61_, v_aig_62_, v_vec_64_, v_distance_65_, v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg___boxed(lean_object* v_w_69_, lean_object* v_aig_70_, lean_object* v_target_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_69_, v_aig_70_, v_target_71_);
lean_dec_ref(v_target_71_);
lean_dec(v_w_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(lean_object* v_00_u03b1_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_w_76_, lean_object* v_aig_77_, lean_object* v_target_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_76_, v_aig_77_, v_target_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___boxed(lean_object* v_00_u03b1_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_w_83_, lean_object* v_aig_84_, lean_object* v_target_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(v_00_u03b1_80_, v_inst_81_, v_inst_82_, v_w_83_, v_aig_84_, v_target_85_);
lean_dec_ref(v_target_85_);
lean_dec(v_w_83_);
lean_dec_ref(v_inst_82_);
lean_dec_ref(v_inst_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_w_89_, lean_object* v_aig_90_, lean_object* v_target_91_){
_start:
{
lean_object* v_n_92_; lean_object* v_lhs_93_; lean_object* v_rhs_94_; lean_object* v_pow_95_; uint8_t v___x_96_; 
v_n_92_ = lean_ctor_get(v_target_91_, 0);
v_lhs_93_ = lean_ctor_get(v_target_91_, 1);
v_rhs_94_ = lean_ctor_get(v_target_91_, 2);
v_pow_95_ = lean_ctor_get(v_target_91_, 3);
v___x_96_ = lean_nat_dec_lt(v_pow_95_, v_n_92_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v_inst_88_);
lean_dec_ref(v_inst_87_);
lean_inc_ref(v_lhs_93_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_aig_90_);
lean_ctor_set(v___x_97_, 1, v_lhs_93_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_res_101_; lean_object* v_aig_102_; lean_object* v_vec_103_; lean_object* v_ref_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_nat_pow(v___x_98_, v_pow_95_);
lean_inc_ref_n(v_lhs_93_, 2);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_lhs_93_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v_res_101_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_89_, v_aig_90_, v___x_100_);
lean_dec_ref_known(v___x_100_, 2);
v_aig_102_ = lean_ctor_get(v_res_101_, 0);
lean_inc_ref(v_aig_102_);
v_vec_103_ = lean_ctor_get(v_res_101_, 1);
lean_inc_ref(v_vec_103_);
lean_dec_ref(v_res_101_);
v_ref_104_ = lean_array_fget_borrowed(v_rhs_94_, v_pow_95_);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_shiftr(v_ref_104_, v___x_105_);
v___x_107_ = lean_nat_land(v___x_105_, v_ref_104_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_nat_dec_eq(v___x_107_, v___x_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_bool_not(v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v_vec_103_);
lean_ctor_set(v___x_112_, 2, v_lhs_93_);
v___x_113_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_87_, v_inst_88_, v_w_89_, v_aig_102_, v___x_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg___boxed(lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_w_116_, lean_object* v_aig_117_, lean_object* v_target_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_114_, v_inst_115_, v_w_116_, v_aig_117_, v_target_118_);
lean_dec_ref(v_target_118_);
lean_dec(v_w_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(lean_object* v_00_u03b1_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_w_123_, lean_object* v_aig_124_, lean_object* v_target_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_121_, v_inst_122_, v_w_123_, v_aig_124_, v_target_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___boxed(lean_object* v_00_u03b1_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_w_130_, lean_object* v_aig_131_, lean_object* v_target_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(v_00_u03b1_127_, v_inst_128_, v_inst_129_, v_w_130_, v_aig_131_, v_target_132_);
lean_dec_ref(v_target_132_);
lean_dec(v_w_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_w_136_, lean_object* v_n_137_, lean_object* v_aig_138_, lean_object* v_distance_139_, lean_object* v_curr_140_, lean_object* v_acc_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_sub(v_n_137_, v___x_142_);
v___x_144_ = lean_nat_dec_lt(v_curr_140_, v___x_143_);
lean_dec(v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_dec(v_curr_140_);
lean_dec_ref(v_distance_139_);
lean_dec(v_n_137_);
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_134_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_aig_138_);
lean_ctor_set(v___x_145_, 1, v_acc_141_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_res_148_; lean_object* v_aig_149_; lean_object* v_vec_150_; 
v___x_146_ = lean_nat_add(v_curr_140_, v___x_142_);
lean_dec(v_curr_140_);
lean_inc(v___x_146_);
lean_inc_ref(v_distance_139_);
lean_inc(v_n_137_);
v___x_147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_147_, 0, v_n_137_);
lean_ctor_set(v___x_147_, 1, v_acc_141_);
lean_ctor_set(v___x_147_, 2, v_distance_139_);
lean_ctor_set(v___x_147_, 3, v___x_146_);
lean_inc_ref(v_inst_135_);
lean_inc_ref(v_inst_134_);
v_res_148_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_134_, v_inst_135_, v_w_136_, v_aig_138_, v___x_147_);
lean_dec_ref_known(v___x_147_, 4);
v_aig_149_ = lean_ctor_get(v_res_148_, 0);
lean_inc_ref(v_aig_149_);
v_vec_150_ = lean_ctor_get(v_res_148_, 1);
lean_inc_ref(v_vec_150_);
lean_dec_ref(v_res_148_);
v_aig_138_ = v_aig_149_;
v_curr_140_ = v___x_146_;
v_acc_141_ = v_vec_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg___boxed(lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_w_154_, lean_object* v_n_155_, lean_object* v_aig_156_, lean_object* v_distance_157_, lean_object* v_curr_158_, lean_object* v_acc_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_152_, v_inst_153_, v_w_154_, v_n_155_, v_aig_156_, v_distance_157_, v_curr_158_, v_acc_159_);
lean_dec(v_w_154_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(lean_object* v_00_u03b1_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_w_164_, lean_object* v_n_165_, lean_object* v_aig_166_, lean_object* v_distance_167_, lean_object* v_curr_168_, lean_object* v_acc_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_162_, v_inst_163_, v_w_164_, v_n_165_, v_aig_166_, v_distance_167_, v_curr_168_, v_acc_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___boxed(lean_object* v_00_u03b1_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_w_174_, lean_object* v_n_175_, lean_object* v_aig_176_, lean_object* v_distance_177_, lean_object* v_curr_178_, lean_object* v_acc_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(v_00_u03b1_171_, v_inst_172_, v_inst_173_, v_w_174_, v_n_175_, v_aig_176_, v_distance_177_, v_curr_178_, v_acc_179_);
lean_dec(v_w_174_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_w_183_, lean_object* v_aig_184_, lean_object* v_target_185_){
_start:
{
lean_object* v_n_186_; lean_object* v_target_187_; lean_object* v_distance_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_n_186_ = lean_ctor_get(v_target_185_, 0);
lean_inc(v_n_186_);
v_target_187_ = lean_ctor_get(v_target_185_, 1);
lean_inc_ref(v_target_187_);
v_distance_188_ = lean_ctor_get(v_target_185_, 2);
lean_inc_ref(v_distance_188_);
lean_dec_ref(v_target_185_);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_nat_dec_eq(v_n_186_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v_res_192_; lean_object* v_aig_193_; lean_object* v_vec_194_; lean_object* v___x_195_; 
lean_inc_ref(v_distance_188_);
lean_inc(v_n_186_);
v___x_191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_191_, 0, v_n_186_);
lean_ctor_set(v___x_191_, 1, v_target_187_);
lean_ctor_set(v___x_191_, 2, v_distance_188_);
lean_ctor_set(v___x_191_, 3, v___x_189_);
lean_inc_ref(v_inst_182_);
lean_inc_ref(v_inst_181_);
v_res_192_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_181_, v_inst_182_, v_w_183_, v_aig_184_, v___x_191_);
lean_dec_ref_known(v___x_191_, 4);
v_aig_193_ = lean_ctor_get(v_res_192_, 0);
lean_inc_ref(v_aig_193_);
v_vec_194_ = lean_ctor_get(v_res_192_, 1);
lean_inc_ref(v_vec_194_);
lean_dec_ref(v_res_192_);
v___x_195_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_181_, v_inst_182_, v_w_183_, v_n_186_, v_aig_193_, v_distance_188_, v___x_189_, v_vec_194_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; 
lean_dec_ref(v_distance_188_);
lean_dec(v_n_186_);
lean_dec_ref(v_inst_182_);
lean_dec_ref(v_inst_181_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_aig_184_);
lean_ctor_set(v___x_196_, 1, v_target_187_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg___boxed(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_w_199_, lean_object* v_aig_200_, lean_object* v_target_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_197_, v_inst_198_, v_w_199_, v_aig_200_, v_target_201_);
lean_dec(v_w_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(lean_object* v_00_u03b1_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_w_206_, lean_object* v_aig_207_, lean_object* v_target_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_204_, v_inst_205_, v_w_206_, v_aig_207_, v_target_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___boxed(lean_object* v_00_u03b1_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_w_213_, lean_object* v_aig_214_, lean_object* v_target_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(v_00_u03b1_210_, v_inst_211_, v_inst_212_, v_w_213_, v_aig_214_, v_target_215_);
lean_dec(v_w_213_);
return v_res_216_;
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
