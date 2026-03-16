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
static lean_once_cell_t l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1;
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
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0);
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_nat_lor(v___x_4_, v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(lean_object* v_w_6_, lean_object* v_aig_7_, lean_object* v_input_8_, lean_object* v_distance_9_, lean_object* v_curr_10_, lean_object* v_s_11_){
_start:
{
lean_object* v_gate_13_; uint8_t v_invert_14_; uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_lt(v_curr_10_, v_w_6_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_dec(v_curr_10_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v_aig_7_);
lean_ctor_set(v___x_24_, 1, v_s_11_);
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = lean_nat_dec_lt(v_curr_10_, v_distance_9_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v_ref_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_26_ = lean_nat_sub(v_curr_10_, v_distance_9_);
v_ref_27_ = lean_array_fget_borrowed(v_input_8_, v___x_26_);
lean_dec(v___x_26_);
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_shiftr(v_ref_27_, v___x_28_);
v___x_30_ = lean_nat_land(v___x_28_, v_ref_27_);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_nat_dec_eq(v___x_30_, v___x_31_);
lean_dec(v___x_30_);
if (v___x_32_ == 0)
{
v_gate_13_ = v___x_29_;
v_invert_14_ = v___x_23_;
goto v___jp_12_;
}
else
{
v_gate_13_ = v___x_29_;
v_invert_14_ = v___x_25_;
goto v___jp_12_;
}
}
else
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_s_36_; 
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_curr_10_, v___x_33_);
lean_dec(v_curr_10_);
v___x_35_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1, &l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1_once, _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1);
v_s_36_ = lean_array_push(v_s_11_, v___x_35_);
v_curr_10_ = v___x_34_;
v_s_11_ = v_s_36_;
goto _start;
}
}
v___jp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_s_21_; 
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_add(v_curr_10_, v___x_15_);
lean_dec(v_curr_10_);
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_nat_mul(v_gate_13_, v___x_17_);
lean_dec(v_gate_13_);
v___x_19_ = l_Bool_toNat(v_invert_14_);
v___x_20_ = lean_nat_lor(v___x_18_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v___x_18_);
v_s_21_ = lean_array_push(v_s_11_, v___x_20_);
v_curr_10_ = v___x_16_;
v_s_11_ = v_s_21_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___boxed(lean_object* v_w_38_, lean_object* v_aig_39_, lean_object* v_input_40_, lean_object* v_distance_41_, lean_object* v_curr_42_, lean_object* v_s_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_38_, v_aig_39_, v_input_40_, v_distance_41_, v_curr_42_, v_s_43_);
lean_dec(v_distance_41_);
lean_dec_ref(v_input_40_);
lean_dec(v_w_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_w_48_, lean_object* v_aig_49_, lean_object* v_input_50_, lean_object* v_distance_51_, lean_object* v_curr_52_, lean_object* v_hcurr_53_, lean_object* v_s_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_48_, v_aig_49_, v_input_50_, v_distance_51_, v_curr_52_, v_s_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___boxed(lean_object* v_00_u03b1_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_w_59_, lean_object* v_aig_60_, lean_object* v_input_61_, lean_object* v_distance_62_, lean_object* v_curr_63_, lean_object* v_hcurr_64_, lean_object* v_s_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(v_00_u03b1_56_, v_inst_57_, v_inst_58_, v_w_59_, v_aig_60_, v_input_61_, v_distance_62_, v_curr_63_, v_hcurr_64_, v_s_65_);
lean_dec(v_distance_62_);
lean_dec_ref(v_input_61_);
lean_dec(v_w_59_);
lean_dec_ref(v_inst_58_);
lean_dec_ref(v_inst_57_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object* v_w_67_, lean_object* v_aig_68_, lean_object* v_target_69_){
_start:
{
lean_object* v_vec_70_; lean_object* v_distance_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_vec_70_ = lean_ctor_get(v_target_69_, 0);
v_distance_71_ = lean_ctor_get(v_target_69_, 1);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = lean_mk_empty_array_with_capacity(v_w_67_);
v___x_74_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(v_w_67_, v_aig_68_, v_vec_70_, v_distance_71_, v___x_72_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg___boxed(lean_object* v_w_75_, lean_object* v_aig_76_, lean_object* v_target_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_75_, v_aig_76_, v_target_77_);
lean_dec_ref(v_target_77_);
lean_dec(v_w_75_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_w_82_, lean_object* v_aig_83_, lean_object* v_target_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_82_, v_aig_83_, v_target_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___boxed(lean_object* v_00_u03b1_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_w_89_, lean_object* v_aig_90_, lean_object* v_target_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(v_00_u03b1_86_, v_inst_87_, v_inst_88_, v_w_89_, v_aig_90_, v_target_91_);
lean_dec_ref(v_target_91_);
lean_dec(v_w_89_);
lean_dec_ref(v_inst_88_);
lean_dec_ref(v_inst_87_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_w_95_, lean_object* v_aig_96_, lean_object* v_target_97_){
_start:
{
lean_object* v_n_98_; lean_object* v_lhs_99_; lean_object* v_rhs_100_; lean_object* v_pow_101_; uint8_t v___x_102_; 
v_n_98_ = lean_ctor_get(v_target_97_, 0);
v_lhs_99_ = lean_ctor_get(v_target_97_, 1);
v_rhs_100_ = lean_ctor_get(v_target_97_, 2);
v_pow_101_ = lean_ctor_get(v_target_97_, 3);
v___x_102_ = lean_nat_dec_lt(v_pow_101_, v_n_98_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v_inst_94_);
lean_dec_ref(v_inst_93_);
lean_inc_ref(v_lhs_99_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_aig_96_);
lean_ctor_set(v___x_103_, 1, v_lhs_99_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_res_107_; lean_object* v_aig_108_; lean_object* v_vec_109_; lean_object* v___y_111_; lean_object* v_ref_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_nat_pow(v___x_104_, v_pow_101_);
lean_inc_ref(v_lhs_99_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_lhs_99_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v_res_107_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_95_, v_aig_96_, v___x_106_);
lean_dec_ref(v___x_106_);
v_aig_108_ = lean_ctor_get(v_res_107_, 0);
lean_inc_ref(v_aig_108_);
v_vec_109_ = lean_ctor_get(v_res_107_, 1);
lean_inc_ref(v_vec_109_);
lean_dec_ref(v_res_107_);
v_ref_114_ = lean_array_fget_borrowed(v_rhs_100_, v_pow_101_);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_shiftr(v_ref_114_, v___x_115_);
v___x_117_ = lean_nat_land(v___x_115_, v_ref_114_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_102_);
v___y_111_ = v___x_120_;
goto v___jp_110_;
}
else
{
uint8_t v___x_121_; lean_object* v___x_122_; 
v___x_121_ = 0;
v___x_122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_122_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___x_121_);
v___y_111_ = v___x_122_;
goto v___jp_110_;
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_inc_ref(v_lhs_99_);
v___x_112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_112_, 0, v___y_111_);
lean_ctor_set(v___x_112_, 1, v_vec_109_);
lean_ctor_set(v___x_112_, 2, v_lhs_99_);
v___x_113_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_93_, v_inst_94_, v_w_95_, v_aig_108_, v___x_112_);
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg___boxed(lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_w_125_, lean_object* v_aig_126_, lean_object* v_target_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_123_, v_inst_124_, v_w_125_, v_aig_126_, v_target_127_);
lean_dec_ref(v_target_127_);
lean_dec(v_w_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(lean_object* v_00_u03b1_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_w_132_, lean_object* v_aig_133_, lean_object* v_target_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_130_, v_inst_131_, v_w_132_, v_aig_133_, v_target_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___boxed(lean_object* v_00_u03b1_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_w_139_, lean_object* v_aig_140_, lean_object* v_target_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(v_00_u03b1_136_, v_inst_137_, v_inst_138_, v_w_139_, v_aig_140_, v_target_141_);
lean_dec_ref(v_target_141_);
lean_dec(v_w_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_w_145_, lean_object* v_n_146_, lean_object* v_aig_147_, lean_object* v_distance_148_, lean_object* v_curr_149_, lean_object* v_acc_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_sub(v_n_146_, v___x_151_);
v___x_153_ = lean_nat_dec_lt(v_curr_149_, v___x_152_);
lean_dec(v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
lean_dec(v_curr_149_);
lean_dec_ref(v_distance_148_);
lean_dec(v_n_146_);
lean_dec_ref(v_inst_144_);
lean_dec_ref(v_inst_143_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_aig_147_);
lean_ctor_set(v___x_154_, 1, v_acc_150_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_res_157_; lean_object* v_aig_158_; lean_object* v_vec_159_; 
v___x_155_ = lean_nat_add(v_curr_149_, v___x_151_);
lean_dec(v_curr_149_);
lean_inc(v___x_155_);
lean_inc_ref(v_distance_148_);
lean_inc(v_n_146_);
v___x_156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_156_, 0, v_n_146_);
lean_ctor_set(v___x_156_, 1, v_acc_150_);
lean_ctor_set(v___x_156_, 2, v_distance_148_);
lean_ctor_set(v___x_156_, 3, v___x_155_);
lean_inc_ref(v_inst_144_);
lean_inc_ref(v_inst_143_);
v_res_157_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_143_, v_inst_144_, v_w_145_, v_aig_147_, v___x_156_);
lean_dec_ref(v___x_156_);
v_aig_158_ = lean_ctor_get(v_res_157_, 0);
lean_inc_ref(v_aig_158_);
v_vec_159_ = lean_ctor_get(v_res_157_, 1);
lean_inc_ref(v_vec_159_);
lean_dec_ref(v_res_157_);
v_aig_147_ = v_aig_158_;
v_curr_149_ = v___x_155_;
v_acc_150_ = v_vec_159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg___boxed(lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_w_163_, lean_object* v_n_164_, lean_object* v_aig_165_, lean_object* v_distance_166_, lean_object* v_curr_167_, lean_object* v_acc_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_161_, v_inst_162_, v_w_163_, v_n_164_, v_aig_165_, v_distance_166_, v_curr_167_, v_acc_168_);
lean_dec(v_w_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_w_173_, lean_object* v_n_174_, lean_object* v_aig_175_, lean_object* v_distance_176_, lean_object* v_curr_177_, lean_object* v_acc_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_171_, v_inst_172_, v_w_173_, v_n_174_, v_aig_175_, v_distance_176_, v_curr_177_, v_acc_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___boxed(lean_object* v_00_u03b1_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_w_183_, lean_object* v_n_184_, lean_object* v_aig_185_, lean_object* v_distance_186_, lean_object* v_curr_187_, lean_object* v_acc_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(v_00_u03b1_180_, v_inst_181_, v_inst_182_, v_w_183_, v_n_184_, v_aig_185_, v_distance_186_, v_curr_187_, v_acc_188_);
lean_dec(v_w_183_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_w_192_, lean_object* v_aig_193_, lean_object* v_target_194_){
_start:
{
lean_object* v_n_195_; lean_object* v_target_196_; lean_object* v_distance_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_n_195_ = lean_ctor_get(v_target_194_, 0);
lean_inc(v_n_195_);
v_target_196_ = lean_ctor_get(v_target_194_, 1);
lean_inc_ref(v_target_196_);
v_distance_197_ = lean_ctor_get(v_target_194_, 2);
lean_inc_ref(v_distance_197_);
lean_dec_ref(v_target_194_);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_nat_dec_eq(v_n_195_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v_res_201_; lean_object* v_aig_202_; lean_object* v_vec_203_; lean_object* v___x_204_; 
lean_inc_ref(v_distance_197_);
lean_inc(v_n_195_);
v___x_200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_200_, 0, v_n_195_);
lean_ctor_set(v___x_200_, 1, v_target_196_);
lean_ctor_set(v___x_200_, 2, v_distance_197_);
lean_ctor_set(v___x_200_, 3, v___x_198_);
lean_inc_ref(v_inst_191_);
lean_inc_ref(v_inst_190_);
v_res_201_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(v_inst_190_, v_inst_191_, v_w_192_, v_aig_193_, v___x_200_);
lean_dec_ref(v___x_200_);
v_aig_202_ = lean_ctor_get(v_res_201_, 0);
lean_inc_ref(v_aig_202_);
v_vec_203_ = lean_ctor_get(v_res_201_, 1);
lean_inc_ref(v_vec_203_);
lean_dec_ref(v_res_201_);
v___x_204_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(v_inst_190_, v_inst_191_, v_w_192_, v_n_195_, v_aig_202_, v_distance_197_, v___x_198_, v_vec_203_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
lean_dec_ref(v_distance_197_);
lean_dec(v_n_195_);
lean_dec_ref(v_inst_191_);
lean_dec_ref(v_inst_190_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v_aig_193_);
lean_ctor_set(v___x_205_, 1, v_target_196_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg___boxed(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_w_208_, lean_object* v_aig_209_, lean_object* v_target_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_206_, v_inst_207_, v_w_208_, v_aig_209_, v_target_210_);
lean_dec(v_w_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_w_215_, lean_object* v_aig_216_, lean_object* v_target_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(v_inst_213_, v_inst_214_, v_w_215_, v_aig_216_, v_target_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___boxed(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_w_222_, lean_object* v_aig_223_, lean_object* v_target_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(v_00_u03b1_219_, v_inst_220_, v_inst_221_, v_w_222_, v_aig_223_, v_target_224_);
lean_dec(v_w_222_);
return v_res_225_;
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
