// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const import Init.Omega
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
lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_lhs_5_, lean_object* v_rhs_6_, lean_object* v_curr_7_, lean_object* v_acc_8_){
_start:
{
lean_object* v___y_10_; lean_object* v___y_11_; lean_object* v___y_12_; uint8_t v___x_20_; lean_object* v___y_22_; 
v___x_20_ = lean_nat_dec_lt(v_curr_7_, v_w_3_);
if (v___x_20_ == 0)
{
lean_object* v___x_50_; 
lean_dec(v_curr_7_);
lean_dec_ref(v_lhs_5_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v_aig_4_);
lean_ctor_set(v___x_50_, 1, v_acc_8_);
return v___x_50_;
}
else
{
lean_object* v_ref_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v_ref_51_ = lean_array_fget_borrowed(v_rhs_6_, v_curr_7_);
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_shiftr(v_ref_51_, v___x_52_);
v___x_54_ = lean_nat_land(v___x_52_, v_ref_51_);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_nat_dec_eq(v___x_54_, v___x_55_);
lean_dec(v___x_54_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
v___x_57_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_57_, 0, v___x_53_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*1, v___x_20_);
v___y_22_ = v___x_57_;
goto v___jp_21_;
}
else
{
uint8_t v___x_58_; lean_object* v___x_59_; 
v___x_58_ = 0;
v___x_59_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_53_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___x_58_);
v___y_22_ = v___x_59_;
goto v___jp_21_;
}
}
v___jp_9_:
{
lean_object* v___x_13_; lean_object* v_res_14_; lean_object* v_aig_15_; lean_object* v_vec_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_13_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_13_, 0, v___y_12_);
lean_ctor_set(v___x_13_, 1, v___y_11_);
lean_ctor_set(v___x_13_, 2, v_acc_8_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_14_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_1_, v_inst_2_, v_w_3_, v___y_10_, v___x_13_);
v_aig_15_ = lean_ctor_get(v_res_14_, 0);
lean_inc_ref(v_aig_15_);
v_vec_16_ = lean_ctor_get(v_res_14_, 1);
lean_inc_ref(v_vec_16_);
lean_dec_ref(v_res_14_);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_add(v_curr_7_, v___x_17_);
lean_dec(v_curr_7_);
v_aig_4_ = v_aig_15_;
v_curr_7_ = v___x_18_;
v_acc_8_ = v_vec_16_;
goto _start;
}
v___jp_21_:
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 0;
v___x_24_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_4_, v___y_22_, v___x_23_);
lean_dec_ref(v___y_22_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v_res_26_; lean_object* v_aig_27_; lean_object* v_vec_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_46_; 
lean_inc(v_curr_7_);
lean_inc_ref(v_lhs_5_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v_lhs_5_);
lean_ctor_set(v___x_25_, 1, v_curr_7_);
v_res_26_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_3_, v_aig_4_, v___x_25_);
lean_dec_ref(v___x_25_);
v_aig_27_ = lean_ctor_get(v_res_26_, 0);
v_vec_28_ = lean_ctor_get(v_res_26_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_res_26_);
if (v_isSharedCheck_46_ == 0)
{
v___x_30_ = v_res_26_;
v_isShared_31_ = v_isSharedCheck_46_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_vec_28_);
lean_inc(v_aig_27_);
lean_dec(v_res_26_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_46_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
lean_inc_ref(v_acc_8_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v_acc_8_);
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_acc_8_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_vec_28_);
v___x_33_ = v_reuseFailAlloc_45_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v_res_34_; lean_object* v_aig_35_; lean_object* v_vec_36_; lean_object* v_ref_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_34_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_27_, v___x_33_);
v_aig_35_ = lean_ctor_get(v_res_34_, 0);
lean_inc_ref(v_aig_35_);
v_vec_36_ = lean_ctor_get(v_res_34_, 1);
lean_inc_ref(v_vec_36_);
lean_dec_ref(v_res_34_);
v_ref_37_ = lean_array_fget_borrowed(v_rhs_6_, v_curr_7_);
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_shiftr(v_ref_37_, v___x_38_);
v___x_40_ = lean_nat_land(v___x_38_, v_ref_37_);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_nat_dec_eq(v___x_40_, v___x_41_);
lean_dec(v___x_40_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; 
v___x_43_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_43_, 0, v___x_39_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*1, v___x_20_);
v___y_10_ = v_aig_35_;
v___y_11_ = v_vec_36_;
v___y_12_ = v___x_43_;
goto v___jp_9_;
}
else
{
lean_object* v___x_44_; 
v___x_44_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_44_, 0, v___x_39_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*1, v___x_24_);
v___y_10_ = v_aig_35_;
v___y_11_ = v_vec_36_;
v___y_12_ = v___x_44_;
goto v___jp_9_;
}
}
}
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_curr_7_, v___x_47_);
lean_dec(v_curr_7_);
v_curr_7_ = v___x_48_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg___boxed(lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_w_62_, lean_object* v_aig_63_, lean_object* v_lhs_64_, lean_object* v_rhs_65_, lean_object* v_curr_66_, lean_object* v_acc_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(v_inst_60_, v_inst_61_, v_w_62_, v_aig_63_, v_lhs_64_, v_rhs_65_, v_curr_66_, v_acc_67_);
lean_dec_ref(v_rhs_65_);
lean_dec(v_w_62_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_w_72_, lean_object* v_aig_73_, lean_object* v_lhs_74_, lean_object* v_rhs_75_, lean_object* v_curr_76_, lean_object* v_acc_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(v_inst_70_, v_inst_71_, v_w_72_, v_aig_73_, v_lhs_74_, v_rhs_75_, v_curr_76_, v_acc_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_w_82_, lean_object* v_aig_83_, lean_object* v_lhs_84_, lean_object* v_rhs_85_, lean_object* v_curr_86_, lean_object* v_acc_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(v_00_u03b1_79_, v_inst_80_, v_inst_81_, v_w_82_, v_aig_83_, v_lhs_84_, v_rhs_85_, v_curr_86_, v_acc_87_);
lean_dec_ref(v_rhs_85_);
lean_dec(v_w_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_w_91_, lean_object* v_aig_92_, lean_object* v_input_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_eq(v_w_91_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v_lhs_96_; lean_object* v_rhs_97_; lean_object* v___x_98_; lean_object* v_zero_99_; lean_object* v___y_101_; lean_object* v_ref_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_lhs_96_ = lean_ctor_get(v_input_93_, 0);
lean_inc_ref(v_lhs_96_);
v_rhs_97_ = lean_ctor_get(v_input_93_, 1);
lean_inc_ref(v_rhs_97_);
lean_dec_ref(v_input_93_);
v___x_98_ = l_BitVec_ofNat(v_w_91_, v___x_94_);
v_zero_99_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_91_, v___x_98_);
lean_dec(v___x_98_);
v_ref_108_ = lean_array_fget_borrowed(v_rhs_97_, v___x_94_);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_shiftr(v_ref_108_, v___x_109_);
v___x_111_ = lean_nat_land(v___x_109_, v_ref_108_);
v___x_112_ = lean_nat_dec_eq(v___x_111_, v___x_94_);
lean_dec(v___x_111_);
if (v___x_112_ == 0)
{
uint8_t v___x_113_; lean_object* v___x_114_; 
v___x_113_ = 1;
v___x_114_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_113_);
v___y_101_ = v___x_114_;
goto v___jp_100_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_95_);
v___y_101_ = v___x_115_;
goto v___jp_100_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v_res_103_; lean_object* v_aig_104_; lean_object* v_vec_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_inc_ref(v_lhs_96_);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v___y_101_);
lean_ctor_set(v___x_102_, 1, v_lhs_96_);
lean_ctor_set(v___x_102_, 2, v_zero_99_);
lean_inc_ref(v_inst_90_);
lean_inc_ref(v_inst_89_);
v_res_103_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_89_, v_inst_90_, v_w_91_, v_aig_92_, v___x_102_);
v_aig_104_ = lean_ctor_get(v_res_103_, 0);
lean_inc_ref(v_aig_104_);
v_vec_105_ = lean_ctor_get(v_res_103_, 1);
lean_inc_ref(v_vec_105_);
lean_dec_ref(v_res_103_);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(v_inst_89_, v_inst_90_, v_w_91_, v_aig_104_, v_lhs_96_, v_rhs_97_, v___x_106_, v_vec_105_);
lean_dec_ref(v_rhs_97_);
return v___x_107_;
}
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec_ref(v_input_93_);
v___x_116_ = l_Std_Sat_AIG_RefVec_empty(lean_box(0), v_inst_89_, v_inst_90_, v_aig_92_);
lean_dec_ref(v_inst_90_);
lean_dec_ref(v_inst_89_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v_aig_92_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg___boxed(lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_w_120_, lean_object* v_aig_121_, lean_object* v_input_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_118_, v_inst_119_, v_w_120_, v_aig_121_, v_input_122_);
lean_dec(v_w_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object* v_00_u03b1_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_w_127_, lean_object* v_aig_128_, lean_object* v_input_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_125_, v_inst_126_, v_w_127_, v_aig_128_, v_input_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_w_134_, lean_object* v_aig_135_, lean_object* v_input_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(v_00_u03b1_131_, v_inst_132_, v_inst_133_, v_w_134_, v_aig_135_, v_input_136_);
lean_dec(v_w_134_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_w_140_, lean_object* v_aig_141_, lean_object* v_input_142_){
_start:
{
lean_object* v_lhs_143_; lean_object* v_rhs_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_lhs_143_ = lean_ctor_get(v_input_142_, 0);
v_rhs_144_ = lean_ctor_get(v_input_142_, 1);
v___x_145_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_140_, v_aig_141_, v_lhs_143_);
v___x_146_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_140_, v_aig_141_, v_rhs_144_);
v___x_147_ = lean_nat_dec_lt(v___x_145_, v___x_146_);
lean_dec(v___x_146_);
lean_dec(v___x_145_);
if (v___x_147_ == 0)
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
lean_inc_ref(v_rhs_144_);
lean_inc_ref(v_lhs_143_);
v_isSharedCheck_155_ = !lean_is_exclusive(v_input_142_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; 
v_unused_156_ = lean_ctor_get(v_input_142_, 1);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_input_142_, 0);
lean_dec(v_unused_157_);
v___x_149_ = v_input_142_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_input_142_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v_lhs_143_);
lean_ctor_set(v___x_149_, 0, v_rhs_144_);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_rhs_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_lhs_143_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_138_, v_inst_139_, v_w_140_, v_aig_141_, v___x_152_);
return v___x_153_;
}
}
}
else
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_138_, v_inst_139_, v_w_140_, v_aig_141_, v_input_142_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg___boxed(lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_w_161_, lean_object* v_aig_162_, lean_object* v_input_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(v_inst_159_, v_inst_160_, v_w_161_, v_aig_162_, v_input_163_);
lean_dec(v_w_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_w_168_, lean_object* v_aig_169_, lean_object* v_input_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(v_inst_166_, v_inst_167_, v_w_168_, v_aig_169_, v_input_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object* v_00_u03b1_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_w_175_, lean_object* v_aig_176_, lean_object* v_input_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(v_00_u03b1_172_, v_inst_173_, v_inst_174_, v_w_175_, v_aig_176_, v_input_177_);
lean_dec(v_w_175_);
return v_res_178_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
}
#ifdef __cplusplus
}
#endif
