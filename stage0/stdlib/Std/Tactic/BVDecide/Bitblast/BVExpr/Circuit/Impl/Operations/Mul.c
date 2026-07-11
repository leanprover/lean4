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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_lt(v_curr_7_, v_w_3_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_curr_7_);
lean_dec_ref(v_lhs_5_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_aig_4_);
lean_ctor_set(v___x_10_, 1, v_acc_8_);
return v___x_10_;
}
else
{
lean_object* v_ref_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; uint8_t v___x_20_; 
v_ref_11_ = lean_array_fget_borrowed(v_rhs_6_, v_curr_7_);
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_shiftr(v_ref_11_, v___x_12_);
v___x_14_ = lean_nat_land(v___x_12_, v_ref_11_);
v___x_15_ = lean_unsigned_to_nat(0u);
v___x_16_ = lean_nat_dec_eq(v___x_14_, v___x_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_bool_not(v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_18_, 0, v___x_13_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*1, v___x_17_);
v___x_19_ = 0;
v___x_20_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_4_, v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v_res_22_; lean_object* v_aig_23_; lean_object* v_vec_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_40_; 
lean_inc(v_curr_7_);
lean_inc_ref(v_lhs_5_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_lhs_5_);
lean_ctor_set(v___x_21_, 1, v_curr_7_);
v_res_22_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(v_w_3_, v_aig_4_, v___x_21_);
lean_dec_ref_known(v___x_21_, 2);
v_aig_23_ = lean_ctor_get(v_res_22_, 0);
v_vec_24_ = lean_ctor_get(v_res_22_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_res_22_);
if (v_isSharedCheck_40_ == 0)
{
v___x_26_ = v_res_22_;
v_isShared_27_ = v_isSharedCheck_40_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_vec_24_);
lean_inc(v_aig_23_);
lean_dec(v_res_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_40_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
lean_inc_ref(v_acc_8_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v_acc_8_);
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_acc_8_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_vec_24_);
v___x_29_ = v_reuseFailAlloc_39_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v_res_30_; lean_object* v_aig_31_; lean_object* v_vec_32_; lean_object* v___x_33_; lean_object* v_res_34_; lean_object* v_aig_35_; lean_object* v_vec_36_; lean_object* v___x_37_; 
lean_inc_ref_n(v_inst_2_, 2);
lean_inc_ref_n(v_inst_1_, 2);
v_res_30_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_23_, v___x_29_);
v_aig_31_ = lean_ctor_get(v_res_30_, 0);
lean_inc_ref(v_aig_31_);
v_vec_32_ = lean_ctor_get(v_res_30_, 1);
lean_inc_ref(v_vec_32_);
lean_dec_ref(v_res_30_);
v___x_33_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_33_, 0, v___x_18_);
lean_ctor_set(v___x_33_, 1, v_vec_32_);
lean_ctor_set(v___x_33_, 2, v_acc_8_);
v_res_34_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_31_, v___x_33_);
v_aig_35_ = lean_ctor_get(v_res_34_, 0);
lean_inc_ref(v_aig_35_);
v_vec_36_ = lean_ctor_get(v_res_34_, 1);
lean_inc_ref(v_vec_36_);
lean_dec_ref(v_res_34_);
v___x_37_ = lean_nat_add(v_curr_7_, v___x_12_);
lean_dec(v_curr_7_);
v_aig_4_ = v_aig_35_;
v_curr_7_ = v___x_37_;
v_acc_8_ = v_vec_36_;
goto _start;
}
}
}
else
{
lean_object* v___x_41_; 
lean_dec_ref_known(v___x_18_, 1);
v___x_41_ = lean_nat_add(v_curr_7_, v___x_12_);
lean_dec(v_curr_7_);
v_curr_7_ = v___x_41_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg___boxed(lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_w_45_, lean_object* v_aig_46_, lean_object* v_lhs_47_, lean_object* v_rhs_48_, lean_object* v_curr_49_, lean_object* v_acc_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(v_inst_43_, v_inst_44_, v_w_45_, v_aig_46_, v_lhs_47_, v_rhs_48_, v_curr_49_, v_acc_50_);
lean_dec_ref(v_rhs_48_);
lean_dec(v_w_45_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object* v_00_u03b1_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_w_55_, lean_object* v_aig_56_, lean_object* v_lhs_57_, lean_object* v_rhs_58_, lean_object* v_curr_59_, lean_object* v_acc_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(v_inst_53_, v_inst_54_, v_w_55_, v_aig_56_, v_lhs_57_, v_rhs_58_, v_curr_59_, v_acc_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_w_65_, lean_object* v_aig_66_, lean_object* v_lhs_67_, lean_object* v_rhs_68_, lean_object* v_curr_69_, lean_object* v_acc_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(v_00_u03b1_62_, v_inst_63_, v_inst_64_, v_w_65_, v_aig_66_, v_lhs_67_, v_rhs_68_, v_curr_69_, v_acc_70_);
lean_dec_ref(v_rhs_68_);
lean_dec(v_w_65_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_w_74_, lean_object* v_aig_75_, lean_object* v_input_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_nat_dec_eq(v_w_74_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v_lhs_79_; lean_object* v_rhs_80_; lean_object* v___x_81_; lean_object* v_zero_82_; lean_object* v_ref_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_res_91_; lean_object* v_aig_92_; lean_object* v_vec_93_; lean_object* v___x_94_; 
v_lhs_79_ = lean_ctor_get(v_input_76_, 0);
lean_inc_ref_n(v_lhs_79_, 2);
v_rhs_80_ = lean_ctor_get(v_input_76_, 1);
lean_inc_ref(v_rhs_80_);
lean_dec_ref(v_input_76_);
v___x_81_ = l_BitVec_ofNat(v_w_74_, v___x_77_);
v_zero_82_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_74_, v___x_81_);
lean_dec(v___x_81_);
v_ref_83_ = lean_array_fget_borrowed(v_rhs_80_, v___x_77_);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_shiftr(v_ref_83_, v___x_84_);
v___x_86_ = lean_nat_land(v___x_84_, v_ref_83_);
v___x_87_ = lean_nat_dec_eq(v___x_86_, v___x_77_);
lean_dec(v___x_86_);
v___x_88_ = lean_bool_not(v___x_87_);
v___x_89_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_lhs_79_);
lean_ctor_set(v___x_90_, 2, v_zero_82_);
lean_inc_ref(v_inst_73_);
lean_inc_ref(v_inst_72_);
v_res_91_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_72_, v_inst_73_, v_w_74_, v_aig_75_, v___x_90_);
v_aig_92_ = lean_ctor_get(v_res_91_, 0);
lean_inc_ref(v_aig_92_);
v_vec_93_ = lean_ctor_get(v_res_91_, 1);
lean_inc_ref(v_vec_93_);
lean_dec_ref(v_res_91_);
v___x_94_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(v_inst_72_, v_inst_73_, v_w_74_, v_aig_92_, v_lhs_79_, v_rhs_80_, v___x_84_, v_vec_93_);
lean_dec_ref(v_rhs_80_);
return v___x_94_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec_ref(v_input_76_);
v___x_95_ = l_Std_Sat_AIG_RefVec_empty(lean_box(0), v_inst_72_, v_inst_73_, v_aig_75_);
lean_dec_ref(v_inst_73_);
lean_dec_ref(v_inst_72_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_aig_75_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg___boxed(lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_w_99_, lean_object* v_aig_100_, lean_object* v_input_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_97_, v_inst_98_, v_w_99_, v_aig_100_, v_input_101_);
lean_dec(v_w_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_w_106_, lean_object* v_aig_107_, lean_object* v_input_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_104_, v_inst_105_, v_w_106_, v_aig_107_, v_input_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_w_113_, lean_object* v_aig_114_, lean_object* v_input_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(v_00_u03b1_110_, v_inst_111_, v_inst_112_, v_w_113_, v_aig_114_, v_input_115_);
lean_dec(v_w_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_w_119_, lean_object* v_aig_120_, lean_object* v_input_121_){
_start:
{
lean_object* v_lhs_122_; lean_object* v_rhs_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_lhs_122_ = lean_ctor_get(v_input_121_, 0);
v_rhs_123_ = lean_ctor_get(v_input_121_, 1);
v___x_124_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_119_, v_aig_120_, v_lhs_122_);
v___x_125_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_119_, v_aig_120_, v_rhs_123_);
v___x_126_ = lean_nat_dec_lt(v___x_124_, v___x_125_);
lean_dec(v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_134_; 
lean_inc_ref(v_rhs_123_);
lean_inc_ref(v_lhs_122_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_input_121_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_input_121_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_input_121_, 0);
lean_dec(v_unused_136_);
v___x_128_ = v_input_121_;
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
else
{
lean_dec(v_input_121_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_lhs_122_);
lean_ctor_set(v___x_128_, 0, v_rhs_123_);
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_rhs_123_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_lhs_122_);
v___x_131_ = v_reuseFailAlloc_133_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_117_, v_inst_118_, v_w_119_, v_aig_120_, v___x_131_);
return v___x_132_;
}
}
}
else
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(v_inst_117_, v_inst_118_, v_w_119_, v_aig_120_, v_input_121_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg___boxed(lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_w_140_, lean_object* v_aig_141_, lean_object* v_input_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(v_inst_138_, v_inst_139_, v_w_140_, v_aig_141_, v_input_142_);
lean_dec(v_w_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object* v_00_u03b1_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_w_147_, lean_object* v_aig_148_, lean_object* v_input_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(v_inst_145_, v_inst_146_, v_w_147_, v_aig_148_, v_input_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_w_154_, lean_object* v_aig_155_, lean_object* v_input_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(v_00_u03b1_151_, v_inst_152_, v_inst_153_, v_w_154_, v_aig_155_, v_input_156_);
lean_dec(v_w_154_);
return v_res_157_;
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
