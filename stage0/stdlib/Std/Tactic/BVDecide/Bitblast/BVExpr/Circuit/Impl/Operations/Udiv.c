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
lean_object* l_Bool_toNat(uint8_t);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_16_ = l_Bool_toNat(v_invert_10_);
v___x_17_ = lean_nat_lor(v___x_15_, v___x_16_);
lean_dec(v___x_16_);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_w_52_, lean_object* v_aig_53_, lean_object* v_n_54_, lean_object* v_d_55_, lean_object* v_wn_56_, lean_object* v_wr_57_, lean_object* v_q_58_, lean_object* v_r_59_){
_start:
{
lean_object* v___x_60_; lean_object* v_wn_61_; lean_object* v_wr_62_; uint8_t v___x_63_; lean_object* v___y_65_; uint8_t v___x_123_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v_wn_61_ = lean_nat_sub(v_wn_56_, v___x_60_);
v_wr_62_ = lean_nat_add(v_wr_57_, v___x_60_);
v___x_63_ = 0;
v___x_123_ = lean_nat_dec_lt(v_wn_61_, v_w_52_);
if (v___x_123_ == 0)
{
lean_object* v_falseRef_124_; 
v_falseRef_124_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0));
v___y_65_ = v_falseRef_124_;
goto v___jp_64_;
}
else
{
lean_object* v_ref_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_ref_125_ = lean_array_fget_borrowed(v_n_54_, v_wn_61_);
v___x_126_ = lean_nat_shiftr(v_ref_125_, v___x_60_);
v___x_127_ = lean_nat_land(v___x_60_, v_ref_125_);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_dec_eq(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_130_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v___x_123_);
v___y_65_ = v___x_130_;
goto v___jp_64_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_63_);
v___y_65_ = v___x_131_;
goto v___jp_64_;
}
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v_res_67_; lean_object* v_aig_68_; lean_object* v_vec_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_122_; 
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_r_59_);
lean_ctor_set(v___x_66_, 1, v___y_65_);
v_res_67_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_52_, v_aig_53_, v___x_66_);
v_aig_68_ = lean_ctor_get(v_res_67_, 0);
v_vec_69_ = lean_ctor_get(v_res_67_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_res_67_);
if (v_isSharedCheck_122_ == 0)
{
v___x_71_ = v_res_67_;
v_isShared_72_ = v_isSharedCheck_122_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_vec_69_);
lean_inc(v_aig_68_);
lean_dec(v_res_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_122_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_falseRef_73_; lean_object* v___x_75_; 
v_falseRef_73_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0));
lean_inc_ref(v_q_58_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v_falseRef_73_);
lean_ctor_set(v___x_71_, 0, v_q_58_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_q_58_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_falseRef_73_);
v___x_75_ = v_reuseFailAlloc_121_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v_res_76_; lean_object* v_aig_77_; lean_object* v_vec_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_120_; 
v_res_76_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_52_, v_aig_68_, v___x_75_);
v_aig_77_ = lean_ctor_get(v_res_76_, 0);
v_vec_78_ = lean_ctor_get(v_res_76_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_res_76_);
if (v_isSharedCheck_120_ == 0)
{
v___x_80_ = v_res_76_;
v_isShared_81_ = v_isSharedCheck_120_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_vec_78_);
lean_inc(v_aig_77_);
lean_dec(v_res_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_120_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_trueRef_82_; lean_object* v___x_84_; 
v_trueRef_82_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1));
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v_trueRef_82_);
lean_ctor_set(v___x_80_, 0, v_q_58_);
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_q_58_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_trueRef_82_);
v___x_84_ = v_reuseFailAlloc_119_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v_res_85_; lean_object* v_aig_86_; lean_object* v_vec_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_118_; 
v_res_85_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(v_w_52_, v_aig_77_, v___x_84_);
v_aig_86_ = lean_ctor_get(v_res_85_, 0);
v_vec_87_ = lean_ctor_get(v_res_85_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_res_85_);
if (v_isSharedCheck_118_ == 0)
{
v___x_89_ = v_res_85_;
v_isShared_90_ = v_isSharedCheck_118_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_vec_87_);
lean_inc(v_aig_86_);
lean_dec(v_res_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_118_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
lean_inc_ref(v_vec_69_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_d_55_);
lean_ctor_set(v___x_89_, 0, v_vec_69_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_vec_69_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_d_55_);
v___x_92_ = v_reuseFailAlloc_117_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v_res_93_; lean_object* v_aig_94_; lean_object* v_vec_95_; lean_object* v_res_96_; lean_object* v_aig_97_; lean_object* v_ref_98_; lean_object* v___x_99_; lean_object* v_res_100_; lean_object* v_aig_101_; lean_object* v_vec_102_; lean_object* v_gate_103_; uint8_t v_invert_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_116_; 
lean_inc_ref(v___x_92_);
lean_inc_ref(v_inst_51_);
lean_inc_ref(v_inst_50_);
v_res_93_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(v_inst_50_, v_inst_51_, v_w_52_, v_aig_86_, v___x_92_);
v_aig_94_ = lean_ctor_get(v_res_93_, 0);
lean_inc_ref(v_aig_94_);
v_vec_95_ = lean_ctor_get(v_res_93_, 1);
lean_inc_ref(v_vec_95_);
lean_dec_ref(v_res_93_);
lean_inc(v_w_52_);
lean_inc_ref(v_inst_51_);
lean_inc_ref(v_inst_50_);
v_res_96_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(v_inst_50_, v_inst_51_, v_w_52_, v_aig_94_, v___x_92_);
v_aig_97_ = lean_ctor_get(v_res_96_, 0);
lean_inc_ref(v_aig_97_);
v_ref_98_ = lean_ctor_get(v_res_96_, 1);
lean_inc_ref(v_ref_98_);
lean_dec_ref(v_res_96_);
lean_inc_ref(v_ref_98_);
v___x_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_99_, 0, v_ref_98_);
lean_ctor_set(v___x_99_, 1, v_vec_78_);
lean_ctor_set(v___x_99_, 2, v_vec_87_);
lean_inc_ref(v_inst_51_);
lean_inc_ref(v_inst_50_);
v_res_100_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_50_, v_inst_51_, v_w_52_, v_aig_97_, v___x_99_);
v_aig_101_ = lean_ctor_get(v_res_100_, 0);
lean_inc_ref(v_aig_101_);
v_vec_102_ = lean_ctor_get(v_res_100_, 1);
lean_inc_ref(v_vec_102_);
lean_dec_ref(v_res_100_);
v_gate_103_ = lean_ctor_get(v_ref_98_, 0);
v_invert_104_ = lean_ctor_get_uint8(v_ref_98_, sizeof(void*)*1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_ref_98_);
if (v_isSharedCheck_116_ == 0)
{
v___x_106_ = v_ref_98_;
v_isShared_107_ = v_isSharedCheck_116_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_gate_103_);
lean_dec(v_ref_98_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_116_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_discr_109_; 
if (v_isShared_107_ == 0)
{
v_discr_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_gate_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*1, v_invert_104_);
v_discr_109_ = v_reuseFailAlloc_115_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v_res_111_; lean_object* v_aig_112_; lean_object* v_vec_113_; lean_object* v___x_114_; 
v___x_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_110_, 0, v_discr_109_);
lean_ctor_set(v___x_110_, 1, v_vec_69_);
lean_ctor_set(v___x_110_, 2, v_vec_95_);
v_res_111_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_50_, v_inst_51_, v_w_52_, v_aig_101_, v___x_110_);
lean_dec(v_w_52_);
v_aig_112_ = lean_ctor_get(v_res_111_, 0);
lean_inc_ref(v_aig_112_);
v_vec_113_ = lean_ctor_get(v_res_111_, 1);
lean_inc_ref(v_vec_113_);
lean_dec_ref(v_res_111_);
v___x_114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_114_, 0, v_aig_112_);
lean_ctor_set(v___x_114_, 1, v_wn_61_);
lean_ctor_set(v___x_114_, 2, v_wr_62_);
lean_ctor_set(v___x_114_, 3, v_vec_102_);
lean_ctor_set(v___x_114_, 4, v_vec_113_);
return v___x_114_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___boxed(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_w_134_, lean_object* v_aig_135_, lean_object* v_n_136_, lean_object* v_d_137_, lean_object* v_wn_138_, lean_object* v_wr_139_, lean_object* v_q_140_, lean_object* v_r_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_132_, v_inst_133_, v_w_134_, v_aig_135_, v_n_136_, v_d_137_, v_wn_138_, v_wr_139_, v_q_140_, v_r_141_);
lean_dec(v_wr_139_);
lean_dec(v_wn_138_);
lean_dec_ref(v_n_136_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object* v_00_u03b1_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_w_146_, lean_object* v_aig_147_, lean_object* v_n_148_, lean_object* v_d_149_, lean_object* v_wn_150_, lean_object* v_wr_151_, lean_object* v_q_152_, lean_object* v_r_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_144_, v_inst_145_, v_w_146_, v_aig_147_, v_n_148_, v_d_149_, v_wn_150_, v_wr_151_, v_q_152_, v_r_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___boxed(lean_object* v_00_u03b1_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_w_158_, lean_object* v_aig_159_, lean_object* v_n_160_, lean_object* v_d_161_, lean_object* v_wn_162_, lean_object* v_wr_163_, lean_object* v_q_164_, lean_object* v_r_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(v_00_u03b1_155_, v_inst_156_, v_inst_157_, v_w_158_, v_aig_159_, v_n_160_, v_d_161_, v_wn_162_, v_wr_163_, v_q_164_, v_r_165_);
lean_dec(v_wr_163_);
lean_dec(v_wn_162_);
lean_dec_ref(v_n_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_w_169_, lean_object* v_aig_170_, lean_object* v_curr_171_, lean_object* v_n_172_, lean_object* v_d_173_, lean_object* v_wn_174_, lean_object* v_wr_175_, lean_object* v_q_176_, lean_object* v_r_177_){
_start:
{
lean_object* v_zero_178_; uint8_t v_isZero_179_; 
v_zero_178_ = lean_unsigned_to_nat(0u);
v_isZero_179_ = lean_nat_dec_eq(v_curr_171_, v_zero_178_);
if (v_isZero_179_ == 1)
{
lean_object* v___x_180_; 
lean_dec_ref(v_d_173_);
lean_dec(v_w_169_);
lean_dec_ref(v_inst_168_);
lean_dec_ref(v_inst_167_);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v_aig_170_);
lean_ctor_set(v___x_180_, 1, v_q_176_);
lean_ctor_set(v___x_180_, 2, v_r_177_);
return v___x_180_;
}
else
{
lean_object* v_res_181_; lean_object* v_aig_182_; lean_object* v_wn_183_; lean_object* v_wr_184_; lean_object* v_q_185_; lean_object* v_r_186_; lean_object* v_one_187_; lean_object* v_n_188_; lean_object* v_res_189_; lean_object* v_aig_190_; lean_object* v_q_191_; lean_object* v_r_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_inc_ref(v_d_173_);
lean_inc(v_w_169_);
lean_inc_ref(v_inst_168_);
lean_inc_ref(v_inst_167_);
v_res_181_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_167_, v_inst_168_, v_w_169_, v_aig_170_, v_n_172_, v_d_173_, v_wn_174_, v_wr_175_, v_q_176_, v_r_177_);
v_aig_182_ = lean_ctor_get(v_res_181_, 0);
lean_inc_ref(v_aig_182_);
v_wn_183_ = lean_ctor_get(v_res_181_, 1);
lean_inc(v_wn_183_);
v_wr_184_ = lean_ctor_get(v_res_181_, 2);
lean_inc(v_wr_184_);
v_q_185_ = lean_ctor_get(v_res_181_, 3);
lean_inc_ref(v_q_185_);
v_r_186_ = lean_ctor_get(v_res_181_, 4);
lean_inc_ref(v_r_186_);
lean_dec_ref(v_res_181_);
v_one_187_ = lean_unsigned_to_nat(1u);
v_n_188_ = lean_nat_sub(v_curr_171_, v_one_187_);
v_res_189_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_167_, v_inst_168_, v_w_169_, v_aig_182_, v_n_188_, v_n_172_, v_d_173_, v_wn_183_, v_wr_184_, v_q_185_, v_r_186_);
lean_dec(v_wr_184_);
lean_dec(v_wn_183_);
lean_dec(v_n_188_);
v_aig_190_ = lean_ctor_get(v_res_189_, 0);
v_q_191_ = lean_ctor_get(v_res_189_, 1);
v_r_192_ = lean_ctor_get(v_res_189_, 2);
v_isSharedCheck_199_ = !lean_is_exclusive(v_res_189_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v_res_189_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_r_192_);
lean_inc(v_q_191_);
lean_inc(v_aig_190_);
lean_dec(v_res_189_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_aig_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_q_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_r_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg___boxed(lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_w_202_, lean_object* v_aig_203_, lean_object* v_curr_204_, lean_object* v_n_205_, lean_object* v_d_206_, lean_object* v_wn_207_, lean_object* v_wr_208_, lean_object* v_q_209_, lean_object* v_r_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_200_, v_inst_201_, v_w_202_, v_aig_203_, v_curr_204_, v_n_205_, v_d_206_, v_wn_207_, v_wr_208_, v_q_209_, v_r_210_);
lean_dec(v_wr_208_);
lean_dec(v_wn_207_);
lean_dec_ref(v_n_205_);
lean_dec(v_curr_204_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_w_215_, lean_object* v_aig_216_, lean_object* v_curr_217_, lean_object* v_n_218_, lean_object* v_d_219_, lean_object* v_wn_220_, lean_object* v_wr_221_, lean_object* v_q_222_, lean_object* v_r_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_213_, v_inst_214_, v_w_215_, v_aig_216_, v_curr_217_, v_n_218_, v_d_219_, v_wn_220_, v_wr_221_, v_q_222_, v_r_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___boxed(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_w_228_, lean_object* v_aig_229_, lean_object* v_curr_230_, lean_object* v_n_231_, lean_object* v_d_232_, lean_object* v_wn_233_, lean_object* v_wr_234_, lean_object* v_q_235_, lean_object* v_r_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(v_00_u03b1_225_, v_inst_226_, v_inst_227_, v_w_228_, v_aig_229_, v_curr_230_, v_n_231_, v_d_232_, v_wn_233_, v_wr_234_, v_q_235_, v_r_236_);
lean_dec(v_wr_234_);
lean_dec(v_wn_233_);
lean_dec_ref(v_n_231_);
lean_dec(v_curr_230_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(lean_object* v_curr_238_, lean_object* v_h__1_239_, lean_object* v_h__2_240_){
_start:
{
lean_object* v_zero_241_; uint8_t v_isZero_242_; 
v_zero_241_ = lean_unsigned_to_nat(0u);
v_isZero_242_ = lean_nat_dec_eq(v_curr_238_, v_zero_241_);
if (v_isZero_242_ == 1)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v_h__2_240_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_apply_1(v_h__1_239_, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v_one_245_; lean_object* v_n_246_; lean_object* v___x_247_; 
lean_dec(v_h__1_239_);
v_one_245_ = lean_unsigned_to_nat(1u);
v_n_246_ = lean_nat_sub(v_curr_238_, v_one_245_);
v___x_247_ = lean_apply_1(v_h__2_240_, v_n_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(lean_object* v_curr_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(v_curr_248_, v_h__1_249_, v_h__2_250_);
lean_dec(v_curr_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object* v_motive_252_, lean_object* v_curr_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_){
_start:
{
lean_object* v_zero_256_; uint8_t v_isZero_257_; 
v_zero_256_ = lean_unsigned_to_nat(0u);
v_isZero_257_ = lean_nat_dec_eq(v_curr_253_, v_zero_256_);
if (v_isZero_257_ == 1)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_h__2_255_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_apply_1(v_h__1_254_, v___x_258_);
return v___x_259_;
}
else
{
lean_object* v_one_260_; lean_object* v_n_261_; lean_object* v___x_262_; 
lean_dec(v_h__1_254_);
v_one_260_ = lean_unsigned_to_nat(1u);
v_n_261_ = lean_nat_sub(v_curr_253_, v_one_260_);
v___x_262_ = lean_apply_1(v_h__2_255_, v_n_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(lean_object* v_motive_263_, lean_object* v_curr_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(v_motive_263_, v_curr_264_, v_h__1_265_, v_h__2_266_);
lean_dec(v_curr_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_w_270_, lean_object* v_aig_271_, lean_object* v_input_272_){
_start:
{
lean_object* v_lhs_273_; lean_object* v_rhs_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_308_; 
v_lhs_273_ = lean_ctor_get(v_input_272_, 0);
v_rhs_274_ = lean_ctor_get(v_input_272_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_input_272_);
if (v_isSharedCheck_308_ == 0)
{
v___x_276_ = v_input_272_;
v_isShared_277_ = v_isSharedCheck_308_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_rhs_274_);
lean_inc(v_lhs_273_);
lean_dec(v_input_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_308_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_zero_280_; lean_object* v___x_282_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = l_BitVec_ofNat(v_w_270_, v___x_278_);
v_zero_280_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_270_, v___x_279_);
lean_dec(v___x_279_);
lean_inc_ref(v_zero_280_);
lean_inc_ref(v_rhs_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v_zero_280_);
lean_ctor_set(v___x_276_, 0, v_rhs_274_);
v___x_282_ = v___x_276_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_rhs_274_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_zero_280_);
v___x_282_ = v_reuseFailAlloc_307_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v_res_283_; lean_object* v_aig_284_; lean_object* v_ref_285_; lean_object* v_res_286_; lean_object* v_aig_287_; lean_object* v_q_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_305_; 
lean_inc_ref(v_inst_269_);
lean_inc_ref(v_inst_268_);
v_res_283_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(v_inst_268_, v_inst_269_, v_w_270_, v_aig_271_, v___x_282_);
lean_dec_ref(v___x_282_);
v_aig_284_ = lean_ctor_get(v_res_283_, 0);
lean_inc_ref(v_aig_284_);
v_ref_285_ = lean_ctor_get(v_res_283_, 1);
lean_inc_ref(v_ref_285_);
lean_dec_ref(v_res_283_);
lean_inc_ref_n(v_zero_280_, 2);
lean_inc(v_w_270_);
lean_inc_ref(v_inst_269_);
lean_inc_ref(v_inst_268_);
v_res_286_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(v_inst_268_, v_inst_269_, v_w_270_, v_aig_284_, v_w_270_, v_lhs_273_, v_rhs_274_, v_w_270_, v___x_278_, v_zero_280_, v_zero_280_);
lean_dec_ref(v_lhs_273_);
v_aig_287_ = lean_ctor_get(v_res_286_, 0);
v_q_288_ = lean_ctor_get(v_res_286_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_res_286_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_res_286_, 2);
lean_dec(v_unused_306_);
v___x_290_ = v_res_286_;
v_isShared_291_ = v_isSharedCheck_305_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_q_288_);
lean_inc(v_aig_287_);
lean_dec(v_res_286_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_305_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_gate_292_; uint8_t v_invert_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_304_; 
v_gate_292_ = lean_ctor_get(v_ref_285_, 0);
v_invert_293_ = lean_ctor_get_uint8(v_ref_285_, sizeof(void*)*1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_ref_285_);
if (v_isSharedCheck_304_ == 0)
{
v___x_295_ = v_ref_285_;
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_gate_292_);
lean_dec(v_ref_285_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_discr_298_; 
if (v_isShared_296_ == 0)
{
v_discr_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_gate_292_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*1, v_invert_293_);
v_discr_298_ = v_reuseFailAlloc_303_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 2, v_q_288_);
lean_ctor_set(v___x_290_, 1, v_zero_280_);
lean_ctor_set(v___x_290_, 0, v_discr_298_);
v___x_300_ = v___x_290_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_discr_298_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_zero_280_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_q_288_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_268_, v_inst_269_, v_w_270_, v_aig_287_, v___x_300_);
lean_dec(v_w_270_);
return v___x_301_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_w_312_, lean_object* v_aig_313_, lean_object* v_input_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(v_inst_310_, v_inst_311_, v_w_312_, v_aig_313_, v_input_314_);
return v___x_315_;
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
