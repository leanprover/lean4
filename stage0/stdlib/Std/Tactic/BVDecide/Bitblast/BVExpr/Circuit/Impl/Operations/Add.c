// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(lean_object* v_val_1_){
_start:
{
lean_object* v_lhs_2_; lean_object* v_rhs_3_; lean_object* v_cin_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_38_; 
v_lhs_2_ = lean_ctor_get(v_val_1_, 0);
v_rhs_3_ = lean_ctor_get(v_val_1_, 1);
v_cin_4_ = lean_ctor_get(v_val_1_, 2);
v_isSharedCheck_38_ = !lean_is_exclusive(v_val_1_);
if (v_isSharedCheck_38_ == 0)
{
v___x_6_ = v_val_1_;
v_isShared_7_ = v_isSharedCheck_38_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_cin_4_);
lean_inc(v_rhs_3_);
lean_inc(v_lhs_2_);
lean_dec(v_val_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_38_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v_gate_8_; uint8_t v_invert_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_37_; 
v_gate_8_ = lean_ctor_get(v_lhs_2_, 0);
v_invert_9_ = lean_ctor_get_uint8(v_lhs_2_, sizeof(void*)*1);
v_isSharedCheck_37_ = !lean_is_exclusive(v_lhs_2_);
if (v_isSharedCheck_37_ == 0)
{
v___x_11_ = v_lhs_2_;
v_isShared_12_ = v_isSharedCheck_37_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_gate_8_);
lean_dec(v_lhs_2_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_37_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v_gate_13_; uint8_t v_invert_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_36_; 
v_gate_13_ = lean_ctor_get(v_rhs_3_, 0);
v_invert_14_ = lean_ctor_get_uint8(v_rhs_3_, sizeof(void*)*1);
v_isSharedCheck_36_ = !lean_is_exclusive(v_rhs_3_);
if (v_isSharedCheck_36_ == 0)
{
v___x_16_ = v_rhs_3_;
v_isShared_17_ = v_isSharedCheck_36_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_gate_13_);
lean_dec(v_rhs_3_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_36_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_gate_18_; uint8_t v_invert_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_35_; 
v_gate_18_ = lean_ctor_get(v_cin_4_, 0);
v_invert_19_ = lean_ctor_get_uint8(v_cin_4_, sizeof(void*)*1);
v_isSharedCheck_35_ = !lean_is_exclusive(v_cin_4_);
if (v_isSharedCheck_35_ == 0)
{
v___x_21_ = v_cin_4_;
v_isShared_22_ = v_isSharedCheck_35_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_gate_18_);
lean_dec(v_cin_4_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_35_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v_gate_8_);
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_gate_8_);
v___x_24_ = v_reuseFailAlloc_34_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_26_; 
lean_ctor_set_uint8(v___x_24_, sizeof(void*)*1, v_invert_9_);
if (v_isShared_17_ == 0)
{
v___x_26_ = v___x_16_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_gate_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_33_, sizeof(void*)*1, v_invert_14_);
v___x_26_ = v_reuseFailAlloc_33_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_28_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 0, v_gate_18_);
v___x_28_ = v___x_11_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_gate_18_);
v___x_28_ = v_reuseFailAlloc_32_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_30_; 
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*1, v_invert_19_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 2, v___x_28_);
lean_ctor_set(v___x_6_, 1, v___x_26_);
lean_ctor_set(v___x_6_, 0, v___x_24_);
v___x_30_ = v___x_6_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_aig1_42_, lean_object* v_aig2_43_, lean_object* v_val_44_, lean_object* v_h_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(v_val_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_aig1_50_, lean_object* v_aig2_51_, lean_object* v_val_52_, lean_object* v_h_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(v_00_u03b1_47_, v_inst_48_, v_inst_49_, v_aig1_50_, v_aig2_51_, v_val_52_, v_h_53_);
lean_dec_ref(v_aig2_51_);
lean_dec_ref(v_aig1_50_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_aig_57_, lean_object* v_input_58_){
_start:
{
lean_object* v_lhs_59_; lean_object* v_rhs_60_; lean_object* v_cin_61_; lean_object* v___x_62_; lean_object* v_res_63_; lean_object* v_aig_64_; lean_object* v_ref_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_82_; 
v_lhs_59_ = lean_ctor_get(v_input_58_, 0);
lean_inc_ref(v_lhs_59_);
v_rhs_60_ = lean_ctor_get(v_input_58_, 1);
lean_inc_ref(v_rhs_60_);
v_cin_61_ = lean_ctor_get(v_input_58_, 2);
lean_inc_ref(v_cin_61_);
lean_dec_ref(v_input_58_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_lhs_59_);
lean_ctor_set(v___x_62_, 1, v_rhs_60_);
lean_inc_ref(v_inst_56_);
lean_inc_ref(v_inst_55_);
v_res_63_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_55_, v_inst_56_, v_aig_57_, v___x_62_);
v_aig_64_ = lean_ctor_get(v_res_63_, 0);
v_ref_65_ = lean_ctor_get(v_res_63_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_res_63_);
if (v_isSharedCheck_82_ == 0)
{
v___x_67_ = v_res_63_;
v_isShared_68_ = v_isSharedCheck_82_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_ref_65_);
lean_inc(v_aig_64_);
lean_dec(v_res_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_82_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v_gate_69_; uint8_t v_invert_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_81_; 
v_gate_69_ = lean_ctor_get(v_cin_61_, 0);
v_invert_70_ = lean_ctor_get_uint8(v_cin_61_, sizeof(void*)*1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_cin_61_);
if (v_isSharedCheck_81_ == 0)
{
v___x_72_ = v_cin_61_;
v_isShared_73_ = v_isSharedCheck_81_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_gate_69_);
lean_dec(v_cin_61_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_81_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_cin_75_; 
if (v_isShared_73_ == 0)
{
v_cin_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_gate_69_);
lean_ctor_set_uint8(v_reuseFailAlloc_80_, sizeof(void*)*1, v_invert_70_);
v_cin_75_ = v_reuseFailAlloc_80_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_77_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v_cin_75_);
lean_ctor_set(v___x_67_, 0, v_ref_65_);
v___x_77_ = v___x_67_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_ref_65_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_cin_75_);
v___x_77_ = v_reuseFailAlloc_79_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_55_, v_inst_56_, v_aig_64_, v___x_77_);
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_aig_86_, lean_object* v_input_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(v_inst_84_, v_inst_85_, v_aig_86_, v_input_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_aig_91_, lean_object* v_input_92_){
_start:
{
lean_object* v_lhs_93_; lean_object* v_rhs_94_; lean_object* v_cin_95_; lean_object* v___x_96_; lean_object* v_res_97_; lean_object* v_aig_98_; lean_object* v_ref_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_163_; 
v_lhs_93_ = lean_ctor_get(v_input_92_, 0);
lean_inc_ref_n(v_lhs_93_, 2);
v_rhs_94_ = lean_ctor_get(v_input_92_, 1);
lean_inc_ref_n(v_rhs_94_, 2);
v_cin_95_ = lean_ctor_get(v_input_92_, 2);
lean_inc_ref(v_cin_95_);
lean_dec_ref(v_input_92_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_lhs_93_);
lean_ctor_set(v___x_96_, 1, v_rhs_94_);
lean_inc_ref(v_inst_90_);
lean_inc_ref(v_inst_89_);
v_res_97_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_89_, v_inst_90_, v_aig_91_, v___x_96_);
v_aig_98_ = lean_ctor_get(v_res_97_, 0);
v_ref_99_ = lean_ctor_get(v_res_97_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_res_97_);
if (v_isSharedCheck_163_ == 0)
{
v___x_101_ = v_res_97_;
v_isShared_102_ = v_isSharedCheck_163_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_ref_99_);
lean_inc(v_aig_98_);
lean_dec(v_res_97_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_163_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_gate_103_; uint8_t v_invert_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_162_; 
v_gate_103_ = lean_ctor_get(v_lhs_93_, 0);
v_invert_104_ = lean_ctor_get_uint8(v_lhs_93_, sizeof(void*)*1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_lhs_93_);
if (v_isSharedCheck_162_ == 0)
{
v___x_106_ = v_lhs_93_;
v_isShared_107_ = v_isSharedCheck_162_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_gate_103_);
lean_dec(v_lhs_93_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_162_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_gate_108_; uint8_t v_invert_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_161_; 
v_gate_108_ = lean_ctor_get(v_rhs_94_, 0);
v_invert_109_ = lean_ctor_get_uint8(v_rhs_94_, sizeof(void*)*1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_rhs_94_);
if (v_isSharedCheck_161_ == 0)
{
v___x_111_ = v_rhs_94_;
v_isShared_112_ = v_isSharedCheck_161_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_gate_108_);
lean_dec(v_rhs_94_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_161_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_gate_113_; uint8_t v_invert_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_160_; 
v_gate_113_ = lean_ctor_get(v_cin_95_, 0);
v_invert_114_ = lean_ctor_get_uint8(v_cin_95_, sizeof(void*)*1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_cin_95_);
if (v_isSharedCheck_160_ == 0)
{
v___x_116_ = v_cin_95_;
v_isShared_117_ = v_isSharedCheck_160_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_gate_113_);
lean_dec(v_cin_95_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_160_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_cin_119_; 
if (v_isShared_117_ == 0)
{
v_cin_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_gate_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_159_, sizeof(void*)*1, v_invert_114_);
v_cin_119_ = v_reuseFailAlloc_159_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_cin_119_);
lean_ctor_set(v___x_101_, 0, v_ref_99_);
v___x_121_ = v___x_101_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_ref_99_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_cin_119_);
v___x_121_ = v_reuseFailAlloc_158_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v_res_122_; lean_object* v_aig_123_; lean_object* v_ref_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_157_; 
lean_inc_ref(v_inst_90_);
lean_inc_ref(v_inst_89_);
v_res_122_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_89_, v_inst_90_, v_aig_98_, v___x_121_);
v_aig_123_ = lean_ctor_get(v_res_122_, 0);
v_ref_124_ = lean_ctor_get(v_res_122_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_res_122_);
if (v_isSharedCheck_157_ == 0)
{
v___x_126_ = v_res_122_;
v_isShared_127_ = v_isSharedCheck_157_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_ref_124_);
lean_inc(v_aig_123_);
lean_dec(v_res_122_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_157_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_lhs_129_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v_gate_103_);
v_lhs_129_ = v___x_111_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_gate_103_);
v_lhs_129_ = v_reuseFailAlloc_156_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v_rhs_131_; 
lean_ctor_set_uint8(v_lhs_129_, sizeof(void*)*1, v_invert_104_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v_gate_108_);
v_rhs_131_ = v___x_106_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_gate_108_);
v_rhs_131_ = v_reuseFailAlloc_155_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_133_; 
lean_ctor_set_uint8(v_rhs_131_, sizeof(void*)*1, v_invert_109_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_rhs_131_);
lean_ctor_set(v___x_126_, 0, v_lhs_129_);
v___x_133_ = v___x_126_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_lhs_129_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_rhs_131_);
v___x_133_ = v_reuseFailAlloc_154_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v_res_134_; lean_object* v_aig_135_; lean_object* v_ref_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_153_; 
lean_inc_ref(v_inst_90_);
lean_inc_ref(v_inst_89_);
v_res_134_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_89_, v_inst_90_, v_aig_123_, v___x_133_);
v_aig_135_ = lean_ctor_get(v_res_134_, 0);
v_ref_136_ = lean_ctor_get(v_res_134_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_res_134_);
if (v_isSharedCheck_153_ == 0)
{
v___x_138_ = v_res_134_;
v_isShared_139_ = v_isSharedCheck_153_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_ref_136_);
lean_inc(v_aig_135_);
lean_dec(v_res_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_153_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v_gate_140_; uint8_t v_invert_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_152_; 
v_gate_140_ = lean_ctor_get(v_ref_124_, 0);
v_invert_141_ = lean_ctor_get_uint8(v_ref_124_, sizeof(void*)*1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_ref_124_);
if (v_isSharedCheck_152_ == 0)
{
v___x_143_ = v_ref_124_;
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_gate_140_);
lean_dec(v_ref_124_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_lorRef_146_; 
if (v_isShared_144_ == 0)
{
v_lorRef_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_gate_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_151_, sizeof(void*)*1, v_invert_141_);
v_lorRef_146_ = v_reuseFailAlloc_151_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v_lorRef_146_);
v___x_148_ = v___x_138_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_lorRef_146_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_ref_136_);
v___x_148_ = v_reuseFailAlloc_150_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_89_, v_inst_90_, v_aig_135_, v___x_148_);
return v___x_149_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object* v_00_u03b1_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_aig_167_, lean_object* v_input_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_165_, v_inst_166_, v_aig_167_, v_input_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_aig_172_, lean_object* v_input_173_){
_start:
{
lean_object* v_res_174_; lean_object* v_aig_175_; lean_object* v_ref_176_; lean_object* v_input_177_; lean_object* v_res_178_; lean_object* v_aig_179_; lean_object* v_ref_180_; lean_object* v_gate_181_; uint8_t v_invert_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
lean_inc_ref(v_input_173_);
lean_inc_ref(v_inst_171_);
lean_inc_ref(v_inst_170_);
v_res_174_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(v_inst_170_, v_inst_171_, v_aig_172_, v_input_173_);
v_aig_175_ = lean_ctor_get(v_res_174_, 0);
lean_inc_ref(v_aig_175_);
v_ref_176_ = lean_ctor_get(v_res_174_, 1);
lean_inc_ref(v_ref_176_);
lean_dec_ref(v_res_174_);
v_input_177_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(v_input_173_);
v_res_178_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_170_, v_inst_171_, v_aig_175_, v_input_177_);
v_aig_179_ = lean_ctor_get(v_res_178_, 0);
lean_inc_ref(v_aig_179_);
v_ref_180_ = lean_ctor_get(v_res_178_, 1);
lean_inc_ref(v_ref_180_);
lean_dec_ref(v_res_178_);
v_gate_181_ = lean_ctor_get(v_ref_176_, 0);
v_invert_182_ = lean_ctor_get_uint8(v_ref_176_, sizeof(void*)*1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_ref_176_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v_ref_176_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_gate_181_);
lean_dec(v_ref_176_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_outRef_187_; 
if (v_isShared_185_ == 0)
{
v_outRef_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_gate_181_);
lean_ctor_set_uint8(v_reuseFailAlloc_189_, sizeof(void*)*1, v_invert_182_);
v_outRef_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v_aig_179_);
lean_ctor_set(v___x_188_, 1, v_outRef_187_);
lean_ctor_set(v___x_188_, 2, v_ref_180_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object* v_00_u03b1_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_aig_194_, lean_object* v_input_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(v_inst_192_, v_inst_193_, v_aig_194_, v_input_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_w_199_, lean_object* v_aig_200_, lean_object* v_lhs_201_, lean_object* v_rhs_202_, lean_object* v_curr_203_, lean_object* v_cin_204_, lean_object* v_s_205_){
_start:
{
lean_object* v___y_207_; lean_object* v___y_208_; uint8_t v___x_224_; lean_object* v___y_226_; 
v___x_224_ = lean_nat_dec_lt(v_curr_203_, v_w_199_);
if (v___x_224_ == 0)
{
lean_object* v___x_236_; 
lean_dec_ref(v_cin_204_);
lean_dec(v_curr_203_);
lean_dec_ref(v_inst_198_);
lean_dec_ref(v_inst_197_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_aig_200_);
lean_ctor_set(v___x_236_, 1, v_s_205_);
return v___x_236_;
}
else
{
lean_object* v_ref_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_ref_237_ = lean_array_fget_borrowed(v_lhs_201_, v_curr_203_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_shiftr(v_ref_237_, v___x_238_);
v___x_240_ = lean_nat_land(v___x_238_, v_ref_237_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_nat_dec_eq(v___x_240_, v___x_241_);
lean_dec(v___x_240_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_239_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_224_);
v___y_226_ = v___x_243_;
goto v___jp_225_;
}
else
{
uint8_t v___x_244_; lean_object* v___x_245_; 
v___x_244_ = 0;
v___x_245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_239_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_244_);
v___y_226_ = v___x_245_;
goto v___jp_225_;
}
}
v___jp_206_:
{
lean_object* v___x_209_; lean_object* v_res_210_; lean_object* v_out_211_; lean_object* v_aig_212_; lean_object* v_cout_213_; lean_object* v_gate_214_; uint8_t v_invert_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_s_222_; 
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v___y_207_);
lean_ctor_set(v___x_209_, 1, v___y_208_);
lean_ctor_set(v___x_209_, 2, v_cin_204_);
lean_inc_ref(v_inst_198_);
lean_inc_ref(v_inst_197_);
v_res_210_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(v_inst_197_, v_inst_198_, v_aig_200_, v___x_209_);
v_out_211_ = lean_ctor_get(v_res_210_, 1);
lean_inc_ref(v_out_211_);
v_aig_212_ = lean_ctor_get(v_res_210_, 0);
lean_inc_ref(v_aig_212_);
v_cout_213_ = lean_ctor_get(v_res_210_, 2);
lean_inc_ref(v_cout_213_);
lean_dec_ref(v_res_210_);
v_gate_214_ = lean_ctor_get(v_out_211_, 0);
lean_inc(v_gate_214_);
v_invert_215_ = lean_ctor_get_uint8(v_out_211_, sizeof(void*)*1);
lean_dec_ref(v_out_211_);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_curr_203_, v___x_216_);
lean_dec(v_curr_203_);
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_nat_mul(v_gate_214_, v___x_218_);
lean_dec(v_gate_214_);
v___x_220_ = l_Bool_toNat(v_invert_215_);
v___x_221_ = lean_nat_lor(v___x_219_, v___x_220_);
lean_dec(v___x_220_);
lean_dec(v___x_219_);
v_s_222_ = lean_array_push(v_s_205_, v___x_221_);
v_aig_200_ = v_aig_212_;
v_curr_203_ = v___x_217_;
v_cin_204_ = v_cout_213_;
v_s_205_ = v_s_222_;
goto _start;
}
v___jp_225_:
{
lean_object* v_ref_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_ref_227_ = lean_array_fget_borrowed(v_rhs_202_, v_curr_203_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_shiftr(v_ref_227_, v___x_228_);
v___x_230_ = lean_nat_land(v___x_228_, v_ref_227_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_dec_eq(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_224_);
v___y_207_ = v___y_226_;
v___y_208_ = v___x_233_;
goto v___jp_206_;
}
else
{
uint8_t v___x_234_; lean_object* v___x_235_; 
v___x_234_ = 0;
v___x_235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_235_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v___x_234_);
v___y_207_ = v___y_226_;
v___y_208_ = v___x_235_;
goto v___jp_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_w_248_, lean_object* v_aig_249_, lean_object* v_lhs_250_, lean_object* v_rhs_251_, lean_object* v_curr_252_, lean_object* v_cin_253_, lean_object* v_s_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_246_, v_inst_247_, v_w_248_, v_aig_249_, v_lhs_250_, v_rhs_251_, v_curr_252_, v_cin_253_, v_s_254_);
lean_dec_ref(v_rhs_251_);
lean_dec_ref(v_lhs_250_);
lean_dec(v_w_248_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object* v_00_u03b1_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_w_259_, lean_object* v_aig_260_, lean_object* v_lhs_261_, lean_object* v_rhs_262_, lean_object* v_curr_263_, lean_object* v_hcurr_264_, lean_object* v_cin_265_, lean_object* v_s_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_257_, v_inst_258_, v_w_259_, v_aig_260_, v_lhs_261_, v_rhs_262_, v_curr_263_, v_cin_265_, v_s_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object* v_00_u03b1_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_w_271_, lean_object* v_aig_272_, lean_object* v_lhs_273_, lean_object* v_rhs_274_, lean_object* v_curr_275_, lean_object* v_hcurr_276_, lean_object* v_cin_277_, lean_object* v_s_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(v_00_u03b1_268_, v_inst_269_, v_inst_270_, v_w_271_, v_aig_272_, v_lhs_273_, v_rhs_274_, v_curr_275_, v_hcurr_276_, v_cin_277_, v_s_278_);
lean_dec_ref(v_rhs_274_);
lean_dec_ref(v_lhs_273_);
lean_dec(v_w_271_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_w_285_, lean_object* v_aig_286_, lean_object* v_input_287_){
_start:
{
lean_object* v_lhs_288_; lean_object* v_rhs_289_; lean_object* v___x_290_; lean_object* v_cin_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_lhs_288_ = lean_ctor_get(v_input_287_, 0);
v_rhs_289_ = lean_ctor_get(v_input_287_, 1);
v___x_290_ = lean_unsigned_to_nat(0u);
v_cin_291_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0));
v___x_292_ = lean_mk_empty_array_with_capacity(v_w_285_);
v___x_293_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_283_, v_inst_284_, v_w_285_, v_aig_286_, v_lhs_288_, v_rhs_289_, v___x_290_, v_cin_291_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_w_296_, lean_object* v_aig_297_, lean_object* v_input_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_294_, v_inst_295_, v_w_296_, v_aig_297_, v_input_298_);
lean_dec_ref(v_input_298_);
lean_dec(v_w_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_w_303_, lean_object* v_aig_304_, lean_object* v_input_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_301_, v_inst_302_, v_w_303_, v_aig_304_, v_input_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_w_310_, lean_object* v_aig_311_, lean_object* v_input_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(v_00_u03b1_307_, v_inst_308_, v_inst_309_, v_w_310_, v_aig_311_, v_input_312_);
lean_dec_ref(v_input_312_);
lean_dec(v_w_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_w_316_, lean_object* v_aig_317_, lean_object* v_input_318_){
_start:
{
lean_object* v_lhs_319_; lean_object* v_rhs_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_lhs_319_ = lean_ctor_get(v_input_318_, 0);
v_rhs_320_ = lean_ctor_get(v_input_318_, 1);
v___x_321_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_316_, v_aig_317_, v_lhs_319_);
v___x_322_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_316_, v_aig_317_, v_rhs_320_);
v___x_323_ = lean_nat_dec_lt(v___x_321_, v___x_322_);
lean_dec(v___x_322_);
lean_dec(v___x_321_);
if (v___x_323_ == 0)
{
lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
lean_inc_ref(v_rhs_320_);
lean_inc_ref(v_lhs_319_);
v_isSharedCheck_331_ = !lean_is_exclusive(v_input_318_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; lean_object* v_unused_333_; 
v_unused_332_ = lean_ctor_get(v_input_318_, 1);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_input_318_, 0);
lean_dec(v_unused_333_);
v___x_325_ = v_input_318_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_dec(v_input_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_lhs_319_);
lean_ctor_set(v___x_325_, 0, v_rhs_320_);
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_rhs_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_lhs_319_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_314_, v_inst_315_, v_w_316_, v_aig_317_, v___x_328_);
lean_dec_ref(v___x_328_);
return v___x_329_;
}
}
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_314_, v_inst_315_, v_w_316_, v_aig_317_, v_input_318_);
lean_dec_ref(v_input_318_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_w_337_, lean_object* v_aig_338_, lean_object* v_input_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_335_, v_inst_336_, v_w_337_, v_aig_338_, v_input_339_);
lean_dec(v_w_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object* v_00_u03b1_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_w_344_, lean_object* v_aig_345_, lean_object* v_input_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_342_, v_inst_343_, v_w_344_, v_aig_345_, v_input_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object* v_00_u03b1_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_w_351_, lean_object* v_aig_352_, lean_object* v_input_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(v_00_u03b1_348_, v_inst_349_, v_inst_350_, v_w_351_, v_aig_352_, v_input_353_);
lean_dec(v_w_351_);
return v_res_354_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
}
#ifdef __cplusplus
}
#endif
