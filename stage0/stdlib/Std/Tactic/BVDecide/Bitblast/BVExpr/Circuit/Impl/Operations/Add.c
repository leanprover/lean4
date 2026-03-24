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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(lean_object* v_val_55_, lean_object* v_h__1_56_){
_start:
{
lean_object* v_lhs_57_; lean_object* v_rhs_58_; lean_object* v_cin_59_; lean_object* v___x_60_; 
v_lhs_57_ = lean_ctor_get(v_val_55_, 0);
lean_inc_ref(v_lhs_57_);
v_rhs_58_ = lean_ctor_get(v_val_55_, 1);
lean_inc_ref(v_rhs_58_);
v_cin_59_ = lean_ctor_get(v_val_55_, 2);
lean_inc_ref(v_cin_59_);
lean_dec_ref(v_val_55_);
v___x_60_ = lean_apply_3(v_h__1_56_, v_lhs_57_, v_rhs_58_, v_cin_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_aig1_64_, lean_object* v_motive_65_, lean_object* v_val_66_, lean_object* v_h__1_67_){
_start:
{
lean_object* v_lhs_68_; lean_object* v_rhs_69_; lean_object* v_cin_70_; lean_object* v___x_71_; 
v_lhs_68_ = lean_ctor_get(v_val_66_, 0);
lean_inc_ref(v_lhs_68_);
v_rhs_69_ = lean_ctor_get(v_val_66_, 1);
lean_inc_ref(v_rhs_69_);
v_cin_70_ = lean_ctor_get(v_val_66_, 2);
lean_inc_ref(v_cin_70_);
lean_dec_ref(v_val_66_);
v___x_71_ = lean_apply_3(v_h__1_67_, v_lhs_68_, v_rhs_69_, v_cin_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(lean_object* v_00_u03b1_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_aig1_75_, lean_object* v_motive_76_, lean_object* v_val_77_, lean_object* v_h__1_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(v_00_u03b1_72_, v_inst_73_, v_inst_74_, v_aig1_75_, v_motive_76_, v_val_77_, v_h__1_78_);
lean_dec_ref(v_aig1_75_);
lean_dec_ref(v_inst_74_);
lean_dec_ref(v_inst_73_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_aig_82_, lean_object* v_input_83_){
_start:
{
lean_object* v_lhs_84_; lean_object* v_rhs_85_; lean_object* v_cin_86_; lean_object* v___x_87_; lean_object* v_res_88_; lean_object* v_aig_89_; lean_object* v_ref_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_107_; 
v_lhs_84_ = lean_ctor_get(v_input_83_, 0);
lean_inc_ref(v_lhs_84_);
v_rhs_85_ = lean_ctor_get(v_input_83_, 1);
lean_inc_ref(v_rhs_85_);
v_cin_86_ = lean_ctor_get(v_input_83_, 2);
lean_inc_ref(v_cin_86_);
lean_dec_ref(v_input_83_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v_lhs_84_);
lean_ctor_set(v___x_87_, 1, v_rhs_85_);
lean_inc_ref(v_inst_81_);
lean_inc_ref(v_inst_80_);
v_res_88_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_80_, v_inst_81_, v_aig_82_, v___x_87_);
v_aig_89_ = lean_ctor_get(v_res_88_, 0);
v_ref_90_ = lean_ctor_get(v_res_88_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_res_88_);
if (v_isSharedCheck_107_ == 0)
{
v___x_92_ = v_res_88_;
v_isShared_93_ = v_isSharedCheck_107_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_ref_90_);
lean_inc(v_aig_89_);
lean_dec(v_res_88_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_107_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v_gate_94_; uint8_t v_invert_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_106_; 
v_gate_94_ = lean_ctor_get(v_cin_86_, 0);
v_invert_95_ = lean_ctor_get_uint8(v_cin_86_, sizeof(void*)*1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_cin_86_);
if (v_isSharedCheck_106_ == 0)
{
v___x_97_ = v_cin_86_;
v_isShared_98_ = v_isSharedCheck_106_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_gate_94_);
lean_dec(v_cin_86_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_106_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v_cin_100_; 
if (v_isShared_98_ == 0)
{
v_cin_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_gate_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_105_, sizeof(void*)*1, v_invert_95_);
v_cin_100_ = v_reuseFailAlloc_105_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v_cin_100_);
lean_ctor_set(v___x_92_, 0, v_ref_90_);
v___x_102_ = v___x_92_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_ref_90_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_cin_100_);
v___x_102_ = v_reuseFailAlloc_104_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_80_, v_inst_81_, v_aig_89_, v___x_102_);
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object* v_00_u03b1_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_aig_111_, lean_object* v_input_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(v_inst_109_, v_inst_110_, v_aig_111_, v_input_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_aig_116_, lean_object* v_input_117_){
_start:
{
lean_object* v_lhs_118_; lean_object* v_rhs_119_; lean_object* v_cin_120_; lean_object* v___x_121_; lean_object* v_res_122_; lean_object* v_aig_123_; lean_object* v_ref_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_188_; 
v_lhs_118_ = lean_ctor_get(v_input_117_, 0);
lean_inc_ref(v_lhs_118_);
v_rhs_119_ = lean_ctor_get(v_input_117_, 1);
lean_inc_ref(v_rhs_119_);
v_cin_120_ = lean_ctor_get(v_input_117_, 2);
lean_inc_ref(v_cin_120_);
lean_dec_ref(v_input_117_);
lean_inc_ref(v_rhs_119_);
lean_inc_ref(v_lhs_118_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_lhs_118_);
lean_ctor_set(v___x_121_, 1, v_rhs_119_);
lean_inc_ref(v_inst_115_);
lean_inc_ref(v_inst_114_);
v_res_122_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_114_, v_inst_115_, v_aig_116_, v___x_121_);
v_aig_123_ = lean_ctor_get(v_res_122_, 0);
v_ref_124_ = lean_ctor_get(v_res_122_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_res_122_);
if (v_isSharedCheck_188_ == 0)
{
v___x_126_ = v_res_122_;
v_isShared_127_ = v_isSharedCheck_188_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_ref_124_);
lean_inc(v_aig_123_);
lean_dec(v_res_122_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_188_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_gate_128_; uint8_t v_invert_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_187_; 
v_gate_128_ = lean_ctor_get(v_lhs_118_, 0);
v_invert_129_ = lean_ctor_get_uint8(v_lhs_118_, sizeof(void*)*1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_lhs_118_);
if (v_isSharedCheck_187_ == 0)
{
v___x_131_ = v_lhs_118_;
v_isShared_132_ = v_isSharedCheck_187_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_gate_128_);
lean_dec(v_lhs_118_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_187_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_gate_133_; uint8_t v_invert_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_186_; 
v_gate_133_ = lean_ctor_get(v_rhs_119_, 0);
v_invert_134_ = lean_ctor_get_uint8(v_rhs_119_, sizeof(void*)*1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_rhs_119_);
if (v_isSharedCheck_186_ == 0)
{
v___x_136_ = v_rhs_119_;
v_isShared_137_ = v_isSharedCheck_186_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_gate_133_);
lean_dec(v_rhs_119_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_186_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_gate_138_; uint8_t v_invert_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_185_; 
v_gate_138_ = lean_ctor_get(v_cin_120_, 0);
v_invert_139_ = lean_ctor_get_uint8(v_cin_120_, sizeof(void*)*1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_cin_120_);
if (v_isSharedCheck_185_ == 0)
{
v___x_141_ = v_cin_120_;
v_isShared_142_ = v_isSharedCheck_185_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_gate_138_);
lean_dec(v_cin_120_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_185_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_cin_144_; 
if (v_isShared_142_ == 0)
{
v_cin_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_gate_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*1, v_invert_139_);
v_cin_144_ = v_reuseFailAlloc_184_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_cin_144_);
lean_ctor_set(v___x_126_, 0, v_ref_124_);
v___x_146_ = v___x_126_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_ref_124_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_cin_144_);
v___x_146_ = v_reuseFailAlloc_183_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v_res_147_; lean_object* v_aig_148_; lean_object* v_ref_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_182_; 
lean_inc_ref(v_inst_115_);
lean_inc_ref(v_inst_114_);
v_res_147_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_114_, v_inst_115_, v_aig_123_, v___x_146_);
v_aig_148_ = lean_ctor_get(v_res_147_, 0);
v_ref_149_ = lean_ctor_get(v_res_147_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_res_147_);
if (v_isSharedCheck_182_ == 0)
{
v___x_151_ = v_res_147_;
v_isShared_152_ = v_isSharedCheck_182_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_ref_149_);
lean_inc(v_aig_148_);
lean_dec(v_res_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_182_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_lhs_154_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v_gate_128_);
v_lhs_154_ = v___x_136_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_gate_128_);
v_lhs_154_ = v_reuseFailAlloc_181_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v_rhs_156_; 
lean_ctor_set_uint8(v_lhs_154_, sizeof(void*)*1, v_invert_129_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v_gate_133_);
v_rhs_156_ = v___x_131_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_gate_133_);
v_rhs_156_ = v_reuseFailAlloc_180_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_158_; 
lean_ctor_set_uint8(v_rhs_156_, sizeof(void*)*1, v_invert_134_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_rhs_156_);
lean_ctor_set(v___x_151_, 0, v_lhs_154_);
v___x_158_ = v___x_151_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_lhs_154_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_rhs_156_);
v___x_158_ = v_reuseFailAlloc_179_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v_res_159_; lean_object* v_aig_160_; lean_object* v_ref_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_178_; 
lean_inc_ref(v_inst_115_);
lean_inc_ref(v_inst_114_);
v_res_159_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_114_, v_inst_115_, v_aig_148_, v___x_158_);
v_aig_160_ = lean_ctor_get(v_res_159_, 0);
v_ref_161_ = lean_ctor_get(v_res_159_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_res_159_);
if (v_isSharedCheck_178_ == 0)
{
v___x_163_ = v_res_159_;
v_isShared_164_ = v_isSharedCheck_178_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_ref_161_);
lean_inc(v_aig_160_);
lean_dec(v_res_159_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_178_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_gate_165_; uint8_t v_invert_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_177_; 
v_gate_165_ = lean_ctor_get(v_ref_149_, 0);
v_invert_166_ = lean_ctor_get_uint8(v_ref_149_, sizeof(void*)*1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_ref_149_);
if (v_isSharedCheck_177_ == 0)
{
v___x_168_ = v_ref_149_;
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_gate_165_);
lean_dec(v_ref_149_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_lorRef_171_; 
if (v_isShared_169_ == 0)
{
v_lorRef_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_gate_165_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, sizeof(void*)*1, v_invert_166_);
v_lorRef_171_ = v_reuseFailAlloc_176_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v_lorRef_171_);
v___x_173_ = v___x_163_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_lorRef_171_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_ref_161_);
v___x_173_ = v_reuseFailAlloc_175_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_114_, v_inst_115_, v_aig_160_, v___x_173_);
return v___x_174_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object* v_00_u03b1_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_aig_192_, lean_object* v_input_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_190_, v_inst_191_, v_aig_192_, v_input_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_aig_197_, lean_object* v_input_198_){
_start:
{
lean_object* v_res_199_; lean_object* v_aig_200_; lean_object* v_ref_201_; lean_object* v_input_202_; lean_object* v_res_203_; lean_object* v_aig_204_; lean_object* v_ref_205_; lean_object* v_gate_206_; uint8_t v_invert_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
lean_inc_ref(v_input_198_);
lean_inc_ref(v_inst_196_);
lean_inc_ref(v_inst_195_);
v_res_199_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(v_inst_195_, v_inst_196_, v_aig_197_, v_input_198_);
v_aig_200_ = lean_ctor_get(v_res_199_, 0);
lean_inc_ref(v_aig_200_);
v_ref_201_ = lean_ctor_get(v_res_199_, 1);
lean_inc_ref(v_ref_201_);
lean_dec_ref(v_res_199_);
v_input_202_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(v_input_198_);
v_res_203_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_195_, v_inst_196_, v_aig_200_, v_input_202_);
v_aig_204_ = lean_ctor_get(v_res_203_, 0);
lean_inc_ref(v_aig_204_);
v_ref_205_ = lean_ctor_get(v_res_203_, 1);
lean_inc_ref(v_ref_205_);
lean_dec_ref(v_res_203_);
v_gate_206_ = lean_ctor_get(v_ref_201_, 0);
v_invert_207_ = lean_ctor_get_uint8(v_ref_201_, sizeof(void*)*1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_ref_201_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v_ref_201_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_gate_206_);
lean_dec(v_ref_201_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_outRef_212_; 
if (v_isShared_210_ == 0)
{
v_outRef_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_gate_206_);
lean_ctor_set_uint8(v_reuseFailAlloc_214_, sizeof(void*)*1, v_invert_207_);
v_outRef_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v_aig_204_);
lean_ctor_set(v___x_213_, 1, v_outRef_212_);
lean_ctor_set(v___x_213_, 2, v_ref_205_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_aig_219_, lean_object* v_input_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(v_inst_217_, v_inst_218_, v_aig_219_, v_input_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_w_224_, lean_object* v_aig_225_, lean_object* v_lhs_226_, lean_object* v_rhs_227_, lean_object* v_curr_228_, lean_object* v_cin_229_, lean_object* v_s_230_){
_start:
{
lean_object* v___y_232_; lean_object* v___y_233_; uint8_t v___x_249_; lean_object* v___y_251_; 
v___x_249_ = lean_nat_dec_lt(v_curr_228_, v_w_224_);
if (v___x_249_ == 0)
{
lean_object* v___x_261_; 
lean_dec_ref(v_cin_229_);
lean_dec(v_curr_228_);
lean_dec_ref(v_inst_223_);
lean_dec_ref(v_inst_222_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_aig_225_);
lean_ctor_set(v___x_261_, 1, v_s_230_);
return v___x_261_;
}
else
{
lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_ref_262_ = lean_array_fget_borrowed(v_lhs_226_, v_curr_228_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_shiftr(v_ref_262_, v___x_263_);
v___x_265_ = lean_nat_land(v___x_263_, v_ref_262_);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_nat_dec_eq(v___x_265_, v___x_266_);
lean_dec(v___x_265_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_268_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_249_);
v___y_251_ = v___x_268_;
goto v___jp_250_;
}
else
{
uint8_t v___x_269_; lean_object* v___x_270_; 
v___x_269_ = 0;
v___x_270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_270_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_269_);
v___y_251_ = v___x_270_;
goto v___jp_250_;
}
}
v___jp_231_:
{
lean_object* v___x_234_; lean_object* v_res_235_; lean_object* v_out_236_; lean_object* v_aig_237_; lean_object* v_cout_238_; lean_object* v_gate_239_; uint8_t v_invert_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_s_247_; 
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v___y_232_);
lean_ctor_set(v___x_234_, 1, v___y_233_);
lean_ctor_set(v___x_234_, 2, v_cin_229_);
lean_inc_ref(v_inst_223_);
lean_inc_ref(v_inst_222_);
v_res_235_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(v_inst_222_, v_inst_223_, v_aig_225_, v___x_234_);
v_out_236_ = lean_ctor_get(v_res_235_, 1);
lean_inc_ref(v_out_236_);
v_aig_237_ = lean_ctor_get(v_res_235_, 0);
lean_inc_ref(v_aig_237_);
v_cout_238_ = lean_ctor_get(v_res_235_, 2);
lean_inc_ref(v_cout_238_);
lean_dec_ref(v_res_235_);
v_gate_239_ = lean_ctor_get(v_out_236_, 0);
lean_inc(v_gate_239_);
v_invert_240_ = lean_ctor_get_uint8(v_out_236_, sizeof(void*)*1);
lean_dec_ref(v_out_236_);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_curr_228_, v___x_241_);
lean_dec(v_curr_228_);
v___x_243_ = lean_unsigned_to_nat(2u);
v___x_244_ = lean_nat_mul(v_gate_239_, v___x_243_);
lean_dec(v_gate_239_);
v___x_245_ = l_Bool_toNat(v_invert_240_);
v___x_246_ = lean_nat_lor(v___x_244_, v___x_245_);
lean_dec(v___x_245_);
lean_dec(v___x_244_);
v_s_247_ = lean_array_push(v_s_230_, v___x_246_);
v_aig_225_ = v_aig_237_;
v_curr_228_ = v___x_242_;
v_cin_229_ = v_cout_238_;
v_s_230_ = v_s_247_;
goto _start;
}
v___jp_250_:
{
lean_object* v_ref_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_ref_252_ = lean_array_fget_borrowed(v_rhs_227_, v_curr_228_);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_shiftr(v_ref_252_, v___x_253_);
v___x_255_ = lean_nat_land(v___x_253_, v_ref_252_);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_nat_dec_eq(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_249_);
v___y_232_ = v___y_251_;
v___y_233_ = v___x_258_;
goto v___jp_231_;
}
else
{
uint8_t v___x_259_; lean_object* v___x_260_; 
v___x_259_ = 0;
v___x_260_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_260_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*1, v___x_259_);
v___y_232_ = v___y_251_;
v___y_233_ = v___x_260_;
goto v___jp_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_w_273_, lean_object* v_aig_274_, lean_object* v_lhs_275_, lean_object* v_rhs_276_, lean_object* v_curr_277_, lean_object* v_cin_278_, lean_object* v_s_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_271_, v_inst_272_, v_w_273_, v_aig_274_, v_lhs_275_, v_rhs_276_, v_curr_277_, v_cin_278_, v_s_279_);
lean_dec_ref(v_rhs_276_);
lean_dec_ref(v_lhs_275_);
lean_dec(v_w_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object* v_00_u03b1_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_w_284_, lean_object* v_aig_285_, lean_object* v_lhs_286_, lean_object* v_rhs_287_, lean_object* v_curr_288_, lean_object* v_hcurr_289_, lean_object* v_cin_290_, lean_object* v_s_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_282_, v_inst_283_, v_w_284_, v_aig_285_, v_lhs_286_, v_rhs_287_, v_curr_288_, v_cin_290_, v_s_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object* v_00_u03b1_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_w_296_, lean_object* v_aig_297_, lean_object* v_lhs_298_, lean_object* v_rhs_299_, lean_object* v_curr_300_, lean_object* v_hcurr_301_, lean_object* v_cin_302_, lean_object* v_s_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(v_00_u03b1_293_, v_inst_294_, v_inst_295_, v_w_296_, v_aig_297_, v_lhs_298_, v_rhs_299_, v_curr_300_, v_hcurr_301_, v_cin_302_, v_s_303_);
lean_dec_ref(v_rhs_299_);
lean_dec_ref(v_lhs_298_);
lean_dec(v_w_296_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_w_310_, lean_object* v_aig_311_, lean_object* v_input_312_){
_start:
{
lean_object* v_lhs_313_; lean_object* v_rhs_314_; lean_object* v___x_315_; lean_object* v_cin_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_lhs_313_ = lean_ctor_get(v_input_312_, 0);
v_rhs_314_ = lean_ctor_get(v_input_312_, 1);
v___x_315_ = lean_unsigned_to_nat(0u);
v_cin_316_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0));
v___x_317_ = lean_mk_empty_array_with_capacity(v_w_310_);
v___x_318_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_308_, v_inst_309_, v_w_310_, v_aig_311_, v_lhs_313_, v_rhs_314_, v___x_315_, v_cin_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_w_321_, lean_object* v_aig_322_, lean_object* v_input_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_319_, v_inst_320_, v_w_321_, v_aig_322_, v_input_323_);
lean_dec_ref(v_input_323_);
lean_dec(v_w_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object* v_00_u03b1_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_w_328_, lean_object* v_aig_329_, lean_object* v_input_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_326_, v_inst_327_, v_w_328_, v_aig_329_, v_input_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object* v_00_u03b1_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_w_335_, lean_object* v_aig_336_, lean_object* v_input_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(v_00_u03b1_332_, v_inst_333_, v_inst_334_, v_w_335_, v_aig_336_, v_input_337_);
lean_dec_ref(v_input_337_);
lean_dec(v_w_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_w_341_, lean_object* v_aig_342_, lean_object* v_input_343_){
_start:
{
lean_object* v_lhs_344_; lean_object* v_rhs_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_lhs_344_ = lean_ctor_get(v_input_343_, 0);
v_rhs_345_ = lean_ctor_get(v_input_343_, 1);
v___x_346_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_341_, v_aig_342_, v_lhs_344_);
v___x_347_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_341_, v_aig_342_, v_rhs_345_);
v___x_348_ = lean_nat_dec_lt(v___x_346_, v___x_347_);
lean_dec(v___x_347_);
lean_dec(v___x_346_);
if (v___x_348_ == 0)
{
lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
lean_inc_ref(v_rhs_345_);
lean_inc_ref(v_lhs_344_);
v_isSharedCheck_356_ = !lean_is_exclusive(v_input_343_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; lean_object* v_unused_358_; 
v_unused_357_ = lean_ctor_get(v_input_343_, 1);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_input_343_, 0);
lean_dec(v_unused_358_);
v___x_350_ = v_input_343_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_dec(v_input_343_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v_lhs_344_);
lean_ctor_set(v___x_350_, 0, v_rhs_345_);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_rhs_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_lhs_344_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_339_, v_inst_340_, v_w_341_, v_aig_342_, v___x_353_);
lean_dec_ref(v___x_353_);
return v___x_354_;
}
}
}
else
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_339_, v_inst_340_, v_w_341_, v_aig_342_, v_input_343_);
lean_dec_ref(v_input_343_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_w_362_, lean_object* v_aig_363_, lean_object* v_input_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_360_, v_inst_361_, v_w_362_, v_aig_363_, v_input_364_);
lean_dec(v_w_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object* v_00_u03b1_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_w_369_, lean_object* v_aig_370_, lean_object* v_input_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_367_, v_inst_368_, v_w_369_, v_aig_370_, v_input_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_w_376_, lean_object* v_aig_377_, lean_object* v_input_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(v_00_u03b1_373_, v_inst_374_, v_inst_375_, v_w_376_, v_aig_377_, v_input_378_);
lean_dec(v_w_376_);
return v_res_379_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
