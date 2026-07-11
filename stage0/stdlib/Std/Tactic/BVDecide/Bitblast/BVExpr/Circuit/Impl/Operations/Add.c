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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref_n(v_lhs_118_, 2);
v_rhs_119_ = lean_ctor_get(v_input_117_, 1);
lean_inc_ref_n(v_rhs_119_, 2);
v_cin_120_ = lean_ctor_get(v_input_117_, 2);
lean_inc_ref(v_cin_120_);
lean_dec_ref(v_input_117_);
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
uint8_t v___x_231_; 
v___x_231_ = lean_nat_dec_lt(v_curr_228_, v_w_224_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec_ref(v_cin_229_);
lean_dec(v_curr_228_);
lean_dec_ref(v_inst_223_);
lean_dec_ref(v_inst_222_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_aig_225_);
lean_ctor_set(v___x_232_, 1, v_s_230_);
return v___x_232_;
}
else
{
lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v_lin_240_; lean_object* v_ref_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; uint8_t v___x_245_; lean_object* v_rin_246_; lean_object* v___x_247_; lean_object* v_res_248_; lean_object* v_out_249_; lean_object* v_aig_250_; lean_object* v_cout_251_; lean_object* v_gate_252_; uint8_t v_invert_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_s_259_; 
v_ref_233_ = lean_array_fget_borrowed(v_lhs_226_, v_curr_228_);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_land(v___x_234_, v_ref_233_);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_nat_dec_eq(v___x_235_, v___x_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_nat_shiftr(v_ref_233_, v___x_234_);
v___x_239_ = lean_bool_not(v___x_237_);
v_lin_240_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_lin_240_, 0, v___x_238_);
lean_ctor_set_uint8(v_lin_240_, sizeof(void*)*1, v___x_239_);
v_ref_241_ = lean_array_fget_borrowed(v_rhs_227_, v_curr_228_);
v___x_242_ = lean_nat_shiftr(v_ref_241_, v___x_234_);
v___x_243_ = lean_nat_land(v___x_234_, v_ref_241_);
v___x_244_ = lean_nat_dec_eq(v___x_243_, v___x_236_);
lean_dec(v___x_243_);
v___x_245_ = lean_bool_not(v___x_244_);
v_rin_246_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_rin_246_, 0, v___x_242_);
lean_ctor_set_uint8(v_rin_246_, sizeof(void*)*1, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_247_, 0, v_lin_240_);
lean_ctor_set(v___x_247_, 1, v_rin_246_);
lean_ctor_set(v___x_247_, 2, v_cin_229_);
lean_inc_ref(v_inst_223_);
lean_inc_ref(v_inst_222_);
v_res_248_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(v_inst_222_, v_inst_223_, v_aig_225_, v___x_247_);
v_out_249_ = lean_ctor_get(v_res_248_, 1);
lean_inc_ref(v_out_249_);
v_aig_250_ = lean_ctor_get(v_res_248_, 0);
lean_inc_ref(v_aig_250_);
v_cout_251_ = lean_ctor_get(v_res_248_, 2);
lean_inc_ref(v_cout_251_);
lean_dec_ref(v_res_248_);
v_gate_252_ = lean_ctor_get(v_out_249_, 0);
lean_inc(v_gate_252_);
v_invert_253_ = lean_ctor_get_uint8(v_out_249_, sizeof(void*)*1);
lean_dec_ref(v_out_249_);
v___x_254_ = lean_nat_add(v_curr_228_, v___x_234_);
lean_dec(v_curr_228_);
v___x_255_ = lean_unsigned_to_nat(2u);
v___x_256_ = lean_nat_mul(v_gate_252_, v___x_255_);
lean_dec(v_gate_252_);
v___x_257_ = lean_bool_to_nat(v_invert_253_);
v___x_258_ = lean_nat_lor(v___x_256_, v___x_257_);
lean_dec(v___x_256_);
v_s_259_ = lean_array_push(v_s_230_, v___x_258_);
v_aig_225_ = v_aig_250_;
v_curr_228_ = v___x_254_;
v_cin_229_ = v_cout_251_;
v_s_230_ = v_s_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_w_263_, lean_object* v_aig_264_, lean_object* v_lhs_265_, lean_object* v_rhs_266_, lean_object* v_curr_267_, lean_object* v_cin_268_, lean_object* v_s_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_261_, v_inst_262_, v_w_263_, v_aig_264_, v_lhs_265_, v_rhs_266_, v_curr_267_, v_cin_268_, v_s_269_);
lean_dec_ref(v_rhs_266_);
lean_dec_ref(v_lhs_265_);
lean_dec(v_w_263_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object* v_00_u03b1_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_w_274_, lean_object* v_aig_275_, lean_object* v_lhs_276_, lean_object* v_rhs_277_, lean_object* v_curr_278_, lean_object* v_hcurr_279_, lean_object* v_cin_280_, lean_object* v_s_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_272_, v_inst_273_, v_w_274_, v_aig_275_, v_lhs_276_, v_rhs_277_, v_curr_278_, v_cin_280_, v_s_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object* v_00_u03b1_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_w_286_, lean_object* v_aig_287_, lean_object* v_lhs_288_, lean_object* v_rhs_289_, lean_object* v_curr_290_, lean_object* v_hcurr_291_, lean_object* v_cin_292_, lean_object* v_s_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(v_00_u03b1_283_, v_inst_284_, v_inst_285_, v_w_286_, v_aig_287_, v_lhs_288_, v_rhs_289_, v_curr_290_, v_hcurr_291_, v_cin_292_, v_s_293_);
lean_dec_ref(v_rhs_289_);
lean_dec_ref(v_lhs_288_);
lean_dec(v_w_286_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_w_300_, lean_object* v_aig_301_, lean_object* v_input_302_){
_start:
{
lean_object* v_lhs_303_; lean_object* v_rhs_304_; lean_object* v___x_305_; lean_object* v_cin_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_lhs_303_ = lean_ctor_get(v_input_302_, 0);
v_rhs_304_ = lean_ctor_get(v_input_302_, 1);
v___x_305_ = lean_unsigned_to_nat(0u);
v_cin_306_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0));
v___x_307_ = lean_mk_empty_array_with_capacity(v_w_300_);
v___x_308_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_298_, v_inst_299_, v_w_300_, v_aig_301_, v_lhs_303_, v_rhs_304_, v___x_305_, v_cin_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_w_311_, lean_object* v_aig_312_, lean_object* v_input_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_309_, v_inst_310_, v_w_311_, v_aig_312_, v_input_313_);
lean_dec_ref(v_input_313_);
lean_dec(v_w_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object* v_00_u03b1_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_w_318_, lean_object* v_aig_319_, lean_object* v_input_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_316_, v_inst_317_, v_w_318_, v_aig_319_, v_input_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_w_325_, lean_object* v_aig_326_, lean_object* v_input_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(v_00_u03b1_322_, v_inst_323_, v_inst_324_, v_w_325_, v_aig_326_, v_input_327_);
lean_dec_ref(v_input_327_);
lean_dec(v_w_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_w_331_, lean_object* v_aig_332_, lean_object* v_input_333_){
_start:
{
lean_object* v_lhs_334_; lean_object* v_rhs_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_lhs_334_ = lean_ctor_get(v_input_333_, 0);
v_rhs_335_ = lean_ctor_get(v_input_333_, 1);
v___x_336_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_331_, v_aig_332_, v_lhs_334_);
v___x_337_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_331_, v_aig_332_, v_rhs_335_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
lean_dec(v___x_337_);
lean_dec(v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_346_; 
lean_inc_ref(v_rhs_335_);
lean_inc_ref(v_lhs_334_);
v_isSharedCheck_346_ = !lean_is_exclusive(v_input_333_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; 
v_unused_347_ = lean_ctor_get(v_input_333_, 1);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_input_333_, 0);
lean_dec(v_unused_348_);
v___x_340_ = v_input_333_;
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
else
{
lean_dec(v_input_333_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_lhs_334_);
lean_ctor_set(v___x_340_, 0, v_rhs_335_);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_rhs_335_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_lhs_334_);
v___x_343_ = v_reuseFailAlloc_345_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_329_, v_inst_330_, v_w_331_, v_aig_332_, v___x_343_);
lean_dec_ref(v___x_343_);
return v___x_344_;
}
}
}
else
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_329_, v_inst_330_, v_w_331_, v_aig_332_, v_input_333_);
lean_dec_ref(v_input_333_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_w_352_, lean_object* v_aig_353_, lean_object* v_input_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_350_, v_inst_351_, v_w_352_, v_aig_353_, v_input_354_);
lean_dec(v_w_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_w_359_, lean_object* v_aig_360_, lean_object* v_input_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_357_, v_inst_358_, v_w_359_, v_aig_360_, v_input_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_w_366_, lean_object* v_aig_367_, lean_object* v_input_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(v_00_u03b1_363_, v_inst_364_, v_inst_365_, v_w_366_, v_aig_367_, v_input_368_);
lean_dec(v_w_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast_match__1_splitter___redArg(lean_object* v_input_370_, lean_object* v_h__1_371_){
_start:
{
lean_object* v_lhs_372_; lean_object* v_rhs_373_; lean_object* v___x_374_; 
v_lhs_372_ = lean_ctor_get(v_input_370_, 0);
lean_inc_ref(v_lhs_372_);
v_rhs_373_ = lean_ctor_get(v_input_370_, 1);
lean_inc_ref(v_rhs_373_);
lean_dec_ref(v_input_370_);
v___x_374_ = lean_apply_2(v_h__1_371_, v_lhs_372_, v_rhs_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast_match__1_splitter(lean_object* v_00_u03b1_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_w_378_, lean_object* v_aig_379_, lean_object* v_motive_380_, lean_object* v_input_381_, lean_object* v_h__1_382_){
_start:
{
lean_object* v_lhs_383_; lean_object* v_rhs_384_; lean_object* v___x_385_; 
v_lhs_383_ = lean_ctor_get(v_input_381_, 0);
lean_inc_ref(v_lhs_383_);
v_rhs_384_ = lean_ctor_get(v_input_381_, 1);
lean_inc_ref(v_rhs_384_);
lean_dec_ref(v_input_381_);
v___x_385_ = lean_apply_2(v_h__1_382_, v_lhs_383_, v_rhs_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast_match__1_splitter___boxed(lean_object* v_00_u03b1_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_w_389_, lean_object* v_aig_390_, lean_object* v_motive_391_, lean_object* v_input_392_, lean_object* v_h__1_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast_match__1_splitter(v_00_u03b1_386_, v_inst_387_, v_inst_388_, v_w_389_, v_aig_390_, v_motive_391_, v_input_392_, v_h__1_393_);
lean_dec_ref(v_aig_390_);
lean_dec(v_w_389_);
lean_dec_ref(v_inst_388_);
lean_dec_ref(v_inst_387_);
return v_res_394_;
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
