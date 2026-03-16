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
lean_object* v___x_68_; 
v___x_68_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(v_val_66_, v_h__1_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_aig1_72_, lean_object* v_motive_73_, lean_object* v_val_74_, lean_object* v_h__1_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(v_00_u03b1_69_, v_inst_70_, v_inst_71_, v_aig1_72_, v_motive_73_, v_val_74_, v_h__1_75_);
lean_dec_ref(v_aig1_72_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_aig_79_, lean_object* v_input_80_){
_start:
{
lean_object* v_lhs_81_; lean_object* v_rhs_82_; lean_object* v_cin_83_; lean_object* v___x_84_; lean_object* v_res_85_; lean_object* v_aig_86_; lean_object* v_ref_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_104_; 
v_lhs_81_ = lean_ctor_get(v_input_80_, 0);
lean_inc_ref(v_lhs_81_);
v_rhs_82_ = lean_ctor_get(v_input_80_, 1);
lean_inc_ref(v_rhs_82_);
v_cin_83_ = lean_ctor_get(v_input_80_, 2);
lean_inc_ref(v_cin_83_);
lean_dec_ref(v_input_80_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v_lhs_81_);
lean_ctor_set(v___x_84_, 1, v_rhs_82_);
lean_inc_ref(v_inst_78_);
lean_inc_ref(v_inst_77_);
v_res_85_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_77_, v_inst_78_, v_aig_79_, v___x_84_);
v_aig_86_ = lean_ctor_get(v_res_85_, 0);
v_ref_87_ = lean_ctor_get(v_res_85_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v_res_85_);
if (v_isSharedCheck_104_ == 0)
{
v___x_89_ = v_res_85_;
v_isShared_90_ = v_isSharedCheck_104_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_ref_87_);
lean_inc(v_aig_86_);
lean_dec(v_res_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_104_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_gate_91_; uint8_t v_invert_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_103_; 
v_gate_91_ = lean_ctor_get(v_cin_83_, 0);
v_invert_92_ = lean_ctor_get_uint8(v_cin_83_, sizeof(void*)*1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_cin_83_);
if (v_isSharedCheck_103_ == 0)
{
v___x_94_ = v_cin_83_;
v_isShared_95_ = v_isSharedCheck_103_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_gate_91_);
lean_dec(v_cin_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_103_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_cin_97_; 
if (v_isShared_95_ == 0)
{
v_cin_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_gate_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*1, v_invert_92_);
v_cin_97_ = v_reuseFailAlloc_102_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_99_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_cin_97_);
lean_ctor_set(v___x_89_, 0, v_ref_87_);
v___x_99_ = v___x_89_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_ref_87_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_cin_97_);
v___x_99_ = v_reuseFailAlloc_101_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_77_, v_inst_78_, v_aig_86_, v___x_99_);
return v___x_100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object* v_00_u03b1_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_aig_108_, lean_object* v_input_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(v_inst_106_, v_inst_107_, v_aig_108_, v_input_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_aig_113_, lean_object* v_input_114_){
_start:
{
lean_object* v_lhs_115_; lean_object* v_rhs_116_; lean_object* v_cin_117_; lean_object* v___x_118_; lean_object* v_res_119_; lean_object* v_aig_120_; lean_object* v_ref_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_185_; 
v_lhs_115_ = lean_ctor_get(v_input_114_, 0);
lean_inc_ref(v_lhs_115_);
v_rhs_116_ = lean_ctor_get(v_input_114_, 1);
lean_inc_ref(v_rhs_116_);
v_cin_117_ = lean_ctor_get(v_input_114_, 2);
lean_inc_ref(v_cin_117_);
lean_dec_ref(v_input_114_);
lean_inc_ref(v_rhs_116_);
lean_inc_ref(v_lhs_115_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_lhs_115_);
lean_ctor_set(v___x_118_, 1, v_rhs_116_);
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v_res_119_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_111_, v_inst_112_, v_aig_113_, v___x_118_);
v_aig_120_ = lean_ctor_get(v_res_119_, 0);
v_ref_121_ = lean_ctor_get(v_res_119_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_res_119_);
if (v_isSharedCheck_185_ == 0)
{
v___x_123_ = v_res_119_;
v_isShared_124_ = v_isSharedCheck_185_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_ref_121_);
lean_inc(v_aig_120_);
lean_dec(v_res_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_185_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_gate_125_; uint8_t v_invert_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_184_; 
v_gate_125_ = lean_ctor_get(v_lhs_115_, 0);
v_invert_126_ = lean_ctor_get_uint8(v_lhs_115_, sizeof(void*)*1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_lhs_115_);
if (v_isSharedCheck_184_ == 0)
{
v___x_128_ = v_lhs_115_;
v_isShared_129_ = v_isSharedCheck_184_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_gate_125_);
lean_dec(v_lhs_115_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_184_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_gate_130_; uint8_t v_invert_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_183_; 
v_gate_130_ = lean_ctor_get(v_rhs_116_, 0);
v_invert_131_ = lean_ctor_get_uint8(v_rhs_116_, sizeof(void*)*1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_rhs_116_);
if (v_isSharedCheck_183_ == 0)
{
v___x_133_ = v_rhs_116_;
v_isShared_134_ = v_isSharedCheck_183_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_gate_130_);
lean_dec(v_rhs_116_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_183_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_gate_135_; uint8_t v_invert_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_182_; 
v_gate_135_ = lean_ctor_get(v_cin_117_, 0);
v_invert_136_ = lean_ctor_get_uint8(v_cin_117_, sizeof(void*)*1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_cin_117_);
if (v_isSharedCheck_182_ == 0)
{
v___x_138_ = v_cin_117_;
v_isShared_139_ = v_isSharedCheck_182_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_gate_135_);
lean_dec(v_cin_117_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_182_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v_cin_141_; 
if (v_isShared_139_ == 0)
{
v_cin_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_gate_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, sizeof(void*)*1, v_invert_136_);
v_cin_141_ = v_reuseFailAlloc_181_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_cin_141_);
lean_ctor_set(v___x_123_, 0, v_ref_121_);
v___x_143_ = v___x_123_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_ref_121_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_cin_141_);
v___x_143_ = v_reuseFailAlloc_180_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_res_144_; lean_object* v_aig_145_; lean_object* v_ref_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_179_; 
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v_res_144_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_111_, v_inst_112_, v_aig_120_, v___x_143_);
v_aig_145_ = lean_ctor_get(v_res_144_, 0);
v_ref_146_ = lean_ctor_get(v_res_144_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_res_144_);
if (v_isSharedCheck_179_ == 0)
{
v___x_148_ = v_res_144_;
v_isShared_149_ = v_isSharedCheck_179_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_ref_146_);
lean_inc(v_aig_145_);
lean_dec(v_res_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_179_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_lhs_151_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v_gate_125_);
v_lhs_151_ = v___x_133_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_gate_125_);
v_lhs_151_ = v_reuseFailAlloc_178_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v_rhs_153_; 
lean_ctor_set_uint8(v_lhs_151_, sizeof(void*)*1, v_invert_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v_gate_130_);
v_rhs_153_ = v___x_128_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_gate_130_);
v_rhs_153_ = v_reuseFailAlloc_177_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_155_; 
lean_ctor_set_uint8(v_rhs_153_, sizeof(void*)*1, v_invert_131_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_rhs_153_);
lean_ctor_set(v___x_148_, 0, v_lhs_151_);
v___x_155_ = v___x_148_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_lhs_151_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_rhs_153_);
v___x_155_ = v_reuseFailAlloc_176_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v_res_156_; lean_object* v_aig_157_; lean_object* v_ref_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_175_; 
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v_res_156_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_111_, v_inst_112_, v_aig_145_, v___x_155_);
v_aig_157_ = lean_ctor_get(v_res_156_, 0);
v_ref_158_ = lean_ctor_get(v_res_156_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_res_156_);
if (v_isSharedCheck_175_ == 0)
{
v___x_160_ = v_res_156_;
v_isShared_161_ = v_isSharedCheck_175_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_ref_158_);
lean_inc(v_aig_157_);
lean_dec(v_res_156_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_175_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_gate_162_; uint8_t v_invert_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_174_; 
v_gate_162_ = lean_ctor_get(v_ref_146_, 0);
v_invert_163_ = lean_ctor_get_uint8(v_ref_146_, sizeof(void*)*1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_ref_146_);
if (v_isSharedCheck_174_ == 0)
{
v___x_165_ = v_ref_146_;
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_gate_162_);
lean_dec(v_ref_146_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_lorRef_168_; 
if (v_isShared_166_ == 0)
{
v_lorRef_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_gate_162_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*1, v_invert_163_);
v_lorRef_168_ = v_reuseFailAlloc_173_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_170_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v_lorRef_168_);
v___x_170_ = v___x_160_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_lorRef_168_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_ref_158_);
v___x_170_ = v_reuseFailAlloc_172_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_111_, v_inst_112_, v_aig_157_, v___x_170_);
return v___x_171_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_aig_189_, lean_object* v_input_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_187_, v_inst_188_, v_aig_189_, v_input_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_aig_194_, lean_object* v_input_195_){
_start:
{
lean_object* v_res_196_; lean_object* v_aig_197_; lean_object* v_ref_198_; lean_object* v_input_199_; lean_object* v_res_200_; lean_object* v_aig_201_; lean_object* v_ref_202_; lean_object* v_gate_203_; uint8_t v_invert_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
lean_inc_ref(v_input_195_);
lean_inc_ref(v_inst_193_);
lean_inc_ref(v_inst_192_);
v_res_196_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(v_inst_192_, v_inst_193_, v_aig_194_, v_input_195_);
v_aig_197_ = lean_ctor_get(v_res_196_, 0);
lean_inc_ref(v_aig_197_);
v_ref_198_ = lean_ctor_get(v_res_196_, 1);
lean_inc_ref(v_ref_198_);
lean_dec_ref(v_res_196_);
v_input_199_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(v_input_195_);
v_res_200_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(v_inst_192_, v_inst_193_, v_aig_197_, v_input_199_);
v_aig_201_ = lean_ctor_get(v_res_200_, 0);
lean_inc_ref(v_aig_201_);
v_ref_202_ = lean_ctor_get(v_res_200_, 1);
lean_inc_ref(v_ref_202_);
lean_dec_ref(v_res_200_);
v_gate_203_ = lean_ctor_get(v_ref_198_, 0);
v_invert_204_ = lean_ctor_get_uint8(v_ref_198_, sizeof(void*)*1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_ref_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v_ref_198_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_gate_203_);
lean_dec(v_ref_198_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_outRef_209_; 
if (v_isShared_207_ == 0)
{
v_outRef_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_gate_203_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*1, v_invert_204_);
v_outRef_209_ = v_reuseFailAlloc_211_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v_aig_201_);
lean_ctor_set(v___x_210_, 1, v_outRef_209_);
lean_ctor_set(v___x_210_, 2, v_ref_202_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object* v_00_u03b1_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_aig_216_, lean_object* v_input_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(v_inst_214_, v_inst_215_, v_aig_216_, v_input_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_w_221_, lean_object* v_aig_222_, lean_object* v_lhs_223_, lean_object* v_rhs_224_, lean_object* v_curr_225_, lean_object* v_cin_226_, lean_object* v_s_227_){
_start:
{
lean_object* v___y_229_; lean_object* v___y_230_; uint8_t v___x_246_; lean_object* v___y_248_; 
v___x_246_ = lean_nat_dec_lt(v_curr_225_, v_w_221_);
if (v___x_246_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_cin_226_);
lean_dec(v_curr_225_);
lean_dec_ref(v_inst_220_);
lean_dec_ref(v_inst_219_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_aig_222_);
lean_ctor_set(v___x_258_, 1, v_s_227_);
return v___x_258_;
}
else
{
lean_object* v_ref_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_ref_259_ = lean_array_fget_borrowed(v_lhs_223_, v_curr_225_);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_shiftr(v_ref_259_, v___x_260_);
v___x_262_ = lean_nat_land(v___x_260_, v_ref_259_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_nat_dec_eq(v___x_262_, v___x_263_);
lean_dec(v___x_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_261_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_246_);
v___y_248_ = v___x_265_;
goto v___jp_247_;
}
else
{
uint8_t v___x_266_; lean_object* v___x_267_; 
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_261_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
v___y_248_ = v___x_267_;
goto v___jp_247_;
}
}
v___jp_228_:
{
lean_object* v___x_231_; lean_object* v_res_232_; lean_object* v_out_233_; lean_object* v_aig_234_; lean_object* v_cout_235_; lean_object* v_gate_236_; uint8_t v_invert_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_s_244_; 
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___y_229_);
lean_ctor_set(v___x_231_, 1, v___y_230_);
lean_ctor_set(v___x_231_, 2, v_cin_226_);
lean_inc_ref(v_inst_220_);
lean_inc_ref(v_inst_219_);
v_res_232_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(v_inst_219_, v_inst_220_, v_aig_222_, v___x_231_);
v_out_233_ = lean_ctor_get(v_res_232_, 1);
lean_inc_ref(v_out_233_);
v_aig_234_ = lean_ctor_get(v_res_232_, 0);
lean_inc_ref(v_aig_234_);
v_cout_235_ = lean_ctor_get(v_res_232_, 2);
lean_inc_ref(v_cout_235_);
lean_dec_ref(v_res_232_);
v_gate_236_ = lean_ctor_get(v_out_233_, 0);
lean_inc(v_gate_236_);
v_invert_237_ = lean_ctor_get_uint8(v_out_233_, sizeof(void*)*1);
lean_dec_ref(v_out_233_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_curr_225_, v___x_238_);
lean_dec(v_curr_225_);
v___x_240_ = lean_unsigned_to_nat(2u);
v___x_241_ = lean_nat_mul(v_gate_236_, v___x_240_);
lean_dec(v_gate_236_);
v___x_242_ = l_Bool_toNat(v_invert_237_);
v___x_243_ = lean_nat_lor(v___x_241_, v___x_242_);
lean_dec(v___x_242_);
lean_dec(v___x_241_);
v_s_244_ = lean_array_push(v_s_227_, v___x_243_);
v_aig_222_ = v_aig_234_;
v_curr_225_ = v___x_239_;
v_cin_226_ = v_cout_235_;
v_s_227_ = v_s_244_;
goto _start;
}
v___jp_247_:
{
lean_object* v_ref_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_ref_249_ = lean_array_fget_borrowed(v_rhs_224_, v_curr_225_);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_shiftr(v_ref_249_, v___x_250_);
v___x_252_ = lean_nat_land(v___x_250_, v_ref_249_);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_nat_dec_eq(v___x_252_, v___x_253_);
lean_dec(v___x_252_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_251_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_246_);
v___y_229_ = v___y_248_;
v___y_230_ = v___x_255_;
goto v___jp_228_;
}
else
{
uint8_t v___x_256_; lean_object* v___x_257_; 
v___x_256_ = 0;
v___x_257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_251_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_256_);
v___y_229_ = v___y_248_;
v___y_230_ = v___x_257_;
goto v___jp_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_w_270_, lean_object* v_aig_271_, lean_object* v_lhs_272_, lean_object* v_rhs_273_, lean_object* v_curr_274_, lean_object* v_cin_275_, lean_object* v_s_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_268_, v_inst_269_, v_w_270_, v_aig_271_, v_lhs_272_, v_rhs_273_, v_curr_274_, v_cin_275_, v_s_276_);
lean_dec_ref(v_rhs_273_);
lean_dec_ref(v_lhs_272_);
lean_dec(v_w_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object* v_00_u03b1_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_w_281_, lean_object* v_aig_282_, lean_object* v_lhs_283_, lean_object* v_rhs_284_, lean_object* v_curr_285_, lean_object* v_hcurr_286_, lean_object* v_cin_287_, lean_object* v_s_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_279_, v_inst_280_, v_w_281_, v_aig_282_, v_lhs_283_, v_rhs_284_, v_curr_285_, v_cin_287_, v_s_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_w_293_, lean_object* v_aig_294_, lean_object* v_lhs_295_, lean_object* v_rhs_296_, lean_object* v_curr_297_, lean_object* v_hcurr_298_, lean_object* v_cin_299_, lean_object* v_s_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(v_00_u03b1_290_, v_inst_291_, v_inst_292_, v_w_293_, v_aig_294_, v_lhs_295_, v_rhs_296_, v_curr_297_, v_hcurr_298_, v_cin_299_, v_s_300_);
lean_dec_ref(v_rhs_296_);
lean_dec_ref(v_lhs_295_);
lean_dec(v_w_293_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_w_307_, lean_object* v_aig_308_, lean_object* v_input_309_){
_start:
{
lean_object* v_lhs_310_; lean_object* v_rhs_311_; lean_object* v___x_312_; lean_object* v_cin_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_lhs_310_ = lean_ctor_get(v_input_309_, 0);
v_rhs_311_ = lean_ctor_get(v_input_309_, 1);
v___x_312_ = lean_unsigned_to_nat(0u);
v_cin_313_ = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0));
v___x_314_ = lean_mk_empty_array_with_capacity(v_w_307_);
v___x_315_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(v_inst_305_, v_inst_306_, v_w_307_, v_aig_308_, v_lhs_310_, v_rhs_311_, v___x_312_, v_cin_313_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_w_318_, lean_object* v_aig_319_, lean_object* v_input_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_316_, v_inst_317_, v_w_318_, v_aig_319_, v_input_320_);
lean_dec_ref(v_input_320_);
lean_dec(v_w_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_w_325_, lean_object* v_aig_326_, lean_object* v_input_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_323_, v_inst_324_, v_w_325_, v_aig_326_, v_input_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_w_332_, lean_object* v_aig_333_, lean_object* v_input_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(v_00_u03b1_329_, v_inst_330_, v_inst_331_, v_w_332_, v_aig_333_, v_input_334_);
lean_dec_ref(v_input_334_);
lean_dec(v_w_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_w_338_, lean_object* v_aig_339_, lean_object* v_input_340_){
_start:
{
lean_object* v_lhs_341_; lean_object* v_rhs_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_lhs_341_ = lean_ctor_get(v_input_340_, 0);
v_rhs_342_ = lean_ctor_get(v_input_340_, 1);
v___x_343_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_338_, v_aig_339_, v_lhs_341_);
v___x_344_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_338_, v_aig_339_, v_rhs_342_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
lean_dec(v___x_344_);
lean_dec(v___x_343_);
if (v___x_345_ == 0)
{
lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_353_; 
lean_inc_ref(v_rhs_342_);
lean_inc_ref(v_lhs_341_);
v_isSharedCheck_353_ = !lean_is_exclusive(v_input_340_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; 
v_unused_354_ = lean_ctor_get(v_input_340_, 1);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_input_340_, 0);
lean_dec(v_unused_355_);
v___x_347_ = v_input_340_;
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
else
{
lean_dec(v_input_340_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_lhs_341_);
lean_ctor_set(v___x_347_, 0, v_rhs_342_);
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_rhs_342_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_lhs_341_);
v___x_350_ = v_reuseFailAlloc_352_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_336_, v_inst_337_, v_w_338_, v_aig_339_, v___x_350_);
lean_dec_ref(v___x_350_);
return v___x_351_;
}
}
}
else
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(v_inst_336_, v_inst_337_, v_w_338_, v_aig_339_, v_input_340_);
lean_dec_ref(v_input_340_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_w_359_, lean_object* v_aig_360_, lean_object* v_input_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_357_, v_inst_358_, v_w_359_, v_aig_360_, v_input_361_);
lean_dec(v_w_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_w_366_, lean_object* v_aig_367_, lean_object* v_input_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_364_, v_inst_365_, v_w_366_, v_aig_367_, v_input_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object* v_00_u03b1_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_w_373_, lean_object* v_aig_374_, lean_object* v_input_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(v_00_u03b1_370_, v_inst_371_, v_inst_372_, v_w_373_, v_aig_374_, v_input_375_);
lean_dec(v_w_373_);
return v_res_376_;
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
