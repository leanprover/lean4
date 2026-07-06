// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas public import Init.GrindInstances.ToInt import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Internal.Linear import Init.Data.Nat.Simproc
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v_snd_3_; lean_object* v_fst_4_; lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_7_; 
v_snd_3_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_snd_3_);
v_fst_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_4_);
lean_dec_ref(v_x_1_);
v_fst_5_ = lean_ctor_get(v_snd_3_, 0);
lean_inc(v_fst_5_);
v_snd_6_ = lean_ctor_get(v_snd_3_, 1);
lean_inc(v_snd_6_);
lean_dec(v_snd_3_);
v___x_7_ = lean_apply_3(v_h__1_2_, v_fst_4_, v_fst_5_, v_snd_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(lean_object* v_n_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_){
_start:
{
lean_object* v_snd_12_; lean_object* v_fst_13_; lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_16_; 
v_snd_12_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_snd_12_);
v_fst_13_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_fst_13_);
lean_dec_ref(v_x_10_);
v_fst_14_ = lean_ctor_get(v_snd_12_, 0);
lean_inc(v_fst_14_);
v_snd_15_ = lean_ctor_get(v_snd_12_, 1);
lean_inc(v_snd_15_);
lean_dec(v_snd_12_);
v___x_16_ = lean_apply_3(v_h__1_11_, v_fst_13_, v_fst_14_, v_snd_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___boxed(lean_object* v_n_17_, lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_h__1_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(v_n_17_, v_motive_18_, v_x_19_, v_h__1_20_);
lean_dec(v_n_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(lean_object* v_x_22_, lean_object* v_h__1_23_){
_start:
{
lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_26_; 
v_fst_24_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_fst_24_);
v_snd_25_ = lean_ctor_get(v_x_22_, 1);
lean_inc(v_snd_25_);
lean_dec_ref(v_x_22_);
v___x_26_ = lean_apply_2(v_h__1_23_, v_fst_24_, v_snd_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(lean_object* v_n_27_, lean_object* v_motive_28_, lean_object* v_x_29_, lean_object* v_h__1_30_){
_start:
{
lean_object* v_fst_31_; lean_object* v_snd_32_; lean_object* v___x_33_; 
v_fst_31_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_fst_31_);
v_snd_32_ = lean_ctor_get(v_x_29_, 1);
lean_inc(v_snd_32_);
lean_dec_ref(v_x_29_);
v___x_33_ = lean_apply_2(v_h__1_30_, v_fst_31_, v_snd_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___boxed(lean_object* v_n_34_, lean_object* v_motive_35_, lean_object* v_x_36_, lean_object* v_h__1_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(v_n_34_, v_motive_35_, v_x_36_, v_h__1_37_);
lean_dec(v_n_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_h__1_41_){
_start:
{
lean_object* v_fst_42_; lean_object* v_snd_43_; lean_object* v___x_44_; 
v_fst_42_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_fst_42_);
v_snd_43_ = lean_ctor_get(v_x_40_, 1);
lean_inc(v_snd_43_);
lean_dec_ref(v_x_40_);
v___x_44_ = lean_apply_3(v_h__1_41_, v_x_39_, v_fst_42_, v_snd_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(lean_object* v_n_45_, lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_h__1_49_){
_start:
{
lean_object* v_fst_50_; lean_object* v_snd_51_; lean_object* v___x_52_; 
v_fst_50_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_fst_50_);
v_snd_51_ = lean_ctor_get(v_x_48_, 1);
lean_inc(v_snd_51_);
lean_dec_ref(v_x_48_);
v___x_52_ = lean_apply_3(v_h__1_49_, v_x_47_, v_fst_50_, v_snd_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___boxed(lean_object* v_n_53_, lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_h__1_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(v_n_53_, v_motive_54_, v_x_55_, v_x_56_, v_h__1_57_);
lean_dec(v_n_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object* v_f_59_, lean_object* v_h__1_60_){
_start:
{
lean_object* v_clauses_61_; lean_object* v_rupUnits_62_; lean_object* v_ratUnits_63_; lean_object* v_assignments_64_; lean_object* v___x_65_; 
v_clauses_61_ = lean_ctor_get(v_f_59_, 0);
lean_inc_ref(v_clauses_61_);
v_rupUnits_62_ = lean_ctor_get(v_f_59_, 1);
lean_inc_ref(v_rupUnits_62_);
v_ratUnits_63_ = lean_ctor_get(v_f_59_, 2);
lean_inc_ref(v_ratUnits_63_);
v_assignments_64_ = lean_ctor_get(v_f_59_, 3);
lean_inc_ref(v_assignments_64_);
lean_dec_ref(v_f_59_);
v___x_65_ = lean_apply_4(v_h__1_60_, v_clauses_61_, v_rupUnits_62_, v_ratUnits_63_, v_assignments_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object* v_n_66_, lean_object* v_motive_67_, lean_object* v_f_68_, lean_object* v_h__1_69_){
_start:
{
lean_object* v_clauses_70_; lean_object* v_rupUnits_71_; lean_object* v_ratUnits_72_; lean_object* v_assignments_73_; lean_object* v___x_74_; 
v_clauses_70_ = lean_ctor_get(v_f_68_, 0);
lean_inc_ref(v_clauses_70_);
v_rupUnits_71_ = lean_ctor_get(v_f_68_, 1);
lean_inc_ref(v_rupUnits_71_);
v_ratUnits_72_ = lean_ctor_get(v_f_68_, 2);
lean_inc_ref(v_ratUnits_72_);
v_assignments_73_ = lean_ctor_get(v_f_68_, 3);
lean_inc_ref(v_assignments_73_);
lean_dec_ref(v_f_68_);
v___x_74_ = lean_apply_4(v_h__1_69_, v_clauses_70_, v_rupUnits_71_, v_ratUnits_72_, v_assignments_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object* v_n_75_, lean_object* v_motive_76_, lean_object* v_f_77_, lean_object* v_h__1_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_75_, v_motive_76_, v_f_77_, v_h__1_78_);
lean_dec(v_n_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(lean_object* v_x_80_, lean_object* v_h__1_81_){
_start:
{
lean_object* v_snd_82_; lean_object* v_snd_83_; lean_object* v_fst_84_; lean_object* v_fst_85_; lean_object* v_fst_86_; lean_object* v_snd_87_; lean_object* v___x_88_; 
v_snd_82_ = lean_ctor_get(v_x_80_, 1);
lean_inc(v_snd_82_);
v_snd_83_ = lean_ctor_get(v_snd_82_, 1);
lean_inc(v_snd_83_);
v_fst_84_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_fst_84_);
lean_dec_ref(v_x_80_);
v_fst_85_ = lean_ctor_get(v_snd_82_, 0);
lean_inc(v_fst_85_);
lean_dec(v_snd_82_);
v_fst_86_ = lean_ctor_get(v_snd_83_, 0);
lean_inc(v_fst_86_);
v_snd_87_ = lean_ctor_get(v_snd_83_, 1);
lean_inc(v_snd_87_);
lean_dec(v_snd_83_);
v___x_88_ = lean_apply_4(v_h__1_81_, v_fst_84_, v_fst_85_, v_fst_86_, v_snd_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(lean_object* v_n_89_, lean_object* v_motive_90_, lean_object* v_x_91_, lean_object* v_h__1_92_){
_start:
{
lean_object* v_snd_93_; lean_object* v_snd_94_; lean_object* v_fst_95_; lean_object* v_fst_96_; lean_object* v_fst_97_; lean_object* v_snd_98_; lean_object* v___x_99_; 
v_snd_93_ = lean_ctor_get(v_x_91_, 1);
lean_inc(v_snd_93_);
v_snd_94_ = lean_ctor_get(v_snd_93_, 1);
lean_inc(v_snd_94_);
v_fst_95_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_fst_95_);
lean_dec_ref(v_x_91_);
v_fst_96_ = lean_ctor_get(v_snd_93_, 0);
lean_inc(v_fst_96_);
lean_dec(v_snd_93_);
v_fst_97_ = lean_ctor_get(v_snd_94_, 0);
lean_inc(v_fst_97_);
v_snd_98_ = lean_ctor_get(v_snd_94_, 1);
lean_inc(v_snd_98_);
lean_dec(v_snd_94_);
v___x_99_ = lean_apply_4(v_h__1_92_, v_fst_95_, v_fst_96_, v_fst_97_, v_snd_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___boxed(lean_object* v_n_100_, lean_object* v_motive_101_, lean_object* v_x_102_, lean_object* v_h__1_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(v_n_100_, v_motive_101_, v_x_102_, v_h__1_103_);
lean_dec(v_n_100_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_1(v_h__3_108_, v___x_109_);
return v___x_110_;
}
else
{
lean_object* v_val_111_; 
lean_dec(v_h__3_108_);
v_val_111_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_111_);
lean_dec_ref_known(v_x_105_, 1);
if (lean_obj_tag(v_val_111_) == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_106_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_apply_1(v_h__2_107_, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v_val_114_; lean_object* v___x_115_; 
lean_dec(v_h__2_107_);
v_val_114_ = lean_ctor_get(v_val_111_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v_val_111_, 1);
v___x_115_ = lean_apply_1(v_h__1_106_, v_val_114_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object* v_n_116_, lean_object* v_motive_117_, lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_, lean_object* v_h__3_121_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_h__2_120_);
lean_dec(v_h__1_119_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_1(v_h__3_121_, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; 
lean_dec(v_h__3_121_);
v_val_124_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v_x_118_, 1);
if (lean_obj_tag(v_val_124_) == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_h__1_119_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_apply_1(v_h__2_120_, v___x_125_);
return v___x_126_;
}
else
{
lean_object* v_val_127_; lean_object* v___x_128_; 
lean_dec(v_h__2_120_);
v_val_127_ = lean_ctor_get(v_val_124_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v_val_124_, 1);
v___x_128_ = lean_apply_1(v_h__1_119_, v_val_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object* v_n_129_, lean_object* v_motive_130_, lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_, lean_object* v_h__3_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_129_, v_motive_130_, v_x_131_, v_h__1_132_, v_h__2_133_, v_h__3_134_);
lean_dec(v_n_129_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_, lean_object* v_h__3_139_, lean_object* v_h__4_140_){
_start:
{
switch(lean_obj_tag(v_x_136_))
{
case 0:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_h__4_140_);
lean_dec(v_h__3_139_);
lean_dec(v_h__2_138_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_apply_1(v_h__1_137_, v___x_141_);
return v___x_142_;
}
case 1:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_h__4_140_);
lean_dec(v_h__3_139_);
lean_dec(v_h__1_137_);
v___x_143_ = lean_box(0);
v___x_144_ = lean_apply_1(v_h__2_138_, v___x_143_);
return v___x_144_;
}
case 2:
{
lean_object* v_l_145_; lean_object* v_fst_146_; lean_object* v_snd_147_; lean_object* v___x_148_; 
lean_dec(v_h__4_140_);
lean_dec(v_h__2_138_);
lean_dec(v_h__1_137_);
v_l_145_ = lean_ctor_get(v_x_136_, 0);
lean_inc_ref(v_l_145_);
lean_dec_ref_known(v_x_136_, 1);
v_fst_146_ = lean_ctor_get(v_l_145_, 0);
lean_inc(v_fst_146_);
v_snd_147_ = lean_ctor_get(v_l_145_, 1);
lean_inc(v_snd_147_);
lean_dec_ref(v_l_145_);
v___x_148_ = lean_apply_2(v_h__3_139_, v_fst_146_, v_snd_147_);
return v___x_148_;
}
default: 
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_h__3_139_);
lean_dec(v_h__2_138_);
lean_dec(v_h__1_137_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v_h__4_140_, v___x_149_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object* v_n_151_, lean_object* v_motive_152_, lean_object* v_x_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_, lean_object* v_h__3_156_, lean_object* v_h__4_157_){
_start:
{
switch(lean_obj_tag(v_x_153_))
{
case 0:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_h__4_157_);
lean_dec(v_h__3_156_);
lean_dec(v_h__2_155_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_apply_1(v_h__1_154_, v___x_158_);
return v___x_159_;
}
case 1:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__4_157_);
lean_dec(v_h__3_156_);
lean_dec(v_h__1_154_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_1(v_h__2_155_, v___x_160_);
return v___x_161_;
}
case 2:
{
lean_object* v_l_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v___x_165_; 
lean_dec(v_h__4_157_);
lean_dec(v_h__2_155_);
lean_dec(v_h__1_154_);
v_l_162_ = lean_ctor_get(v_x_153_, 0);
lean_inc_ref(v_l_162_);
lean_dec_ref_known(v_x_153_, 1);
v_fst_163_ = lean_ctor_get(v_l_162_, 0);
lean_inc(v_fst_163_);
v_snd_164_ = lean_ctor_get(v_l_162_, 1);
lean_inc(v_snd_164_);
lean_dec_ref(v_l_162_);
v___x_165_ = lean_apply_2(v_h__3_156_, v_fst_163_, v_snd_164_);
return v___x_165_;
}
default: 
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__3_156_);
lean_dec(v_h__2_155_);
lean_dec(v_h__1_154_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__4_157_, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object* v_n_168_, lean_object* v_motive_169_, lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_, lean_object* v_h__3_173_, lean_object* v_h__4_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_168_, v_motive_169_, v_x_170_, v_h__1_171_, v_h__2_172_, v_h__3_173_, v_h__4_174_);
lean_dec(v_n_168_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter___redArg(lean_object* v_x_176_, lean_object* v_x_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
lean_object* v_head_180_; lean_object* v_tail_181_; lean_object* v_zero_182_; uint8_t v_isZero_183_; 
v_head_180_ = lean_ctor_get(v_x_176_, 0);
lean_inc(v_head_180_);
v_tail_181_ = lean_ctor_get(v_x_176_, 1);
lean_inc(v_tail_181_);
lean_dec(v_x_176_);
v_zero_182_ = lean_unsigned_to_nat(0u);
v_isZero_183_ = lean_nat_dec_eq(v_x_177_, v_zero_182_);
if (v_isZero_183_ == 1)
{
lean_object* v___x_184_; 
lean_dec(v_h__2_179_);
v___x_184_ = lean_apply_3(v_h__1_178_, v_head_180_, v_tail_181_, lean_box(0));
return v___x_184_;
}
else
{
lean_object* v_one_185_; lean_object* v_n_186_; lean_object* v___x_187_; 
lean_dec(v_h__1_178_);
v_one_185_ = lean_unsigned_to_nat(1u);
v_n_186_ = lean_nat_sub(v_x_177_, v_one_185_);
v___x_187_ = lean_apply_4(v_h__2_179_, v_head_180_, v_tail_181_, v_n_186_, lean_box(0));
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter___redArg___boxed(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter___redArg(v_x_188_, v_x_189_, v_h__1_190_, v_h__2_191_);
lean_dec(v_x_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter(lean_object* v_00_u03b1_193_, lean_object* v_motive_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
lean_object* v_head_199_; lean_object* v_tail_200_; lean_object* v_zero_201_; uint8_t v_isZero_202_; 
v_head_199_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_head_199_);
v_tail_200_ = lean_ctor_get(v_x_195_, 1);
lean_inc(v_tail_200_);
lean_dec(v_x_195_);
v_zero_201_ = lean_unsigned_to_nat(0u);
v_isZero_202_ = lean_nat_dec_eq(v_x_196_, v_zero_201_);
if (v_isZero_202_ == 1)
{
lean_object* v___x_203_; 
lean_dec(v_h__2_198_);
v___x_203_ = lean_apply_3(v_h__1_197_, v_head_199_, v_tail_200_, lean_box(0));
return v___x_203_;
}
else
{
lean_object* v_one_204_; lean_object* v_n_205_; lean_object* v___x_206_; 
lean_dec(v_h__1_197_);
v_one_204_ = lean_unsigned_to_nat(1u);
v_n_205_ = lean_nat_sub(v_x_196_, v_one_204_);
v___x_206_ = lean_apply_4(v_h__2_198_, v_head_199_, v_tail_200_, v_n_205_, lean_box(0));
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter___boxed(lean_object* v_00_u03b1_207_, lean_object* v_motive_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__List_get_match__1_splitter(v_00_u03b1_207_, v_motive_208_, v_x_209_, v_x_210_, v_h__1_211_, v_h__2_212_);
lean_dec(v_x_210_);
return v_res_213_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
}
#ifdef __cplusplus
}
#endif
