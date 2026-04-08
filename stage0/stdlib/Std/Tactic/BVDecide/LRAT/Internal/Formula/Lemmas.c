// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation public import Std.Tactic.BVDecide.LRAT.Internal.CNF import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Int.OfNat import Init.Data.List.Pairwise import Init.Data.Nat.Linear
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object* v_f_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v_clauses_3_; lean_object* v_rupUnits_4_; lean_object* v_ratUnits_5_; lean_object* v_assignments_6_; lean_object* v___x_7_; 
v_clauses_3_ = lean_ctor_get(v_f_1_, 0);
lean_inc_ref(v_clauses_3_);
v_rupUnits_4_ = lean_ctor_get(v_f_1_, 1);
lean_inc_ref(v_rupUnits_4_);
v_ratUnits_5_ = lean_ctor_get(v_f_1_, 2);
lean_inc_ref(v_ratUnits_5_);
v_assignments_6_ = lean_ctor_get(v_f_1_, 3);
lean_inc_ref(v_assignments_6_);
lean_dec_ref(v_f_1_);
v___x_7_ = lean_apply_4(v_h__1_2_, v_clauses_3_, v_rupUnits_4_, v_ratUnits_5_, v_assignments_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object* v_n_8_, lean_object* v_motive_9_, lean_object* v_f_10_, lean_object* v_h__1_11_){
_start:
{
lean_object* v_clauses_12_; lean_object* v_rupUnits_13_; lean_object* v_ratUnits_14_; lean_object* v_assignments_15_; lean_object* v___x_16_; 
v_clauses_12_ = lean_ctor_get(v_f_10_, 0);
lean_inc_ref(v_clauses_12_);
v_rupUnits_13_ = lean_ctor_get(v_f_10_, 1);
lean_inc_ref(v_rupUnits_13_);
v_ratUnits_14_ = lean_ctor_get(v_f_10_, 2);
lean_inc_ref(v_ratUnits_14_);
v_assignments_15_ = lean_ctor_get(v_f_10_, 3);
lean_inc_ref(v_assignments_15_);
lean_dec_ref(v_f_10_);
v___x_16_ = lean_apply_4(v_h__1_11_, v_clauses_12_, v_rupUnits_13_, v_ratUnits_14_, v_assignments_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object* v_n_17_, lean_object* v_motive_18_, lean_object* v_f_19_, lean_object* v_h__1_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_17_, v_motive_18_, v_f_19_, v_h__1_20_);
lean_dec(v_n_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___redArg(lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_, lean_object* v_h__3_25_){
_start:
{
if (lean_obj_tag(v_x_22_) == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__3_25_);
lean_dec(v_h__2_24_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_1(v_h__1_23_, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v_val_28_; lean_object* v_snd_29_; uint8_t v___x_30_; 
lean_dec(v_h__1_23_);
v_val_28_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_val_28_);
lean_dec_ref(v_x_22_);
v_snd_29_ = lean_ctor_get(v_val_28_, 1);
v___x_30_ = lean_unbox(v_snd_29_);
if (v___x_30_ == 0)
{
lean_object* v_fst_31_; lean_object* v___x_32_; 
lean_dec(v_h__2_24_);
v_fst_31_ = lean_ctor_get(v_val_28_, 0);
lean_inc(v_fst_31_);
lean_dec(v_val_28_);
v___x_32_ = lean_apply_1(v_h__3_25_, v_fst_31_);
return v___x_32_;
}
else
{
lean_object* v_fst_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_25_);
v_fst_33_ = lean_ctor_get(v_val_28_, 0);
lean_inc(v_fst_33_);
lean_dec(v_val_28_);
v___x_34_ = lean_apply_1(v_h__2_24_, v_fst_33_);
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(lean_object* v_n_35_, lean_object* v_motive_36_, lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_, lean_object* v_h__3_40_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_h__3_40_);
lean_dec(v_h__2_39_);
v___x_41_ = lean_box(0);
v___x_42_ = lean_apply_1(v_h__1_38_, v___x_41_);
return v___x_42_;
}
else
{
lean_object* v_val_43_; lean_object* v_snd_44_; uint8_t v___x_45_; 
lean_dec(v_h__1_38_);
v_val_43_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_43_);
lean_dec_ref(v_x_37_);
v_snd_44_ = lean_ctor_get(v_val_43_, 1);
v___x_45_ = lean_unbox(v_snd_44_);
if (v___x_45_ == 0)
{
lean_object* v_fst_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_39_);
v_fst_46_ = lean_ctor_get(v_val_43_, 0);
lean_inc(v_fst_46_);
lean_dec(v_val_43_);
v___x_47_ = lean_apply_1(v_h__3_40_, v_fst_46_);
return v___x_47_;
}
else
{
lean_object* v_fst_48_; lean_object* v___x_49_; 
lean_dec(v_h__3_40_);
v_fst_48_ = lean_ctor_get(v_val_43_, 0);
lean_inc(v_fst_48_);
lean_dec(v_val_43_);
v___x_49_ = lean_apply_1(v_h__2_39_, v_fst_48_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___boxed(lean_object* v_n_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_, lean_object* v_h__3_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(v_n_50_, v_motive_51_, v_x_52_, v_h__1_53_, v_h__2_54_, v_h__3_55_);
lean_dec(v_n_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(lean_object* v_cOpt_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
if (lean_obj_tag(v_cOpt_57_) == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v_h__2_59_);
v___x_60_ = lean_box(0);
v___x_61_ = lean_apply_1(v_h__1_58_, v___x_60_);
return v___x_61_;
}
else
{
lean_object* v_val_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_58_);
v_val_62_ = lean_ctor_get(v_cOpt_57_, 0);
lean_inc(v_val_62_);
lean_dec_ref(v_cOpt_57_);
v___x_63_ = lean_apply_1(v_h__2_59_, v_val_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(lean_object* v_n_64_, lean_object* v_motive_65_, lean_object* v_cOpt_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
if (lean_obj_tag(v_cOpt_66_) == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_68_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_67_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_67_);
v_val_71_ = lean_ctor_get(v_cOpt_66_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v_cOpt_66_);
v___x_72_ = lean_apply_1(v_h__2_68_, v_val_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(lean_object* v_n_73_, lean_object* v_motive_74_, lean_object* v_cOpt_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(v_n_73_, v_motive_74_, v_cOpt_75_, v_h__1_76_, v_h__2_77_);
lean_dec(v_n_73_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(lean_object* v_x_79_, lean_object* v_h__1_80_){
_start:
{
lean_object* v_snd_81_; lean_object* v_fst_82_; lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_85_; 
v_snd_81_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_snd_81_);
v_fst_82_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_fst_82_);
lean_dec_ref(v_x_79_);
v_fst_83_ = lean_ctor_get(v_snd_81_, 0);
lean_inc(v_fst_83_);
v_snd_84_ = lean_ctor_get(v_snd_81_, 1);
lean_inc(v_snd_84_);
lean_dec(v_snd_81_);
v___x_85_ = lean_apply_3(v_h__1_80_, v_fst_82_, v_fst_83_, v_snd_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(lean_object* v_n_86_, lean_object* v_motive_87_, lean_object* v_x_88_, lean_object* v_h__1_89_){
_start:
{
lean_object* v_snd_90_; lean_object* v_fst_91_; lean_object* v_fst_92_; lean_object* v_snd_93_; lean_object* v___x_94_; 
v_snd_90_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_snd_90_);
v_fst_91_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_fst_91_);
lean_dec_ref(v_x_88_);
v_fst_92_ = lean_ctor_get(v_snd_90_, 0);
lean_inc(v_fst_92_);
v_snd_93_ = lean_ctor_get(v_snd_90_, 1);
lean_inc(v_snd_93_);
lean_dec(v_snd_90_);
v___x_94_ = lean_apply_3(v_h__1_89_, v_fst_91_, v_fst_92_, v_snd_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___boxed(lean_object* v_n_95_, lean_object* v_motive_96_, lean_object* v_x_97_, lean_object* v_h__1_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(v_n_95_, v_motive_96_, v_x_97_, v_h__1_98_);
lean_dec(v_n_95_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(lean_object* v_x_100_, lean_object* v_h__1_101_){
_start:
{
lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_104_; 
v_fst_102_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_fst_102_);
v_snd_103_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_snd_103_);
lean_dec_ref(v_x_100_);
v___x_104_ = lean_apply_2(v_h__1_101_, v_fst_102_, v_snd_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(lean_object* v_n_105_, lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_h__1_108_){
_start:
{
lean_object* v_fst_109_; lean_object* v_snd_110_; lean_object* v___x_111_; 
v_fst_109_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_fst_109_);
v_snd_110_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_snd_110_);
lean_dec_ref(v_x_107_);
v___x_111_ = lean_apply_2(v_h__1_108_, v_fst_109_, v_snd_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___boxed(lean_object* v_n_112_, lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(v_n_112_, v_motive_113_, v_x_114_, v_h__1_115_);
lean_dec(v_n_112_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___redArg(lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_, lean_object* v_h__3_120_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_h__3_120_);
lean_dec(v_h__2_119_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_1(v_h__1_118_, v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; 
lean_dec(v_h__1_118_);
v_val_123_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_val_123_);
lean_dec_ref(v_x_117_);
if (lean_obj_tag(v_val_123_) == 1)
{
lean_object* v_tail_124_; 
v_tail_124_ = lean_ctor_get(v_val_123_, 1);
if (lean_obj_tag(v_tail_124_) == 0)
{
lean_object* v_head_125_; lean_object* v___x_126_; 
lean_dec(v_h__3_120_);
v_head_125_ = lean_ctor_get(v_val_123_, 0);
lean_inc(v_head_125_);
lean_dec_ref(v_val_123_);
v___x_126_ = lean_apply_3(v_h__2_119_, v_head_125_, lean_box(0), lean_box(0));
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
lean_dec(v_h__2_119_);
v___x_127_ = lean_apply_2(v_h__3_120_, v_val_123_, lean_box(0));
return v___x_127_;
}
}
else
{
lean_object* v___x_128_; 
lean_dec(v_h__2_119_);
v___x_128_ = lean_apply_2(v_h__3_120_, v_val_123_, lean_box(0));
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(lean_object* v_n_129_, lean_object* v_motive_130_, lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_, lean_object* v_h__3_134_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__3_134_);
lean_dec(v_h__2_133_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__1_132_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_val_137_; 
lean_dec(v_h__1_132_);
v_val_137_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_val_137_);
lean_dec_ref(v_x_131_);
if (lean_obj_tag(v_val_137_) == 1)
{
lean_object* v_tail_138_; 
v_tail_138_ = lean_ctor_get(v_val_137_, 1);
if (lean_obj_tag(v_tail_138_) == 0)
{
lean_object* v_head_139_; lean_object* v___x_140_; 
lean_dec(v_h__3_134_);
v_head_139_ = lean_ctor_get(v_val_137_, 0);
lean_inc(v_head_139_);
lean_dec_ref(v_val_137_);
v___x_140_ = lean_apply_3(v_h__2_133_, v_head_139_, lean_box(0), lean_box(0));
return v___x_140_;
}
else
{
lean_object* v___x_141_; 
lean_dec(v_h__2_133_);
v___x_141_ = lean_apply_2(v_h__3_134_, v_val_137_, lean_box(0));
return v___x_141_;
}
}
else
{
lean_object* v___x_142_; 
lean_dec(v_h__2_133_);
v___x_142_ = lean_apply_2(v_h__3_134_, v_val_137_, lean_box(0));
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___boxed(lean_object* v_n_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_, lean_object* v_h__3_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(v_n_143_, v_motive_144_, v_x_145_, v_h__1_146_, v_h__2_147_, v_h__3_148_);
lean_dec(v_n_143_);
return v_res_149_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
