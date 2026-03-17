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
lean_object* v___x_12_; 
v___x_12_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(v_f_10_, v_h__1_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object* v_n_13_, lean_object* v_motive_14_, lean_object* v_f_15_, lean_object* v_h__1_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_13_, v_motive_14_, v_f_15_, v_h__1_16_);
lean_dec(v_n_13_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_, lean_object* v_h__3_21_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_21_);
lean_dec(v_h__2_20_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_19_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v_val_24_; lean_object* v_snd_25_; uint8_t v___x_26_; 
lean_dec(v_h__1_19_);
v_val_24_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_val_24_);
lean_dec_ref(v_x_18_);
v_snd_25_ = lean_ctor_get(v_val_24_, 1);
v___x_26_ = lean_unbox(v_snd_25_);
if (v___x_26_ == 0)
{
lean_object* v_fst_27_; lean_object* v___x_28_; 
lean_dec(v_h__2_20_);
v_fst_27_ = lean_ctor_get(v_val_24_, 0);
lean_inc(v_fst_27_);
lean_dec(v_val_24_);
v___x_28_ = lean_apply_1(v_h__3_21_, v_fst_27_);
return v___x_28_;
}
else
{
lean_object* v_fst_29_; lean_object* v___x_30_; 
lean_dec(v_h__3_21_);
v_fst_29_ = lean_ctor_get(v_val_24_, 0);
lean_inc(v_fst_29_);
lean_dec(v_val_24_);
v___x_30_ = lean_apply_1(v_h__2_20_, v_fst_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(lean_object* v_n_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___redArg(v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___boxed(lean_object* v_n_38_, lean_object* v_motive_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_, lean_object* v_h__3_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(v_n_38_, v_motive_39_, v_x_40_, v_h__1_41_, v_h__2_42_, v_h__3_43_);
lean_dec(v_n_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(lean_object* v_cOpt_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_cOpt_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_46_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v_val_50_ = lean_ctor_get(v_cOpt_45_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v_cOpt_45_);
v___x_51_ = lean_apply_1(v_h__2_47_, v_val_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(lean_object* v_n_52_, lean_object* v_motive_53_, lean_object* v_cOpt_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(v_cOpt_54_, v_h__1_55_, v_h__2_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(lean_object* v_n_58_, lean_object* v_motive_59_, lean_object* v_cOpt_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(v_n_58_, v_motive_59_, v_cOpt_60_, v_h__1_61_, v_h__2_62_);
lean_dec(v_n_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(lean_object* v_x_64_, lean_object* v_h__1_65_){
_start:
{
lean_object* v_snd_66_; lean_object* v_fst_67_; lean_object* v_fst_68_; lean_object* v_snd_69_; lean_object* v___x_70_; 
v_snd_66_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_snd_66_);
v_fst_67_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_fst_67_);
lean_dec_ref(v_x_64_);
v_fst_68_ = lean_ctor_get(v_snd_66_, 0);
lean_inc(v_fst_68_);
v_snd_69_ = lean_ctor_get(v_snd_66_, 1);
lean_inc(v_snd_69_);
lean_dec(v_snd_66_);
v___x_70_ = lean_apply_3(v_h__1_65_, v_fst_67_, v_fst_68_, v_snd_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(lean_object* v_n_71_, lean_object* v_motive_72_, lean_object* v_x_73_, lean_object* v_h__1_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(v_x_73_, v_h__1_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___boxed(lean_object* v_n_76_, lean_object* v_motive_77_, lean_object* v_x_78_, lean_object* v_h__1_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(v_n_76_, v_motive_77_, v_x_78_, v_h__1_79_);
lean_dec(v_n_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(lean_object* v_x_81_, lean_object* v_h__1_82_){
_start:
{
lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_85_; 
v_fst_83_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_fst_83_);
v_snd_84_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_snd_84_);
lean_dec_ref(v_x_81_);
v___x_85_ = lean_apply_2(v_h__1_82_, v_fst_83_, v_snd_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(lean_object* v_n_86_, lean_object* v_motive_87_, lean_object* v_x_88_, lean_object* v_h__1_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(v_x_88_, v_h__1_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___boxed(lean_object* v_n_91_, lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_h__1_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(v_n_91_, v_motive_92_, v_x_93_, v_h__1_94_);
lean_dec(v_n_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___redArg(lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_h__3_99_);
lean_dec(v_h__2_98_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_1(v_h__1_97_, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v_val_102_; 
lean_dec(v_h__1_97_);
v_val_102_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_val_102_);
lean_dec_ref(v_x_96_);
if (lean_obj_tag(v_val_102_) == 1)
{
lean_object* v_tail_103_; 
v_tail_103_ = lean_ctor_get(v_val_102_, 1);
if (lean_obj_tag(v_tail_103_) == 0)
{
lean_object* v_head_104_; lean_object* v___x_105_; 
lean_dec(v_h__3_99_);
v_head_104_ = lean_ctor_get(v_val_102_, 0);
lean_inc(v_head_104_);
lean_dec_ref(v_val_102_);
v___x_105_ = lean_apply_3(v_h__2_98_, v_head_104_, lean_box(0), lean_box(0));
return v___x_105_;
}
else
{
lean_object* v___x_106_; 
lean_dec(v_h__2_98_);
v___x_106_ = lean_apply_2(v_h__3_99_, v_val_102_, lean_box(0));
return v___x_106_;
}
}
else
{
lean_object* v___x_107_; 
lean_dec(v_h__2_98_);
v___x_107_ = lean_apply_2(v_h__3_99_, v_val_102_, lean_box(0));
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(lean_object* v_n_108_, lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__3_113_);
lean_dec(v_h__2_112_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__1_111_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v_val_116_; 
lean_dec(v_h__1_111_);
v_val_116_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_116_);
lean_dec_ref(v_x_110_);
if (lean_obj_tag(v_val_116_) == 1)
{
lean_object* v_tail_117_; 
v_tail_117_ = lean_ctor_get(v_val_116_, 1);
if (lean_obj_tag(v_tail_117_) == 0)
{
lean_object* v_head_118_; lean_object* v___x_119_; 
lean_dec(v_h__3_113_);
v_head_118_ = lean_ctor_get(v_val_116_, 0);
lean_inc(v_head_118_);
lean_dec_ref(v_val_116_);
v___x_119_ = lean_apply_3(v_h__2_112_, v_head_118_, lean_box(0), lean_box(0));
return v___x_119_;
}
else
{
lean_object* v___x_120_; 
lean_dec(v_h__2_112_);
v___x_120_ = lean_apply_2(v_h__3_113_, v_val_116_, lean_box(0));
return v___x_120_;
}
}
else
{
lean_object* v___x_121_; 
lean_dec(v_h__2_112_);
v___x_121_ = lean_apply_2(v_h__3_113_, v_val_116_, lean_box(0));
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___boxed(lean_object* v_n_122_, lean_object* v_motive_123_, lean_object* v_x_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_, lean_object* v_h__3_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(v_n_122_, v_motive_123_, v_x_124_, v_h__1_125_, v_h__2_126_, v_h__3_127_);
lean_dec(v_n_122_);
return v_res_128_;
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
