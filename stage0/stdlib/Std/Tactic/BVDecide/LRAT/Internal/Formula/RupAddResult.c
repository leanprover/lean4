// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas public import Init.GrindInstances.ToInt import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Linear import Init.Data.Nat.Simproc
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; 
v_fst_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_x_2_);
v___x_6_ = lean_apply_3(v_h__1_3_, v_x_1_, v_fst_4_, v_snd_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(lean_object* v_n_7_, lean_object* v_motive_8_, lean_object* v_x_9_, lean_object* v_x_10_, lean_object* v_h__1_11_){
_start:
{
lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v___x_14_; 
v_fst_12_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_fst_12_);
v_snd_13_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_snd_13_);
lean_dec_ref(v_x_10_);
v___x_14_ = lean_apply_3(v_h__1_11_, v_x_9_, v_fst_12_, v_snd_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___boxed(lean_object* v_n_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(v_n_15_, v_motive_16_, v_x_17_, v_x_18_, v_h__1_19_);
lean_dec(v_n_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(lean_object* v_f_21_, lean_object* v_h__1_22_){
_start:
{
lean_object* v_clauses_23_; lean_object* v_rupUnits_24_; lean_object* v_ratUnits_25_; lean_object* v_assignments_26_; lean_object* v___x_27_; 
v_clauses_23_ = lean_ctor_get(v_f_21_, 0);
lean_inc_ref(v_clauses_23_);
v_rupUnits_24_ = lean_ctor_get(v_f_21_, 1);
lean_inc_ref(v_rupUnits_24_);
v_ratUnits_25_ = lean_ctor_get(v_f_21_, 2);
lean_inc_ref(v_ratUnits_25_);
v_assignments_26_ = lean_ctor_get(v_f_21_, 3);
lean_inc_ref(v_assignments_26_);
lean_dec_ref(v_f_21_);
v___x_27_ = lean_apply_4(v_h__1_22_, v_clauses_23_, v_rupUnits_24_, v_ratUnits_25_, v_assignments_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(lean_object* v_n_28_, lean_object* v_motive_29_, lean_object* v_f_30_, lean_object* v_h__1_31_){
_start:
{
lean_object* v_clauses_32_; lean_object* v_rupUnits_33_; lean_object* v_ratUnits_34_; lean_object* v_assignments_35_; lean_object* v___x_36_; 
v_clauses_32_ = lean_ctor_get(v_f_30_, 0);
lean_inc_ref(v_clauses_32_);
v_rupUnits_33_ = lean_ctor_get(v_f_30_, 1);
lean_inc_ref(v_rupUnits_33_);
v_ratUnits_34_ = lean_ctor_get(v_f_30_, 2);
lean_inc_ref(v_ratUnits_34_);
v_assignments_35_ = lean_ctor_get(v_f_30_, 3);
lean_inc_ref(v_assignments_35_);
lean_dec_ref(v_f_30_);
v___x_36_ = lean_apply_4(v_h__1_31_, v_clauses_32_, v_rupUnits_33_, v_ratUnits_34_, v_assignments_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(lean_object* v_n_37_, lean_object* v_motive_38_, lean_object* v_f_39_, lean_object* v_h__1_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_37_, v_motive_38_, v_f_39_, v_h__1_40_);
lean_dec(v_n_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(lean_object* v_x_42_, lean_object* v_h__1_43_){
_start:
{
lean_object* v_snd_44_; lean_object* v_snd_45_; lean_object* v_fst_46_; lean_object* v_fst_47_; lean_object* v_fst_48_; lean_object* v_snd_49_; lean_object* v___x_50_; 
v_snd_44_ = lean_ctor_get(v_x_42_, 1);
lean_inc(v_snd_44_);
v_snd_45_ = lean_ctor_get(v_snd_44_, 1);
lean_inc(v_snd_45_);
v_fst_46_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_fst_46_);
lean_dec_ref(v_x_42_);
v_fst_47_ = lean_ctor_get(v_snd_44_, 0);
lean_inc(v_fst_47_);
lean_dec(v_snd_44_);
v_fst_48_ = lean_ctor_get(v_snd_45_, 0);
lean_inc(v_fst_48_);
v_snd_49_ = lean_ctor_get(v_snd_45_, 1);
lean_inc(v_snd_49_);
lean_dec(v_snd_45_);
v___x_50_ = lean_apply_4(v_h__1_43_, v_fst_46_, v_fst_47_, v_fst_48_, v_snd_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(lean_object* v_n_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_h__1_54_){
_start:
{
lean_object* v_snd_55_; lean_object* v_snd_56_; lean_object* v_fst_57_; lean_object* v_fst_58_; lean_object* v_fst_59_; lean_object* v_snd_60_; lean_object* v___x_61_; 
v_snd_55_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_snd_55_);
v_snd_56_ = lean_ctor_get(v_snd_55_, 1);
lean_inc(v_snd_56_);
v_fst_57_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_fst_57_);
lean_dec_ref(v_x_53_);
v_fst_58_ = lean_ctor_get(v_snd_55_, 0);
lean_inc(v_fst_58_);
lean_dec(v_snd_55_);
v_fst_59_ = lean_ctor_get(v_snd_56_, 0);
lean_inc(v_fst_59_);
v_snd_60_ = lean_ctor_get(v_snd_56_, 1);
lean_inc(v_snd_60_);
lean_dec(v_snd_56_);
v___x_61_ = lean_apply_4(v_h__1_54_, v_fst_57_, v_fst_58_, v_fst_59_, v_snd_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___boxed(lean_object* v_n_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_h__1_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(v_n_62_, v_motive_63_, v_x_64_, v_h__1_65_);
lean_dec(v_n_62_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_, lean_object* v_h__3_70_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__2_69_);
lean_dec(v_h__1_68_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__3_70_, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; 
lean_dec(v_h__3_70_);
v_val_73_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_val_73_);
lean_dec_ref(v_x_67_);
if (lean_obj_tag(v_val_73_) == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__1_68_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__2_69_, v___x_74_);
return v___x_75_;
}
else
{
lean_object* v_val_76_; lean_object* v___x_77_; 
lean_dec(v_h__2_69_);
v_val_76_ = lean_ctor_get(v_val_73_, 0);
lean_inc(v_val_76_);
lean_dec_ref(v_val_73_);
v___x_77_ = lean_apply_1(v_h__1_68_, v_val_76_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object* v_n_78_, lean_object* v_motive_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_, lean_object* v_h__3_83_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_82_);
lean_dec(v_h__1_81_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__3_83_, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; 
lean_dec(v_h__3_83_);
v_val_86_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_val_86_);
lean_dec_ref(v_x_80_);
if (lean_obj_tag(v_val_86_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_h__1_81_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_apply_1(v_h__2_82_, v___x_87_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_82_);
v_val_89_ = lean_ctor_get(v_val_86_, 0);
lean_inc(v_val_89_);
lean_dec_ref(v_val_86_);
v___x_90_ = lean_apply_1(v_h__1_81_, v_val_89_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object* v_n_91_, lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_91_, v_motive_92_, v_x_93_, v_h__1_94_, v_h__2_95_, v_h__3_96_);
lean_dec(v_n_91_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_, lean_object* v_h__3_101_, lean_object* v_h__4_102_){
_start:
{
switch(lean_obj_tag(v_x_98_))
{
case 0:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__1_99_, v___x_103_);
return v___x_104_;
}
case 1:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__4_102_);
lean_dec(v_h__3_101_);
lean_dec(v_h__1_99_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__2_100_, v___x_105_);
return v___x_106_;
}
case 2:
{
lean_object* v_l_107_; lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v___x_110_; 
lean_dec(v_h__4_102_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v_l_107_ = lean_ctor_get(v_x_98_, 0);
lean_inc_ref(v_l_107_);
lean_dec_ref(v_x_98_);
v_fst_108_ = lean_ctor_get(v_l_107_, 0);
lean_inc(v_fst_108_);
v_snd_109_ = lean_ctor_get(v_l_107_, 1);
lean_inc(v_snd_109_);
lean_dec_ref(v_l_107_);
v___x_110_ = lean_apply_2(v_h__3_101_, v_fst_108_, v_snd_109_);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_1(v_h__4_102_, v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object* v_n_113_, lean_object* v_motive_114_, lean_object* v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_, lean_object* v_h__3_118_, lean_object* v_h__4_119_){
_start:
{
switch(lean_obj_tag(v_x_115_))
{
case 0:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__4_119_);
lean_dec(v_h__3_118_);
lean_dec(v_h__2_117_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__1_116_, v___x_120_);
return v___x_121_;
}
case 1:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_h__4_119_);
lean_dec(v_h__3_118_);
lean_dec(v_h__1_116_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_1(v_h__2_117_, v___x_122_);
return v___x_123_;
}
case 2:
{
lean_object* v_l_124_; lean_object* v_fst_125_; lean_object* v_snd_126_; lean_object* v___x_127_; 
lean_dec(v_h__4_119_);
lean_dec(v_h__2_117_);
lean_dec(v_h__1_116_);
v_l_124_ = lean_ctor_get(v_x_115_, 0);
lean_inc_ref(v_l_124_);
lean_dec_ref(v_x_115_);
v_fst_125_ = lean_ctor_get(v_l_124_, 0);
lean_inc(v_fst_125_);
v_snd_126_ = lean_ctor_get(v_l_124_, 1);
lean_inc(v_snd_126_);
lean_dec_ref(v_l_124_);
v___x_127_ = lean_apply_2(v_h__3_118_, v_fst_125_, v_snd_126_);
return v___x_127_;
}
default: 
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__3_118_);
lean_dec(v_h__2_117_);
lean_dec(v_h__1_116_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__4_119_, v___x_128_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object* v_n_130_, lean_object* v_motive_131_, lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_, lean_object* v_h__3_135_, lean_object* v_h__4_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_130_, v_motive_131_, v_x_132_, v_h__1_133_, v_h__2_134_, v_h__3_135_, v_h__4_136_);
lean_dec(v_n_130_);
return v_res_137_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
