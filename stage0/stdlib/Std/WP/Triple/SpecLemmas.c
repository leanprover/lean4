// Lean compiler output
// Module: Std.WP.Triple.SpecLemmas
// Imports: public import Init.BinderNameHint public import Std.WP.Triple.Monad public import Std.WP.Monad public import Std.Do.Triple.SpecLemmas public import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic public import Init.Data.Slice.Array public import Init.Data.Iterators.Lemmas.Combinators.FilterMap public import Init.Data.Range import Init.Data.Iterators.Lemmas import Init.Data.List.Nat.Range import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.TakeDrop import Init.Data.Nat.Mod import Init.Data.Slice.Lemmas import Init.Omega public import Init.Data.String.Defs public import Init.Data.String.Iterate import Init.Data.String.Lemmas.Splits import Init.Data.String.Termination import Init.Data.String.Lemmas.Iterate public import Std.Internal.ForIn
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
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__string__earlyReturn_match__1__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__string__earlyReturn_match__1__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn_x27__list_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn_x27__list_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__stringSlice__earlyReturn_match__1__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__stringSlice__earlyReturn_match__1__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v_a_13_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_x_10_, 1);
v___x_14_ = lean_apply_1(v_h__1_11_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_a_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__2_12_, v_a_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__string__earlyReturn_match__1__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_19_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_apply_1(v_h__1_18_, v___x_20_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v_val_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_val_22_);
lean_dec_ref_known(v_x_17_, 1);
v___x_23_ = lean_apply_1(v_h__2_19_, v_val_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__string__earlyReturn_match__1__1_splitter(lean_object* v_00_u03b3_24_, lean_object* v_motive_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_28_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_apply_1(v_h__1_27_, v___x_29_);
return v___x_30_;
}
else
{
lean_object* v_val_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_27_);
v_val_31_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_val_31_);
lean_dec_ref_known(v_x_26_, 1);
v___x_32_ = lean_apply_1(v_h__2_28_, v_val_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn_x27__list_match__1_splitter___redArg(lean_object* v_r_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_r_33_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_34_);
v_a_36_ = lean_ctor_get(v_r_33_, 0);
lean_inc(v_a_36_);
lean_dec_ref_known(v_r_33_, 1);
v___x_37_ = lean_apply_1(v_h__2_35_, v_a_36_);
return v___x_37_;
}
else
{
lean_object* v_a_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_35_);
v_a_38_ = lean_ctor_get(v_r_33_, 0);
lean_inc(v_a_38_);
lean_dec_ref_known(v_r_33_, 1);
v___x_39_ = lean_apply_1(v_h__1_34_, v_a_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn_x27__list_match__1_splitter(lean_object* v_00_u03b2_40_, lean_object* v_motive_41_, lean_object* v_r_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
if (lean_obj_tag(v_r_42_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_43_);
v_a_45_ = lean_ctor_get(v_r_42_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v_r_42_, 1);
v___x_46_ = lean_apply_1(v_h__2_44_, v_a_45_);
return v___x_46_;
}
else
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_44_);
v_a_47_ = lean_ctor_get(v_r_42_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v_r_42_, 1);
v___x_48_ = lean_apply_1(v_h__1_43_, v_a_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__stringSlice__earlyReturn_match__1__1_splitter___redArg(lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__2_51_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_apply_1(v_h__1_50_, v___x_52_);
return v___x_53_;
}
else
{
lean_object* v_val_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_50_);
v_val_54_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_val_54_);
lean_dec_ref_known(v_x_49_, 1);
v___x_55_ = lean_apply_1(v_h__2_51_, v_val_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Std_WP_Spec_forIn__stringSlice__earlyReturn_match__1__1_splitter(lean_object* v_00_u03b3_56_, lean_object* v_motive_57_, lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_60_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_apply_1(v_h__1_59_, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v_val_63_; lean_object* v___x_64_; 
lean_dec(v_h__1_59_);
v_val_63_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v_x_58_, 1);
v___x_64_ = lean_apply_1(v_h__2_60_, v_val_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk___redArg(lean_object* v_inv_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_apply_1(v_inv_65_, v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk(lean_object* v_00_u03b1_68_, lean_object* v_00_u03b2_69_, lean_object* v_Pred_70_, lean_object* v_inv_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_apply_1(v_inv_71_, v_a_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg(lean_object* v_inv_74_, uint8_t v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_box(v_a_75_);
v___x_78_ = lean_apply_2(v_inv_74_, v___x_77_, v_a_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg___boxed(lean_object* v_inv_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
uint8_t v_a_9__boxed_82_; lean_object* v_res_83_; 
v_a_9__boxed_82_ = lean_unbox(v_a_80_);
v_res_83_ = l_Std_WP_WhileInvariant_mk___redArg(v_inv_79_, v_a_9__boxed_82_, v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk(lean_object* v_00_u03b1_84_, lean_object* v_Pred_85_, lean_object* v_inv_86_, uint8_t v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(v_a_87_);
v___x_90_ = lean_apply_2(v_inv_86_, v___x_89_, v_a_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___boxed(lean_object* v_00_u03b1_91_, lean_object* v_Pred_92_, lean_object* v_inv_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
uint8_t v_a_19__boxed_96_; lean_object* v_res_97_; 
v_a_19__boxed_96_ = lean_unbox(v_a_94_);
v_res_97_ = l_Std_WP_WhileInvariant_mk(v_00_u03b1_91_, v_Pred_92_, v_inv_93_, v_a_19__boxed_96_, v_a_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(lean_object* v_inv_98_, lean_object* v_a_99_){
_start:
{
if (lean_obj_tag(v_a_99_) == 0)
{
lean_object* v_val_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_val_100_ = lean_ctor_get(v_a_99_, 0);
lean_inc(v_val_100_);
lean_dec_ref_known(v_a_99_, 1);
v___x_101_ = 0;
v___x_102_ = lean_box(v___x_101_);
v___x_103_ = lean_apply_2(v_inv_98_, v___x_102_, v_val_100_);
return v___x_103_;
}
else
{
lean_object* v_val_104_; uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_val_104_ = lean_ctor_get(v_a_99_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v_a_99_, 1);
v___x_105_ = 1;
v___x_106_ = lean_box(v___x_105_);
v___x_107_ = lean_apply_2(v_inv_98_, v___x_106_, v_val_104_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant(lean_object* v_00_u03b1_108_, lean_object* v_Pred_109_, lean_object* v_inv_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(v_inv_110_, v_a_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg___lam__0(lean_object* v_f_113_, lean_object* v_inst_114_, lean_object* v_a_115_, lean_object* v_n_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_apply_1(v_f_113_, v_a_115_);
v___x_118_ = lean_apply_2(v_inst_114_, v___x_117_, v_n_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg(lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_f_121_){
_start:
{
lean_object* v___f_122_; lean_object* v___x_123_; 
v___f_122_ = lean_alloc_closure((void*)(l_Std_WP_Variant_ofMeasure___redArg___lam__0), 4, 2);
lean_closure_set(v___f_122_, 0, v_f_121_);
lean_closure_set(v___f_122_, 1, v_inst_119_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_inst_120_);
lean_ctor_set(v___x_123_, 1, v___f_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure(lean_object* v_Pred_124_, lean_object* v_inst_125_, lean_object* v_00_u03b1_126_, lean_object* v_00_u03b3_127_, lean_object* v_Fun_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_f_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_WP_Variant_ofMeasure___redArg(v_inst_129_, v_inst_130_, v_f_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object* v_____do__lift_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (lean_obj_tag(v_____do__lift_133_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; 
lean_dec(v_h__2_135_);
v_a_136_ = lean_ctor_get(v_____do__lift_133_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v_____do__lift_133_, 1);
v___x_137_ = lean_apply_1(v_h__1_134_, v_a_136_);
return v___x_137_;
}
else
{
lean_object* v_a_138_; lean_object* v___x_139_; 
lean_dec(v_h__1_134_);
v_a_138_ = lean_ctor_get(v_____do__lift_133_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v_____do__lift_133_, 1);
v___x_139_ = lean_apply_1(v_h__2_135_, v_a_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object* v_00_u03b2_140_, lean_object* v_motive_141_, lean_object* v_____do__lift_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
if (lean_obj_tag(v_____do__lift_142_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_144_);
v_a_145_ = lean_ctor_get(v_____do__lift_142_, 0);
lean_inc(v_a_145_);
lean_dec_ref_known(v_____do__lift_142_, 1);
v___x_146_ = lean_apply_1(v_h__1_143_, v_a_145_);
return v___x_146_;
}
else
{
lean_object* v_a_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_143_);
v_a_147_ = lean_ctor_get(v_____do__lift_142_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v_____do__lift_142_, 1);
v___x_148_ = lean_apply_1(v_h__2_144_, v_a_147_);
return v___x_148_;
}
}
}
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Triple_Monad(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Monad(uint8_t builtin);
lean_object* runtime_initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_ForIn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_WP_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Triple_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_WP_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* initialize_Std_WP_Triple_Monad(uint8_t builtin);
lean_object* initialize_Std_WP_Monad(uint8_t builtin);
lean_object* initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
lean_object* initialize_Std_Internal_ForIn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_WP_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Triple_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_WP_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_WP_Triple_SpecLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
