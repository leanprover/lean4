// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Lemmas
// Imports: import Init.Data.Iterators.Lemmas.Consumers.Collect import all Init.Data.Range.Polymorphic.Basic import all Init.Data.Range.Polymorphic.RangeIterator public import Init.Data.Range.Polymorphic.Iterators import all Init.Data.Range.Polymorphic.Iterators import all Init.Data.Iterators.Consumers.Loop import Init.Data.Array.Monadic public import Init.Data.List.Control public import Init.Data.Order.Lemmas import Init.Data.Array.Bootstrap import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Loop import Init.Data.List.Pairwise import Init.Data.Nat.Linear import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__1_11_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref(v_x_10_);
v___x_16_ = lean_apply_1(v_h__2_12_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
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
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_1(v_h__2_19_, v_val_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(lean_object* v_00_u03b1_24_, lean_object* v_motive_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
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
lean_dec_ref(v_x_26_);
v___x_32_ = lean_apply_1(v_h__2_28_, v_val_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
switch(lean_obj_tag(v_x_33_))
{
case 0:
{
lean_object* v_it_37_; lean_object* v_out_38_; lean_object* v___x_39_; 
lean_dec(v_h__3_36_);
lean_dec(v_h__2_35_);
v_it_37_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_it_37_);
v_out_38_ = lean_ctor_get(v_x_33_, 1);
lean_inc(v_out_38_);
lean_dec_ref(v_x_33_);
v___x_39_ = lean_apply_2(v_h__1_34_, v_it_37_, v_out_38_);
return v___x_39_;
}
case 1:
{
lean_object* v_it_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_36_);
lean_dec(v_h__1_34_);
v_it_40_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_it_40_);
lean_dec_ref(v_x_33_);
v___x_41_ = lean_apply_1(v_h__2_35_, v_it_40_);
return v___x_41_;
}
default: 
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_35_);
lean_dec(v_h__1_34_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_apply_1(v_h__3_36_, v___x_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_, lean_object* v_h__3_50_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
lean_object* v_it_51_; lean_object* v_out_52_; lean_object* v___x_53_; 
lean_dec(v_h__3_50_);
lean_dec(v_h__2_49_);
v_it_51_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_it_51_);
v_out_52_ = lean_ctor_get(v_x_47_, 1);
lean_inc(v_out_52_);
lean_dec_ref(v_x_47_);
v___x_53_ = lean_apply_2(v_h__1_48_, v_it_51_, v_out_52_);
return v___x_53_;
}
case 1:
{
lean_object* v_it_54_; lean_object* v___x_55_; 
lean_dec(v_h__3_50_);
lean_dec(v_h__1_48_);
v_it_54_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_it_54_);
lean_dec_ref(v_x_47_);
v___x_55_ = lean_apply_1(v_h__2_49_, v_it_54_);
return v___x_55_;
}
default: 
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_h__2_49_);
lean_dec(v_h__1_48_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_apply_1(v_h__3_50_, v___x_56_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter___redArg(lean_object* v_____do__lift_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_____do__lift_58_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_59_);
v_a_61_ = lean_ctor_get(v_____do__lift_58_, 0);
lean_inc(v_a_61_);
lean_dec_ref(v_____do__lift_58_);
v___x_62_ = lean_apply_1(v_h__2_60_, v_a_61_);
return v___x_62_;
}
else
{
lean_object* v_a_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_60_);
v_a_63_ = lean_ctor_get(v_____do__lift_58_, 0);
lean_inc(v_a_63_);
lean_dec_ref(v_____do__lift_58_);
v___x_64_ = lean_apply_1(v_h__1_59_, v_a_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter(lean_object* v_00_u03b3_65_, lean_object* v_motive_66_, lean_object* v_____do__lift_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_____do__lift_67_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_68_);
v_a_70_ = lean_ctor_get(v_____do__lift_67_, 0);
lean_inc(v_a_70_);
lean_dec_ref(v_____do__lift_67_);
v___x_71_ = lean_apply_1(v_h__2_69_, v_a_70_);
return v___x_71_;
}
else
{
lean_object* v_a_72_; lean_object* v___x_73_; 
lean_dec(v_h__2_69_);
v_a_72_ = lean_ctor_get(v_____do__lift_67_, 0);
lean_inc(v_a_72_);
lean_dec_ref(v_____do__lift_67_);
v___x_73_ = lean_apply_1(v_h__1_68_, v_a_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_, lean_object* v_h__3_77_){
_start:
{
switch(lean_obj_tag(v_x_74_))
{
case 0:
{
lean_object* v_it_78_; lean_object* v_out_79_; lean_object* v___x_80_; 
lean_dec(v_h__3_77_);
lean_dec(v_h__2_76_);
v_it_78_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_it_78_);
v_out_79_ = lean_ctor_get(v_x_74_, 1);
lean_inc(v_out_79_);
lean_dec_ref(v_x_74_);
v___x_80_ = lean_apply_3(v_h__1_75_, v_it_78_, v_out_79_, lean_box(0));
return v___x_80_;
}
case 1:
{
lean_object* v_it_81_; lean_object* v___x_82_; 
lean_dec(v_h__3_77_);
lean_dec(v_h__1_75_);
v_it_81_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_it_81_);
lean_dec_ref(v_x_74_);
v___x_82_ = lean_apply_2(v_h__2_76_, v_it_81_, lean_box(0));
return v___x_82_;
}
default: 
{
lean_object* v___x_83_; 
lean_dec(v_h__2_76_);
lean_dec(v_h__1_75_);
v___x_83_ = lean_apply_1(v_h__3_77_, lean_box(0));
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_inst_86_, lean_object* v_it_87_, lean_object* v_motive_88_, lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_, lean_object* v_h__3_92_){
_start:
{
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
lean_object* v_it_93_; lean_object* v_out_94_; lean_object* v___x_95_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__2_91_);
v_it_93_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_it_93_);
v_out_94_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_out_94_);
lean_dec_ref(v_x_89_);
v___x_95_ = lean_apply_3(v_h__1_90_, v_it_93_, v_out_94_, lean_box(0));
return v___x_95_;
}
case 1:
{
lean_object* v_it_96_; lean_object* v___x_97_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__1_90_);
v_it_96_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_it_96_);
lean_dec_ref(v_x_89_);
v___x_97_ = lean_apply_2(v_h__2_91_, v_it_96_, lean_box(0));
return v___x_97_;
}
default: 
{
lean_object* v___x_98_; 
lean_dec(v_h__2_91_);
lean_dec(v_h__1_90_);
v___x_98_ = lean_apply_1(v_h__3_92_, lean_box(0));
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_inst_101_, lean_object* v_it_102_, lean_object* v_motive_103_, lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_, lean_object* v_h__3_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_99_, v_00_u03b2_100_, v_inst_101_, v_it_102_, v_motive_103_, v_x_104_, v_h__1_105_, v_h__2_106_, v_h__3_107_);
lean_dec(v_it_102_);
lean_dec(v_inst_101_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
if (lean_obj_tag(v_____do__lift_109_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_110_);
v_a_112_ = lean_ctor_get(v_____do__lift_109_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v_____do__lift_109_);
v___x_113_ = lean_apply_1(v_h__2_111_, v_a_112_);
return v___x_113_;
}
else
{
lean_object* v_a_114_; lean_object* v___x_115_; 
lean_dec(v_h__2_111_);
v_a_114_ = lean_ctor_get(v_____do__lift_109_, 0);
lean_inc(v_a_114_);
lean_dec_ref(v_____do__lift_109_);
v___x_115_ = lean_apply_1(v_h__1_110_, v_a_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_116_, lean_object* v_motive_117_, lean_object* v_____do__lift_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
if (lean_obj_tag(v_____do__lift_118_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; 
lean_dec(v_h__1_119_);
v_a_121_ = lean_ctor_get(v_____do__lift_118_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v_____do__lift_118_);
v___x_122_ = lean_apply_1(v_h__2_120_, v_a_121_);
return v___x_122_;
}
else
{
lean_object* v_a_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_120_);
v_a_123_ = lean_ctor_get(v_____do__lift_118_, 0);
lean_inc(v_a_123_);
lean_dec_ref(v_____do__lift_118_);
v___x_124_ = lean_apply_1(v_h__1_119_, v_a_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter___redArg(lean_object* v_x_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v___x_128_; 
lean_dec(v_h__2_127_);
v___x_128_ = lean_apply_1(v_h__1_126_, lean_box(0));
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; 
lean_dec(v_h__1_126_);
v_val_129_ = lean_ctor_get(v_x_125_, 0);
lean_inc(v_val_129_);
lean_dec_ref(v_x_125_);
v___x_130_ = lean_apply_2(v_h__2_127_, v_val_129_, lean_box(0));
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter(lean_object* v_00_u03b1_131_, lean_object* v_motive_132_, lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v___x_136_; 
lean_dec(v_h__2_135_);
v___x_136_ = lean_apply_1(v_h__1_134_, lean_box(0));
return v___x_136_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_138_; 
lean_dec(v_h__1_134_);
v_val_137_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_val_137_);
lean_dec_ref(v_x_133_);
v___x_138_ = lean_apply_2(v_h__2_135_, v_val_137_, lean_box(0));
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; 
lean_dec(v_h__2_141_);
v_a_142_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_a_142_);
lean_dec_ref(v_x_139_);
v___x_143_ = lean_apply_1(v_h__1_140_, v_a_142_);
return v___x_143_;
}
else
{
lean_object* v_a_144_; lean_object* v___x_145_; 
lean_dec(v_h__1_140_);
v_a_144_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_a_144_);
lean_dec_ref(v_x_139_);
v___x_145_ = lean_apply_1(v_h__2_141_, v_a_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_146_, lean_object* v_motive_147_, lean_object* v_x_148_, lean_object* v_h__1_149_, lean_object* v_h__2_150_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; 
lean_dec(v_h__2_150_);
v_a_151_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v_x_148_);
v___x_152_ = lean_apply_1(v_h__1_149_, v_a_151_);
return v___x_152_;
}
else
{
lean_object* v_a_153_; lean_object* v___x_154_; 
lean_dec(v_h__1_149_);
v_a_153_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_a_153_);
lean_dec_ref(v_x_148_);
v___x_154_ = lean_apply_1(v_h__2_150_, v_a_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter___redArg(lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_157_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_apply_1(v_h__1_156_, v___x_158_);
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_161_; 
lean_dec(v_h__1_156_);
v_val_160_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_val_160_);
lean_dec_ref(v_x_155_);
v___x_161_ = lean_apply_1(v_h__2_157_, v_val_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter(lean_object* v_00_u03b1_162_, lean_object* v_motive_163_, lean_object* v_x_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_h__2_166_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_apply_1(v_h__1_165_, v___x_167_);
return v___x_168_;
}
else
{
lean_object* v_val_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_165_);
v_val_169_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_val_169_);
lean_dec_ref(v_x_164_);
v___x_170_ = lean_apply_1(v_h__2_166_, v_val_169_);
return v___x_170_;
}
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
