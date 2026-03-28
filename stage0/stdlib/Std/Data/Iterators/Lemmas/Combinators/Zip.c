// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Zip
// Imports: public import Std.Data.Iterators.Combinators.Zip public import Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip public import Init.Data.Iterators.Lemmas.Combinators.Take import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Access import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.List.ToArray import Init.Data.List.Zip
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(lean_object* v_memo_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_memo_1_) == 0)
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
v_val_6_ = lean_ctor_get(v_memo_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_memo_1_);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(lean_object* v_00_u03b1_u2081_8_, lean_object* v_00_u03b2_u2081_9_, lean_object* v_m_10_, lean_object* v_inst_11_, lean_object* v_motive_12_, lean_object* v_memo_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_){
_start:
{
if (lean_obj_tag(v_memo_13_) == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_15_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_apply_1(v_h__1_14_, v___x_16_);
return v___x_17_;
}
else
{
lean_object* v_val_18_; lean_object* v___x_19_; 
lean_dec(v_h__1_14_);
v_val_18_ = lean_ctor_get(v_memo_13_, 0);
lean_inc(v_val_18_);
lean_dec_ref(v_memo_13_);
v___x_19_ = lean_apply_1(v_h__2_15_, v_val_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(lean_object* v_00_u03b1_u2081_20_, lean_object* v_00_u03b2_u2081_21_, lean_object* v_m_22_, lean_object* v_inst_23_, lean_object* v_motive_24_, lean_object* v_memo_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_20_, v_00_u03b2_u2081_21_, v_m_22_, v_inst_23_, v_motive_24_, v_memo_25_, v_h__1_26_, v_h__2_27_);
lean_dec(v_inst_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_, lean_object* v_h__3_32_){
_start:
{
switch(lean_obj_tag(v_x_29_))
{
case 0:
{
lean_object* v_it_33_; lean_object* v_out_34_; lean_object* v___x_35_; 
lean_dec(v_h__3_32_);
lean_dec(v_h__2_31_);
v_it_33_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_it_33_);
v_out_34_ = lean_ctor_get(v_x_29_, 1);
lean_inc(v_out_34_);
lean_dec_ref(v_x_29_);
v___x_35_ = lean_apply_3(v_h__1_30_, v_it_33_, v_out_34_, lean_box(0));
return v___x_35_;
}
case 1:
{
lean_object* v_it_36_; lean_object* v___x_37_; 
lean_dec(v_h__3_32_);
lean_dec(v_h__1_30_);
v_it_36_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_it_36_);
lean_dec_ref(v_x_29_);
v___x_37_ = lean_apply_2(v_h__2_31_, v_it_36_, lean_box(0));
return v___x_37_;
}
default: 
{
lean_object* v___x_38_; 
lean_dec(v_h__2_31_);
lean_dec(v_h__1_30_);
v___x_38_ = lean_apply_1(v_h__3_32_, lean_box(0));
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(lean_object* v_00_u03b1_u2081_39_, lean_object* v_00_u03b2_u2081_40_, lean_object* v_m_41_, lean_object* v_inst_42_, lean_object* v_it_u2081_43_, lean_object* v_motive_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_, lean_object* v_h__3_48_){
_start:
{
switch(lean_obj_tag(v_x_45_))
{
case 0:
{
lean_object* v_it_49_; lean_object* v_out_50_; lean_object* v___x_51_; 
lean_dec(v_h__3_48_);
lean_dec(v_h__2_47_);
v_it_49_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_it_49_);
v_out_50_ = lean_ctor_get(v_x_45_, 1);
lean_inc(v_out_50_);
lean_dec_ref(v_x_45_);
v___x_51_ = lean_apply_3(v_h__1_46_, v_it_49_, v_out_50_, lean_box(0));
return v___x_51_;
}
case 1:
{
lean_object* v_it_52_; lean_object* v___x_53_; 
lean_dec(v_h__3_48_);
lean_dec(v_h__1_46_);
v_it_52_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_it_52_);
lean_dec_ref(v_x_45_);
v___x_53_ = lean_apply_2(v_h__2_47_, v_it_52_, lean_box(0));
return v___x_53_;
}
default: 
{
lean_object* v___x_54_; 
lean_dec(v_h__2_47_);
lean_dec(v_h__1_46_);
v___x_54_ = lean_apply_1(v_h__3_48_, lean_box(0));
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(lean_object* v_00_u03b1_u2081_55_, lean_object* v_00_u03b2_u2081_56_, lean_object* v_m_57_, lean_object* v_inst_58_, lean_object* v_it_u2081_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_55_, v_00_u03b2_u2081_56_, v_m_57_, v_inst_58_, v_it_u2081_59_, v_motive_60_, v_x_61_, v_h__1_62_, v_h__2_63_, v_h__3_64_);
lean_dec(v_it_u2081_59_);
lean_dec(v_inst_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(lean_object* v_memo_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
if (lean_obj_tag(v_memo_66_) == 0)
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
v_val_71_ = lean_ctor_get(v_memo_66_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v_memo_66_);
v___x_72_ = lean_apply_1(v_h__2_68_, v_val_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(lean_object* v_00_u03b1_u2081_73_, lean_object* v_00_u03b2_u2081_74_, lean_object* v_inst_75_, lean_object* v_motive_76_, lean_object* v_memo_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
if (lean_obj_tag(v_memo_77_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_79_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__1_78_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_83_; 
lean_dec(v_h__1_78_);
v_val_82_ = lean_ctor_get(v_memo_77_, 0);
lean_inc(v_val_82_);
lean_dec_ref(v_memo_77_);
v___x_83_ = lean_apply_1(v_h__2_79_, v_val_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___boxed(lean_object* v_00_u03b1_u2081_84_, lean_object* v_00_u03b2_u2081_85_, lean_object* v_inst_86_, lean_object* v_motive_87_, lean_object* v_memo_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_84_, v_00_u03b2_u2081_85_, v_inst_86_, v_motive_87_, v_memo_88_, v_h__1_89_, v_h__2_90_);
lean_dec(v_inst_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_){
_start:
{
switch(lean_obj_tag(v_x_92_))
{
case 0:
{
lean_object* v_it_96_; lean_object* v_out_97_; lean_object* v___x_98_; 
lean_dec(v_h__3_95_);
lean_dec(v_h__2_94_);
v_it_96_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_it_96_);
v_out_97_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_out_97_);
lean_dec_ref(v_x_92_);
v___x_98_ = lean_apply_3(v_h__1_93_, v_it_96_, v_out_97_, lean_box(0));
return v___x_98_;
}
case 1:
{
lean_object* v_it_99_; lean_object* v___x_100_; 
lean_dec(v_h__3_95_);
lean_dec(v_h__1_93_);
v_it_99_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_it_99_);
lean_dec_ref(v_x_92_);
v___x_100_ = lean_apply_2(v_h__2_94_, v_it_99_, lean_box(0));
return v___x_100_;
}
default: 
{
lean_object* v___x_101_; 
lean_dec(v_h__2_94_);
lean_dec(v_h__1_93_);
v___x_101_ = lean_apply_1(v_h__3_95_, lean_box(0));
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(lean_object* v_00_u03b1_u2081_102_, lean_object* v_00_u03b2_u2081_103_, lean_object* v_inst_104_, lean_object* v_it_u2081_105_, lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_, lean_object* v_h__3_110_){
_start:
{
switch(lean_obj_tag(v_x_107_))
{
case 0:
{
lean_object* v_it_111_; lean_object* v_out_112_; lean_object* v___x_113_; 
lean_dec(v_h__3_110_);
lean_dec(v_h__2_109_);
v_it_111_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_it_111_);
v_out_112_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_out_112_);
lean_dec_ref(v_x_107_);
v___x_113_ = lean_apply_3(v_h__1_108_, v_it_111_, v_out_112_, lean_box(0));
return v___x_113_;
}
case 1:
{
lean_object* v_it_114_; lean_object* v___x_115_; 
lean_dec(v_h__3_110_);
lean_dec(v_h__1_108_);
v_it_114_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_it_114_);
lean_dec_ref(v_x_107_);
v___x_115_ = lean_apply_2(v_h__2_109_, v_it_114_, lean_box(0));
return v___x_115_;
}
default: 
{
lean_object* v___x_116_; 
lean_dec(v_h__2_109_);
lean_dec(v_h__1_108_);
v___x_116_ = lean_apply_1(v_h__3_110_, lean_box(0));
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___boxed(lean_object* v_00_u03b1_u2081_117_, lean_object* v_00_u03b2_u2081_118_, lean_object* v_inst_119_, lean_object* v_it_u2081_120_, lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_, lean_object* v_h__3_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_117_, v_00_u03b2_u2081_118_, v_inst_119_, v_it_u2081_120_, v_motive_121_, v_x_122_, v_h__1_123_, v_h__2_124_, v_h__3_125_);
lean_dec(v_it_u2081_120_);
lean_dec(v_inst_119_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_, lean_object* v_h__3_130_){
_start:
{
switch(lean_obj_tag(v_x_127_))
{
case 0:
{
lean_object* v_it_131_; lean_object* v_out_132_; lean_object* v___x_133_; 
lean_dec(v_h__3_130_);
lean_dec(v_h__2_129_);
v_it_131_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_it_131_);
v_out_132_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_out_132_);
lean_dec_ref(v_x_127_);
v___x_133_ = lean_apply_3(v_h__1_128_, v_it_131_, v_out_132_, lean_box(0));
return v___x_133_;
}
case 1:
{
lean_object* v_it_134_; lean_object* v___x_135_; 
lean_dec(v_h__3_130_);
lean_dec(v_h__1_128_);
v_it_134_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_it_134_);
lean_dec_ref(v_x_127_);
v___x_135_ = lean_apply_2(v_h__2_129_, v_it_134_, lean_box(0));
return v___x_135_;
}
default: 
{
lean_object* v___x_136_; 
lean_dec(v_h__2_129_);
lean_dec(v_h__1_128_);
v___x_136_ = lean_apply_1(v_h__3_130_, lean_box(0));
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v_inst_139_, lean_object* v_it_140_, lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_, lean_object* v_h__3_145_){
_start:
{
switch(lean_obj_tag(v_x_142_))
{
case 0:
{
lean_object* v_it_146_; lean_object* v_out_147_; lean_object* v___x_148_; 
lean_dec(v_h__3_145_);
lean_dec(v_h__2_144_);
v_it_146_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_it_146_);
v_out_147_ = lean_ctor_get(v_x_142_, 1);
lean_inc(v_out_147_);
lean_dec_ref(v_x_142_);
v___x_148_ = lean_apply_3(v_h__1_143_, v_it_146_, v_out_147_, lean_box(0));
return v___x_148_;
}
case 1:
{
lean_object* v_it_149_; lean_object* v___x_150_; 
lean_dec(v_h__3_145_);
lean_dec(v_h__1_143_);
v_it_149_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_it_149_);
lean_dec_ref(v_x_142_);
v___x_150_ = lean_apply_2(v_h__2_144_, v_it_149_, lean_box(0));
return v___x_150_;
}
default: 
{
lean_object* v___x_151_; 
lean_dec(v_h__2_144_);
lean_dec(v_h__1_143_);
v___x_151_ = lean_apply_1(v_h__3_145_, lean_box(0));
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_inst_154_, lean_object* v_it_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_, lean_object* v_h__3_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_152_, v_00_u03b2_153_, v_inst_154_, v_it_155_, v_motive_156_, v_x_157_, v_h__1_158_, v_h__2_159_, v_h__3_160_);
lean_dec(v_it_155_);
lean_dec(v_inst_154_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object* v_n_162_, lean_object* v_recur_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_){
_start:
{
lean_object* v_zero_166_; uint8_t v_isZero_167_; 
v_zero_166_ = lean_unsigned_to_nat(0u);
v_isZero_167_ = lean_nat_dec_eq(v_n_162_, v_zero_166_);
if (v_isZero_167_ == 1)
{
lean_object* v___x_168_; 
lean_dec(v_h__2_165_);
v___x_168_ = lean_apply_1(v_h__1_164_, v_recur_163_);
return v___x_168_;
}
else
{
lean_object* v_one_169_; lean_object* v_n_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_164_);
v_one_169_ = lean_unsigned_to_nat(1u);
v_n_170_ = lean_nat_sub(v_n_162_, v_one_169_);
v___x_171_ = lean_apply_2(v_h__2_165_, v_n_170_, v_recur_163_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object* v_n_172_, lean_object* v_recur_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_172_, v_recur_173_, v_h__1_174_, v_h__2_175_);
lean_dec(v_n_172_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_inst_179_, lean_object* v_it_180_, lean_object* v_motive_181_, lean_object* v_n_182_, lean_object* v_recur_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
lean_object* v_zero_186_; uint8_t v_isZero_187_; 
v_zero_186_ = lean_unsigned_to_nat(0u);
v_isZero_187_ = lean_nat_dec_eq(v_n_182_, v_zero_186_);
if (v_isZero_187_ == 1)
{
lean_object* v___x_188_; 
lean_dec(v_h__2_185_);
v___x_188_ = lean_apply_1(v_h__1_184_, v_recur_183_);
return v___x_188_;
}
else
{
lean_object* v_one_189_; lean_object* v_n_190_; lean_object* v___x_191_; 
lean_dec(v_h__1_184_);
v_one_189_ = lean_unsigned_to_nat(1u);
v_n_190_ = lean_nat_sub(v_n_182_, v_one_189_);
v___x_191_ = lean_apply_2(v_h__2_185_, v_n_190_, v_recur_183_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_inst_194_, lean_object* v_it_195_, lean_object* v_motive_196_, lean_object* v_n_197_, lean_object* v_recur_198_, lean_object* v_h__1_199_, lean_object* v_h__2_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_192_, v_00_u03b2_193_, v_inst_194_, v_it_195_, v_motive_196_, v_n_197_, v_recur_198_, v_h__1_199_, v_h__2_200_);
lean_dec(v_n_197_);
lean_dec(v_it_195_);
lean_dec(v_inst_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(lean_object* v_n_202_, lean_object* v_h__1_203_, lean_object* v_h__2_204_){
_start:
{
lean_object* v_zero_205_; uint8_t v_isZero_206_; 
v_zero_205_ = lean_unsigned_to_nat(0u);
v_isZero_206_ = lean_nat_dec_eq(v_n_202_, v_zero_205_);
if (v_isZero_206_ == 1)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_h__2_204_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_1(v_h__1_203_, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v_one_209_; lean_object* v_n_210_; lean_object* v___x_211_; 
lean_dec(v_h__1_203_);
v_one_209_ = lean_unsigned_to_nat(1u);
v_n_210_ = lean_nat_sub(v_n_202_, v_one_209_);
v___x_211_ = lean_apply_1(v_h__2_204_, v_n_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg___boxed(lean_object* v_n_212_, lean_object* v_h__1_213_, lean_object* v_h__2_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(v_n_212_, v_h__1_213_, v_h__2_214_);
lean_dec(v_n_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(lean_object* v_motive_216_, lean_object* v_n_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_){
_start:
{
lean_object* v_zero_220_; uint8_t v_isZero_221_; 
v_zero_220_ = lean_unsigned_to_nat(0u);
v_isZero_221_ = lean_nat_dec_eq(v_n_217_, v_zero_220_);
if (v_isZero_221_ == 1)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v_h__2_219_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_apply_1(v_h__1_218_, v___x_222_);
return v___x_223_;
}
else
{
lean_object* v_one_224_; lean_object* v_n_225_; lean_object* v___x_226_; 
lean_dec(v_h__1_218_);
v_one_224_ = lean_unsigned_to_nat(1u);
v_n_225_ = lean_nat_sub(v_n_217_, v_one_224_);
v___x_226_ = lean_apply_1(v_h__2_219_, v_n_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___boxed(lean_object* v_motive_227_, lean_object* v_n_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(v_motive_227_, v_n_228_, v_h__1_229_, v_h__2_230_);
lean_dec(v_n_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object* v_n_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_){
_start:
{
lean_object* v_zero_235_; uint8_t v_isZero_236_; 
v_zero_235_ = lean_unsigned_to_nat(0u);
v_isZero_236_ = lean_nat_dec_eq(v_n_232_, v_zero_235_);
if (v_isZero_236_ == 1)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_h__2_234_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_apply_1(v_h__1_233_, v___x_237_);
return v___x_238_;
}
else
{
lean_object* v_one_239_; lean_object* v_n_240_; lean_object* v___x_241_; 
lean_dec(v_h__1_233_);
v_one_239_ = lean_unsigned_to_nat(1u);
v_n_240_ = lean_nat_sub(v_n_232_, v_one_239_);
v___x_241_ = lean_apply_1(v_h__2_234_, v_n_240_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object* v_n_242_, lean_object* v_h__1_243_, lean_object* v_h__2_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_242_, v_h__1_243_, v_h__2_244_);
lean_dec(v_n_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object* v_motive_246_, lean_object* v_n_247_, lean_object* v_h__1_248_, lean_object* v_h__2_249_){
_start:
{
lean_object* v_zero_250_; uint8_t v_isZero_251_; 
v_zero_250_ = lean_unsigned_to_nat(0u);
v_isZero_251_ = lean_nat_dec_eq(v_n_247_, v_zero_250_);
if (v_isZero_251_ == 1)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v_h__2_249_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_apply_1(v_h__1_248_, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v_one_254_; lean_object* v_n_255_; lean_object* v___x_256_; 
lean_dec(v_h__1_248_);
v_one_254_ = lean_unsigned_to_nat(1u);
v_n_255_ = lean_nat_sub(v_n_247_, v_one_254_);
v___x_256_ = lean_apply_1(v_h__2_249_, v_n_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object* v_motive_257_, lean_object* v_n_258_, lean_object* v_h__1_259_, lean_object* v_h__2_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_257_, v_n_258_, v_h__1_259_, v_h__2_260_);
lean_dec(v_n_258_);
return v_res_261_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
}
#ifdef __cplusplus
}
#endif
