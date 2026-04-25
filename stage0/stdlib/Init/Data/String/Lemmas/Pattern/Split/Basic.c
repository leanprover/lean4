// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Split.Basic
// Imports: public import Init.Data.String.Lemmas.Pattern.Basic public import Init.Data.String.Slice public import Init.Data.String.Search import all Init.Data.String.Slice import all Init.Data.String.Search import Init.Data.Option.Lemmas import Init.Data.String.Termination import Init.Data.String.Lemmas.Order import Init.ByCases import Init.Data.Order.Lemmas import Init.Data.String.OrderInstances import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.Iterators.Lemmas.Combinators.FilterMap import Init.Data.String.Lemmas.IsEmpty
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_apply_1(v_h__2_3_, lean_box(0));
return v___x_4_;
}
else
{
lean_object* v_val_5_; lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v_val_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v_x_1_);
v___x_6_ = lean_apply_2(v_h__1_2_, v_val_5_, lean_box(0));
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter(lean_object* v_s_7_, lean_object* v_motive_8_, lean_object* v_x_9_, lean_object* v_h__1_10_, lean_object* v_h__2_11_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v___x_12_; 
lean_dec(v_h__1_10_);
v___x_12_ = lean_apply_1(v_h__2_11_, lean_box(0));
return v___x_12_;
}
else
{
lean_object* v_val_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_11_);
v_val_13_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_val_13_);
lean_dec_ref(v_x_9_);
v___x_14_ = lean_apply_2(v_h__1_10_, v_val_13_, lean_box(0));
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___boxed(lean_object* v_s_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter(v_s_15_, v_motive_16_, v_x_17_, v_h__1_18_, v_h__2_19_);
lean_dec_ref(v_s_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(lean_object* v_s_21_, lean_object* v_currPos_22_, lean_object* v_l_23_){
_start:
{
if (lean_obj_tag(v_l_23_) == 0)
{
lean_object* v_startInclusive_24_; lean_object* v_endExclusive_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_startInclusive_24_ = lean_ctor_get(v_s_21_, 1);
v_endExclusive_25_ = lean_ctor_get(v_s_21_, 2);
v___x_26_ = lean_nat_sub(v_endExclusive_25_, v_startInclusive_24_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v_currPos_22_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
return v___x_29_;
}
else
{
lean_object* v_head_30_; 
v_head_30_ = lean_ctor_get(v_l_23_, 0);
if (lean_obj_tag(v_head_30_) == 0)
{
lean_object* v_tail_31_; 
v_tail_31_ = lean_ctor_get(v_l_23_, 1);
lean_inc(v_tail_31_);
lean_dec_ref(v_l_23_);
v_l_23_ = v_tail_31_;
goto _start;
}
else
{
lean_object* v_tail_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_44_; 
lean_inc_ref(v_head_30_);
v_tail_33_ = lean_ctor_get(v_l_23_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v_l_23_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; 
v_unused_45_ = lean_ctor_get(v_l_23_, 0);
lean_dec(v_unused_45_);
v___x_35_ = v_l_23_;
v_isShared_36_ = v_isSharedCheck_44_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_tail_33_);
lean_dec(v_l_23_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_44_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v_startPos_37_; lean_object* v_endPos_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v_startPos_37_ = lean_ctor_get(v_head_30_, 0);
lean_inc(v_startPos_37_);
v_endPos_38_ = lean_ctor_get(v_head_30_, 1);
lean_inc(v_endPos_38_);
lean_dec_ref(v_head_30_);
v___x_39_ = l_String_Slice_subslice_x21(v_s_21_, v_currPos_22_, v_startPos_37_);
v___x_40_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(v_s_21_, v_endPos_38_, v_tail_33_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___x_40_);
lean_ctor_set(v___x_35_, 0, v___x_39_);
v___x_42_ = v___x_35_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps___boxed(lean_object* v_s_46_, lean_object* v_currPos_47_, lean_object* v_l_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(v_s_46_, v_currPos_47_, v_l_48_);
lean_dec_ref(v_s_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___redArg(lean_object* v_l_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_, lean_object* v_h__3_53_){
_start:
{
if (lean_obj_tag(v_l_50_) == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_h__3_53_);
lean_dec(v_h__2_52_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_apply_1(v_h__1_51_, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_head_56_; 
lean_dec(v_h__1_51_);
v_head_56_ = lean_ctor_get(v_l_50_, 0);
lean_inc(v_head_56_);
if (lean_obj_tag(v_head_56_) == 0)
{
lean_object* v_tail_57_; lean_object* v_startPos_58_; lean_object* v_endPos_59_; lean_object* v___x_60_; 
lean_dec(v_h__3_53_);
v_tail_57_ = lean_ctor_get(v_l_50_, 1);
lean_inc(v_tail_57_);
lean_dec_ref(v_l_50_);
v_startPos_58_ = lean_ctor_get(v_head_56_, 0);
lean_inc(v_startPos_58_);
v_endPos_59_ = lean_ctor_get(v_head_56_, 1);
lean_inc(v_endPos_59_);
lean_dec_ref(v_head_56_);
v___x_60_ = lean_apply_3(v_h__2_52_, v_startPos_58_, v_endPos_59_, v_tail_57_);
return v___x_60_;
}
else
{
lean_object* v_tail_61_; lean_object* v_startPos_62_; lean_object* v_endPos_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_52_);
v_tail_61_ = lean_ctor_get(v_l_50_, 1);
lean_inc(v_tail_61_);
lean_dec_ref(v_l_50_);
v_startPos_62_ = lean_ctor_get(v_head_56_, 0);
lean_inc(v_startPos_62_);
v_endPos_63_ = lean_ctor_get(v_head_56_, 1);
lean_inc(v_endPos_63_);
lean_dec_ref(v_head_56_);
v___x_64_ = lean_apply_3(v_h__3_53_, v_startPos_62_, v_endPos_63_, v_tail_61_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter(lean_object* v_s_65_, lean_object* v_motive_66_, lean_object* v_l_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_, lean_object* v_h__3_70_){
_start:
{
if (lean_obj_tag(v_l_67_) == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_70_);
lean_dec(v_h__2_69_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__1_68_, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_head_73_; 
lean_dec(v_h__1_68_);
v_head_73_ = lean_ctor_get(v_l_67_, 0);
lean_inc(v_head_73_);
if (lean_obj_tag(v_head_73_) == 0)
{
lean_object* v_tail_74_; lean_object* v_startPos_75_; lean_object* v_endPos_76_; lean_object* v___x_77_; 
lean_dec(v_h__3_70_);
v_tail_74_ = lean_ctor_get(v_l_67_, 1);
lean_inc(v_tail_74_);
lean_dec_ref(v_l_67_);
v_startPos_75_ = lean_ctor_get(v_head_73_, 0);
lean_inc(v_startPos_75_);
v_endPos_76_ = lean_ctor_get(v_head_73_, 1);
lean_inc(v_endPos_76_);
lean_dec_ref(v_head_73_);
v___x_77_ = lean_apply_3(v_h__2_69_, v_startPos_75_, v_endPos_76_, v_tail_74_);
return v___x_77_;
}
else
{
lean_object* v_tail_78_; lean_object* v_startPos_79_; lean_object* v_endPos_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_69_);
v_tail_78_ = lean_ctor_get(v_l_67_, 1);
lean_inc(v_tail_78_);
lean_dec_ref(v_l_67_);
v_startPos_79_ = lean_ctor_get(v_head_73_, 0);
lean_inc(v_startPos_79_);
v_endPos_80_ = lean_ctor_get(v_head_73_, 1);
lean_inc(v_endPos_80_);
lean_dec_ref(v_head_73_);
v___x_81_ = lean_apply_3(v_h__3_70_, v_startPos_79_, v_endPos_80_, v_tail_78_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___boxed(lean_object* v_s_82_, lean_object* v_motive_83_, lean_object* v_l_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter(v_s_82_, v_motive_83_, v_l_84_, v_h__1_85_, v_h__2_86_, v_h__3_87_);
lean_dec_ref(v_s_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_, lean_object* v_h__3_92_, lean_object* v_h__4_93_){
_start:
{
switch(lean_obj_tag(v_x_89_))
{
case 0:
{
lean_object* v_out_94_; 
lean_dec(v_h__4_93_);
lean_dec(v_h__3_92_);
v_out_94_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_out_94_);
if (lean_obj_tag(v_out_94_) == 0)
{
lean_object* v_it_95_; lean_object* v_startPos_96_; lean_object* v_endPos_97_; lean_object* v___x_98_; 
lean_dec(v_h__1_90_);
v_it_95_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_it_95_);
lean_dec_ref(v_x_89_);
v_startPos_96_ = lean_ctor_get(v_out_94_, 0);
lean_inc(v_startPos_96_);
v_endPos_97_ = lean_ctor_get(v_out_94_, 1);
lean_inc(v_endPos_97_);
lean_dec_ref(v_out_94_);
v___x_98_ = lean_apply_5(v_h__2_91_, v_it_95_, v_startPos_96_, v_endPos_97_, lean_box(0), lean_box(0));
return v___x_98_;
}
else
{
lean_object* v_it_99_; lean_object* v_startPos_100_; lean_object* v_endPos_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_91_);
v_it_99_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_it_99_);
lean_dec_ref(v_x_89_);
v_startPos_100_ = lean_ctor_get(v_out_94_, 0);
lean_inc(v_startPos_100_);
v_endPos_101_ = lean_ctor_get(v_out_94_, 1);
lean_inc(v_endPos_101_);
lean_dec_ref(v_out_94_);
v___x_102_ = lean_apply_5(v_h__1_90_, v_it_99_, v_startPos_100_, v_endPos_101_, lean_box(0), lean_box(0));
return v___x_102_;
}
}
case 1:
{
lean_object* v_it_103_; lean_object* v___x_104_; 
lean_dec(v_h__4_93_);
lean_dec(v_h__2_91_);
lean_dec(v_h__1_90_);
v_it_103_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_it_103_);
lean_dec_ref(v_x_89_);
v___x_104_ = lean_apply_3(v_h__3_92_, v_it_103_, lean_box(0), lean_box(0));
return v___x_104_;
}
default: 
{
lean_object* v___x_105_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__2_91_);
lean_dec(v_h__1_90_);
v___x_105_ = lean_apply_2(v_h__4_93_, lean_box(0), lean_box(0));
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_106_, lean_object* v_inst_107_, lean_object* v_s_108_, lean_object* v_searcher_109_, lean_object* v_motive_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_, lean_object* v_h__4_115_){
_start:
{
switch(lean_obj_tag(v_x_111_))
{
case 0:
{
lean_object* v_out_116_; 
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
v_out_116_ = lean_ctor_get(v_x_111_, 1);
lean_inc(v_out_116_);
if (lean_obj_tag(v_out_116_) == 0)
{
lean_object* v_it_117_; lean_object* v_startPos_118_; lean_object* v_endPos_119_; lean_object* v___x_120_; 
lean_dec(v_h__1_112_);
v_it_117_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_it_117_);
lean_dec_ref(v_x_111_);
v_startPos_118_ = lean_ctor_get(v_out_116_, 0);
lean_inc(v_startPos_118_);
v_endPos_119_ = lean_ctor_get(v_out_116_, 1);
lean_inc(v_endPos_119_);
lean_dec_ref(v_out_116_);
v___x_120_ = lean_apply_5(v_h__2_113_, v_it_117_, v_startPos_118_, v_endPos_119_, lean_box(0), lean_box(0));
return v___x_120_;
}
else
{
lean_object* v_it_121_; lean_object* v_startPos_122_; lean_object* v_endPos_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_113_);
v_it_121_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_it_121_);
lean_dec_ref(v_x_111_);
v_startPos_122_ = lean_ctor_get(v_out_116_, 0);
lean_inc(v_startPos_122_);
v_endPos_123_ = lean_ctor_get(v_out_116_, 1);
lean_inc(v_endPos_123_);
lean_dec_ref(v_out_116_);
v___x_124_ = lean_apply_5(v_h__1_112_, v_it_121_, v_startPos_122_, v_endPos_123_, lean_box(0), lean_box(0));
return v___x_124_;
}
}
case 1:
{
lean_object* v_it_125_; lean_object* v___x_126_; 
lean_dec(v_h__4_115_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_it_125_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_it_125_);
lean_dec_ref(v_x_111_);
v___x_126_ = lean_apply_3(v_h__3_114_, v_it_125_, lean_box(0), lean_box(0));
return v___x_126_;
}
default: 
{
lean_object* v___x_127_; 
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v___x_127_ = lean_apply_2(v_h__4_115_, lean_box(0), lean_box(0));
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_128_, lean_object* v_inst_129_, lean_object* v_s_130_, lean_object* v_searcher_131_, lean_object* v_motive_132_, lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_, lean_object* v_h__3_136_, lean_object* v_h__4_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_128_, v_inst_129_, v_s_130_, v_searcher_131_, v_motive_132_, v_x_133_, v_h__1_134_, v_h__2_135_, v_h__3_136_, v_h__4_137_);
lean_dec(v_searcher_131_);
lean_dec_ref(v_s_130_);
lean_dec(v_inst_129_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_, lean_object* v_h__3_142_){
_start:
{
switch(lean_obj_tag(v_x_139_))
{
case 0:
{
lean_object* v_it_143_; lean_object* v_out_144_; lean_object* v___x_145_; 
lean_dec(v_h__3_142_);
lean_dec(v_h__2_141_);
v_it_143_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_it_143_);
v_out_144_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_out_144_);
lean_dec_ref(v_x_139_);
v___x_145_ = lean_apply_2(v_h__1_140_, v_it_143_, v_out_144_);
return v___x_145_;
}
case 1:
{
lean_object* v_it_146_; lean_object* v___x_147_; 
lean_dec(v_h__3_142_);
lean_dec(v_h__1_140_);
v_it_146_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_it_146_);
lean_dec_ref(v_x_139_);
v___x_147_ = lean_apply_1(v_h__2_141_, v_it_146_);
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_h__2_141_);
lean_dec(v_h__1_140_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_h__3_142_, v___x_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_motive_152_, lean_object* v_x_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_, lean_object* v_h__3_156_){
_start:
{
switch(lean_obj_tag(v_x_153_))
{
case 0:
{
lean_object* v_it_157_; lean_object* v_out_158_; lean_object* v___x_159_; 
lean_dec(v_h__3_156_);
lean_dec(v_h__2_155_);
v_it_157_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_it_157_);
v_out_158_ = lean_ctor_get(v_x_153_, 1);
lean_inc(v_out_158_);
lean_dec_ref(v_x_153_);
v___x_159_ = lean_apply_2(v_h__1_154_, v_it_157_, v_out_158_);
return v___x_159_;
}
case 1:
{
lean_object* v_it_160_; lean_object* v___x_161_; 
lean_dec(v_h__3_156_);
lean_dec(v_h__1_154_);
v_it_160_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_it_160_);
lean_dec_ref(v_x_153_);
v___x_161_ = lean_apply_1(v_h__2_155_, v_it_160_);
return v___x_161_;
}
default: 
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_h__2_155_);
lean_dec(v_h__1_154_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_apply_1(v_h__3_156_, v___x_162_);
return v___x_163_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
