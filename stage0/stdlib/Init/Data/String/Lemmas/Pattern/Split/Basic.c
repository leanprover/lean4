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
lean_dec_ref_known(v_x_1_, 1);
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
lean_dec_ref_known(v_x_9_, 1);
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
lean_dec_ref_known(v_l_23_, 2);
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
lean_dec_ref_known(v_head_30_, 2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_, lean_object* v_h__3_53_, lean_object* v_h__4_54_){
_start:
{
switch(lean_obj_tag(v_x_50_))
{
case 0:
{
lean_object* v_out_55_; 
lean_dec(v_h__4_54_);
lean_dec(v_h__3_53_);
v_out_55_ = lean_ctor_get(v_x_50_, 1);
lean_inc(v_out_55_);
if (lean_obj_tag(v_out_55_) == 0)
{
lean_object* v_it_56_; lean_object* v_startPos_57_; lean_object* v_endPos_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_51_);
v_it_56_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_it_56_);
lean_dec_ref_known(v_x_50_, 2);
v_startPos_57_ = lean_ctor_get(v_out_55_, 0);
lean_inc(v_startPos_57_);
v_endPos_58_ = lean_ctor_get(v_out_55_, 1);
lean_inc(v_endPos_58_);
lean_dec_ref_known(v_out_55_, 2);
v___x_59_ = lean_apply_5(v_h__2_52_, v_it_56_, v_startPos_57_, v_endPos_58_, lean_box(0), lean_box(0));
return v___x_59_;
}
else
{
lean_object* v_it_60_; lean_object* v_startPos_61_; lean_object* v_endPos_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_52_);
v_it_60_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_it_60_);
lean_dec_ref_known(v_x_50_, 2);
v_startPos_61_ = lean_ctor_get(v_out_55_, 0);
lean_inc(v_startPos_61_);
v_endPos_62_ = lean_ctor_get(v_out_55_, 1);
lean_inc(v_endPos_62_);
lean_dec_ref_known(v_out_55_, 2);
v___x_63_ = lean_apply_5(v_h__1_51_, v_it_60_, v_startPos_61_, v_endPos_62_, lean_box(0), lean_box(0));
return v___x_63_;
}
}
case 1:
{
lean_object* v_it_64_; lean_object* v___x_65_; 
lean_dec(v_h__4_54_);
lean_dec(v_h__2_52_);
lean_dec(v_h__1_51_);
v_it_64_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_it_64_);
lean_dec_ref_known(v_x_50_, 1);
v___x_65_ = lean_apply_3(v_h__3_53_, v_it_64_, lean_box(0), lean_box(0));
return v___x_65_;
}
default: 
{
lean_object* v___x_66_; 
lean_dec(v_h__3_53_);
lean_dec(v_h__2_52_);
lean_dec(v_h__1_51_);
v___x_66_ = lean_apply_2(v_h__4_54_, lean_box(0), lean_box(0));
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_67_, lean_object* v_inst_68_, lean_object* v_s_69_, lean_object* v_searcher_70_, lean_object* v_motive_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_, lean_object* v_h__3_75_, lean_object* v_h__4_76_){
_start:
{
switch(lean_obj_tag(v_x_72_))
{
case 0:
{
lean_object* v_out_77_; 
lean_dec(v_h__4_76_);
lean_dec(v_h__3_75_);
v_out_77_ = lean_ctor_get(v_x_72_, 1);
lean_inc(v_out_77_);
if (lean_obj_tag(v_out_77_) == 0)
{
lean_object* v_it_78_; lean_object* v_startPos_79_; lean_object* v_endPos_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_73_);
v_it_78_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_it_78_);
lean_dec_ref_known(v_x_72_, 2);
v_startPos_79_ = lean_ctor_get(v_out_77_, 0);
lean_inc(v_startPos_79_);
v_endPos_80_ = lean_ctor_get(v_out_77_, 1);
lean_inc(v_endPos_80_);
lean_dec_ref_known(v_out_77_, 2);
v___x_81_ = lean_apply_5(v_h__2_74_, v_it_78_, v_startPos_79_, v_endPos_80_, lean_box(0), lean_box(0));
return v___x_81_;
}
else
{
lean_object* v_it_82_; lean_object* v_startPos_83_; lean_object* v_endPos_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_74_);
v_it_82_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_it_82_);
lean_dec_ref_known(v_x_72_, 2);
v_startPos_83_ = lean_ctor_get(v_out_77_, 0);
lean_inc(v_startPos_83_);
v_endPos_84_ = lean_ctor_get(v_out_77_, 1);
lean_inc(v_endPos_84_);
lean_dec_ref_known(v_out_77_, 2);
v___x_85_ = lean_apply_5(v_h__1_73_, v_it_82_, v_startPos_83_, v_endPos_84_, lean_box(0), lean_box(0));
return v___x_85_;
}
}
case 1:
{
lean_object* v_it_86_; lean_object* v___x_87_; 
lean_dec(v_h__4_76_);
lean_dec(v_h__2_74_);
lean_dec(v_h__1_73_);
v_it_86_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_it_86_);
lean_dec_ref_known(v_x_72_, 1);
v___x_87_ = lean_apply_3(v_h__3_75_, v_it_86_, lean_box(0), lean_box(0));
return v___x_87_;
}
default: 
{
lean_object* v___x_88_; 
lean_dec(v_h__3_75_);
lean_dec(v_h__2_74_);
lean_dec(v_h__1_73_);
v___x_88_ = lean_apply_2(v_h__4_76_, lean_box(0), lean_box(0));
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_89_, lean_object* v_inst_90_, lean_object* v_s_91_, lean_object* v_searcher_92_, lean_object* v_motive_93_, lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_, lean_object* v_h__3_97_, lean_object* v_h__4_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_89_, v_inst_90_, v_s_91_, v_searcher_92_, v_motive_93_, v_x_94_, v_h__1_95_, v_h__2_96_, v_h__3_97_, v_h__4_98_);
lean_dec(v_searcher_92_);
lean_dec_ref(v_s_91_);
lean_dec(v_inst_90_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_, lean_object* v_h__3_103_){
_start:
{
switch(lean_obj_tag(v_x_100_))
{
case 0:
{
lean_object* v_it_104_; lean_object* v_out_105_; lean_object* v___x_106_; 
lean_dec(v_h__3_103_);
lean_dec(v_h__2_102_);
v_it_104_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_it_104_);
v_out_105_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_out_105_);
lean_dec_ref_known(v_x_100_, 2);
v___x_106_ = lean_apply_2(v_h__1_101_, v_it_104_, v_out_105_);
return v___x_106_;
}
case 1:
{
lean_object* v_it_107_; lean_object* v___x_108_; 
lean_dec(v_h__3_103_);
lean_dec(v_h__1_101_);
v_it_107_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_it_107_);
lean_dec_ref_known(v_x_100_, 1);
v___x_108_ = lean_apply_1(v_h__2_102_, v_it_107_);
return v___x_108_;
}
default: 
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_102_);
lean_dec(v_h__1_101_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_1(v_h__3_103_, v___x_109_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_, lean_object* v_h__3_117_){
_start:
{
switch(lean_obj_tag(v_x_114_))
{
case 0:
{
lean_object* v_it_118_; lean_object* v_out_119_; lean_object* v___x_120_; 
lean_dec(v_h__3_117_);
lean_dec(v_h__2_116_);
v_it_118_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_it_118_);
v_out_119_ = lean_ctor_get(v_x_114_, 1);
lean_inc(v_out_119_);
lean_dec_ref_known(v_x_114_, 2);
v___x_120_ = lean_apply_2(v_h__1_115_, v_it_118_, v_out_119_);
return v___x_120_;
}
case 1:
{
lean_object* v_it_121_; lean_object* v___x_122_; 
lean_dec(v_h__3_117_);
lean_dec(v_h__1_115_);
v_it_121_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_it_121_);
lean_dec_ref_known(v_x_114_, 1);
v___x_122_ = lean_apply_1(v_h__2_116_, v_it_121_);
return v___x_122_;
}
default: 
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_116_);
lean_dec(v_h__1_115_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_apply_1(v_h__3_117_, v___x_123_);
return v___x_124_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
