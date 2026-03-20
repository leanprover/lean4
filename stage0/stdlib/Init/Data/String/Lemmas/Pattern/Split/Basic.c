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
lean_object* v___x_12_; 
v___x_12_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___redArg(v_x_9_, v_h__1_10_, v_h__2_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___boxed(lean_object* v_s_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter(v_s_13_, v_motive_14_, v_x_15_, v_h__1_16_, v_h__2_17_);
lean_dec_ref(v_s_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(lean_object* v_s_19_, lean_object* v_currPos_20_, lean_object* v_l_21_){
_start:
{
if (lean_obj_tag(v_l_21_) == 0)
{
lean_object* v_startInclusive_22_; lean_object* v_endExclusive_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_startInclusive_22_ = lean_ctor_get(v_s_19_, 1);
v_endExclusive_23_ = lean_ctor_get(v_s_19_, 2);
v___x_24_ = lean_nat_sub(v_endExclusive_23_, v_startInclusive_22_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v_currPos_20_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_25_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v_head_28_; 
v_head_28_ = lean_ctor_get(v_l_21_, 0);
if (lean_obj_tag(v_head_28_) == 0)
{
lean_object* v_tail_29_; 
v_tail_29_ = lean_ctor_get(v_l_21_, 1);
lean_inc(v_tail_29_);
lean_dec_ref(v_l_21_);
v_l_21_ = v_tail_29_;
goto _start;
}
else
{
lean_object* v_tail_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_42_; 
lean_inc_ref(v_head_28_);
v_tail_31_ = lean_ctor_get(v_l_21_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_l_21_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v_l_21_, 0);
lean_dec(v_unused_43_);
v___x_33_ = v_l_21_;
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_tail_31_);
lean_dec(v_l_21_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_startPos_35_; lean_object* v_endPos_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v_startPos_35_ = lean_ctor_get(v_head_28_, 0);
lean_inc(v_startPos_35_);
v_endPos_36_ = lean_ctor_get(v_head_28_, 1);
lean_inc(v_endPos_36_);
lean_dec_ref(v_head_28_);
v___x_37_ = l_String_Slice_subslice_x21(v_s_19_, v_currPos_20_, v_startPos_35_);
v___x_38_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(v_s_19_, v_endPos_36_, v_tail_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___x_38_);
lean_ctor_set(v___x_33_, 0, v___x_37_);
v___x_40_ = v___x_33_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps___boxed(lean_object* v_s_44_, lean_object* v_currPos_45_, lean_object* v_l_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(v_s_44_, v_currPos_45_, v_l_46_);
lean_dec_ref(v_s_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___redArg(lean_object* v_l_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_){
_start:
{
if (lean_obj_tag(v_l_48_) == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__3_51_);
lean_dec(v_h__2_50_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_apply_1(v_h__1_49_, v___x_52_);
return v___x_53_;
}
else
{
lean_object* v_head_54_; 
lean_dec(v_h__1_49_);
v_head_54_ = lean_ctor_get(v_l_48_, 0);
lean_inc(v_head_54_);
if (lean_obj_tag(v_head_54_) == 0)
{
lean_object* v_tail_55_; lean_object* v_startPos_56_; lean_object* v_endPos_57_; lean_object* v___x_58_; 
lean_dec(v_h__3_51_);
v_tail_55_ = lean_ctor_get(v_l_48_, 1);
lean_inc(v_tail_55_);
lean_dec_ref(v_l_48_);
v_startPos_56_ = lean_ctor_get(v_head_54_, 0);
lean_inc(v_startPos_56_);
v_endPos_57_ = lean_ctor_get(v_head_54_, 1);
lean_inc(v_endPos_57_);
lean_dec_ref(v_head_54_);
v___x_58_ = lean_apply_3(v_h__2_50_, v_startPos_56_, v_endPos_57_, v_tail_55_);
return v___x_58_;
}
else
{
lean_object* v_tail_59_; lean_object* v_startPos_60_; lean_object* v_endPos_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_50_);
v_tail_59_ = lean_ctor_get(v_l_48_, 1);
lean_inc(v_tail_59_);
lean_dec_ref(v_l_48_);
v_startPos_60_ = lean_ctor_get(v_head_54_, 0);
lean_inc(v_startPos_60_);
v_endPos_61_ = lean_ctor_get(v_head_54_, 1);
lean_inc(v_endPos_61_);
lean_dec_ref(v_head_54_);
v___x_62_ = lean_apply_3(v_h__3_51_, v_startPos_60_, v_endPos_61_, v_tail_59_);
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter(lean_object* v_s_63_, lean_object* v_motive_64_, lean_object* v_l_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_, lean_object* v_h__3_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___redArg(v_l_65_, v_h__1_66_, v_h__2_67_, v_h__3_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___boxed(lean_object* v_s_70_, lean_object* v_motive_71_, lean_object* v_l_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_, lean_object* v_h__3_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter(v_s_70_, v_motive_71_, v_l_72_, v_h__1_73_, v_h__2_74_, v_h__3_75_);
lean_dec_ref(v_s_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_, lean_object* v_h__3_80_, lean_object* v_h__4_81_){
_start:
{
switch(lean_obj_tag(v_x_77_))
{
case 0:
{
lean_object* v_out_82_; 
lean_dec(v_h__4_81_);
lean_dec(v_h__3_80_);
v_out_82_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_out_82_);
if (lean_obj_tag(v_out_82_) == 0)
{
lean_object* v_it_83_; lean_object* v_startPos_84_; lean_object* v_endPos_85_; lean_object* v___x_86_; 
lean_dec(v_h__1_78_);
v_it_83_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_it_83_);
lean_dec_ref(v_x_77_);
v_startPos_84_ = lean_ctor_get(v_out_82_, 0);
lean_inc(v_startPos_84_);
v_endPos_85_ = lean_ctor_get(v_out_82_, 1);
lean_inc(v_endPos_85_);
lean_dec_ref(v_out_82_);
v___x_86_ = lean_apply_5(v_h__2_79_, v_it_83_, v_startPos_84_, v_endPos_85_, lean_box(0), lean_box(0));
return v___x_86_;
}
else
{
lean_object* v_it_87_; lean_object* v_startPos_88_; lean_object* v_endPos_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_79_);
v_it_87_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_it_87_);
lean_dec_ref(v_x_77_);
v_startPos_88_ = lean_ctor_get(v_out_82_, 0);
lean_inc(v_startPos_88_);
v_endPos_89_ = lean_ctor_get(v_out_82_, 1);
lean_inc(v_endPos_89_);
lean_dec_ref(v_out_82_);
v___x_90_ = lean_apply_5(v_h__1_78_, v_it_87_, v_startPos_88_, v_endPos_89_, lean_box(0), lean_box(0));
return v___x_90_;
}
}
case 1:
{
lean_object* v_it_91_; lean_object* v___x_92_; 
lean_dec(v_h__4_81_);
lean_dec(v_h__2_79_);
lean_dec(v_h__1_78_);
v_it_91_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_it_91_);
lean_dec_ref(v_x_77_);
v___x_92_ = lean_apply_3(v_h__3_80_, v_it_91_, lean_box(0), lean_box(0));
return v___x_92_;
}
default: 
{
lean_object* v___x_93_; 
lean_dec(v_h__3_80_);
lean_dec(v_h__2_79_);
lean_dec(v_h__1_78_);
v___x_93_ = lean_apply_2(v_h__4_81_, lean_box(0), lean_box(0));
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_94_, lean_object* v_inst_95_, lean_object* v_s_96_, lean_object* v_searcher_97_, lean_object* v_motive_98_, lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_, lean_object* v_h__3_102_, lean_object* v_h__4_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(v_x_99_, v_h__1_100_, v_h__2_101_, v_h__3_102_, v_h__4_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_105_, lean_object* v_inst_106_, lean_object* v_s_107_, lean_object* v_searcher_108_, lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_, lean_object* v_h__4_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_105_, v_inst_106_, v_s_107_, v_searcher_108_, v_motive_109_, v_x_110_, v_h__1_111_, v_h__2_112_, v_h__3_113_, v_h__4_114_);
lean_dec(v_searcher_108_);
lean_dec_ref(v_s_107_);
lean_dec(v_inst_106_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_, lean_object* v_h__3_119_){
_start:
{
switch(lean_obj_tag(v_x_116_))
{
case 0:
{
lean_object* v_it_120_; lean_object* v_out_121_; lean_object* v___x_122_; 
lean_dec(v_h__3_119_);
lean_dec(v_h__2_118_);
v_it_120_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_it_120_);
v_out_121_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_out_121_);
lean_dec_ref(v_x_116_);
v___x_122_ = lean_apply_2(v_h__1_117_, v_it_120_, v_out_121_);
return v___x_122_;
}
case 1:
{
lean_object* v_it_123_; lean_object* v___x_124_; 
lean_dec(v_h__3_119_);
lean_dec(v_h__1_117_);
v_it_123_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_it_123_);
lean_dec_ref(v_x_116_);
v___x_124_ = lean_apply_1(v_h__2_118_, v_it_123_);
return v___x_124_;
}
default: 
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_118_);
lean_dec(v_h__1_117_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_apply_1(v_h__3_119_, v___x_125_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_motive_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_, lean_object* v_h__3_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(v_x_130_, v_h__1_131_, v_h__2_132_, v_h__3_133_);
return v___x_134_;
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
