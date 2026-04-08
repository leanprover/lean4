// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Loop
// Imports: import all Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop import all Init.Data.Iterators.Consumers.Loop import all Init.Data.Iterators.Consumers.Monadic.Collect import Init.Data.Array.Monadic public import Init.Data.Iterators.Consumers.Collect public import Init.Data.Iterators.Consumers.Loop public import Init.Data.List.Monadic import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.List.Find import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v_it_5_; lean_object* v_out_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_it_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_5_);
v_out_6_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_out_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_3(v_h__1_2_, v_it_5_, v_out_6_, lean_box(0));
return v___x_7_;
}
case 1:
{
lean_object* v_it_8_; lean_object* v___x_9_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_it_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_8_);
lean_dec_ref(v_x_1_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_it_8_, lean_box(0));
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_apply_1(v_h__3_4_, lean_box(0));
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_inst_13_, lean_object* v_it_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
_start:
{
switch(lean_obj_tag(v_x_16_))
{
case 0:
{
lean_object* v_it_20_; lean_object* v_out_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__2_18_);
v_it_20_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_it_20_);
v_out_21_ = lean_ctor_get(v_x_16_, 1);
lean_inc(v_out_21_);
lean_dec_ref(v_x_16_);
v___x_22_ = lean_apply_3(v_h__1_17_, v_it_20_, v_out_21_, lean_box(0));
return v___x_22_;
}
case 1:
{
lean_object* v_it_23_; lean_object* v___x_24_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__1_17_);
v_it_23_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_it_23_);
lean_dec_ref(v_x_16_);
v___x_24_ = lean_apply_2(v_h__2_18_, v_it_23_, lean_box(0));
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; 
lean_dec(v_h__2_18_);
lean_dec(v_h__1_17_);
v___x_25_ = lean_apply_1(v_h__3_19_, lean_box(0));
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_inst_28_, lean_object* v_it_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_, lean_object* v_h__3_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_26_, v_00_u03b2_27_, v_inst_28_, v_it_29_, v_motive_30_, v_x_31_, v_h__1_32_, v_h__2_33_, v_h__3_34_);
lean_dec(v_it_29_);
lean_dec(v_inst_28_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_____do__lift_36_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_37_);
v_a_39_ = lean_ctor_get(v_____do__lift_36_, 0);
lean_inc(v_a_39_);
lean_dec_ref(v_____do__lift_36_);
v___x_40_ = lean_apply_1(v_h__2_38_, v_a_39_);
return v___x_40_;
}
else
{
lean_object* v_a_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_38_);
v_a_41_ = lean_ctor_get(v_____do__lift_36_, 0);
lean_inc(v_a_41_);
lean_dec_ref(v_____do__lift_36_);
v___x_42_ = lean_apply_1(v_h__1_37_, v_a_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_43_, lean_object* v_motive_44_, lean_object* v_____do__lift_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_____do__lift_45_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_46_);
v_a_48_ = lean_ctor_get(v_____do__lift_45_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v_____do__lift_45_);
v___x_49_ = lean_apply_1(v_h__2_47_, v_a_48_);
return v___x_49_;
}
else
{
lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_47_);
v_a_50_ = lean_ctor_get(v_____do__lift_45_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v_____do__lift_45_);
v___x_51_ = lean_apply_1(v_h__1_46_, v_a_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_, lean_object* v_h__3_55_){
_start:
{
switch(lean_obj_tag(v_x_52_))
{
case 0:
{
lean_object* v_it_56_; lean_object* v_out_57_; lean_object* v___x_58_; 
lean_dec(v_h__3_55_);
lean_dec(v_h__2_54_);
v_it_56_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_it_56_);
v_out_57_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_out_57_);
lean_dec_ref(v_x_52_);
v___x_58_ = lean_apply_3(v_h__1_53_, v_it_56_, v_out_57_, lean_box(0));
return v___x_58_;
}
case 1:
{
lean_object* v_it_59_; lean_object* v___x_60_; 
lean_dec(v_h__3_55_);
lean_dec(v_h__1_53_);
v_it_59_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_it_59_);
lean_dec_ref(v_x_52_);
v___x_60_ = lean_apply_2(v_h__2_54_, v_it_59_, lean_box(0));
return v___x_60_;
}
default: 
{
lean_object* v___x_61_; 
lean_dec(v_h__2_54_);
lean_dec(v_h__1_53_);
v___x_61_ = lean_apply_1(v_h__3_55_, lean_box(0));
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_m_64_, lean_object* v_inst_65_, lean_object* v_it_66_, lean_object* v_motive_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
switch(lean_obj_tag(v_x_68_))
{
case 0:
{
lean_object* v_it_72_; lean_object* v_out_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__2_70_);
v_it_72_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_it_72_);
v_out_73_ = lean_ctor_get(v_x_68_, 1);
lean_inc(v_out_73_);
lean_dec_ref(v_x_68_);
v___x_74_ = lean_apply_3(v_h__1_69_, v_it_72_, v_out_73_, lean_box(0));
return v___x_74_;
}
case 1:
{
lean_object* v_it_75_; lean_object* v___x_76_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__1_69_);
v_it_75_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_it_75_);
lean_dec_ref(v_x_68_);
v___x_76_ = lean_apply_2(v_h__2_70_, v_it_75_, lean_box(0));
return v___x_76_;
}
default: 
{
lean_object* v___x_77_; 
lean_dec(v_h__2_70_);
lean_dec(v_h__1_69_);
v___x_77_ = lean_apply_1(v_h__3_71_, lean_box(0));
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_m_80_, lean_object* v_inst_81_, lean_object* v_it_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_78_, v_00_u03b2_79_, v_m_80_, v_inst_81_, v_it_82_, v_motive_83_, v_x_84_, v_h__1_85_, v_h__2_86_, v_h__3_87_);
lean_dec(v_it_82_);
lean_dec(v_inst_81_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_____do__lift_89_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_90_);
v_a_92_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc(v_a_92_);
lean_dec_ref(v_____do__lift_89_);
v___x_93_ = lean_apply_2(v_h__2_91_, v_a_92_, lean_box(0));
return v___x_93_;
}
else
{
lean_object* v_a_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_91_);
v_a_94_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc(v_a_94_);
lean_dec_ref(v_____do__lift_89_);
v___x_95_ = lean_apply_2(v_h__1_90_, v_a_94_, lean_box(0));
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b2_96_, lean_object* v_00_u03b3_97_, lean_object* v_init_98_, lean_object* v_PlausibleForInStep_99_, lean_object* v_out_100_, lean_object* v_motive_101_, lean_object* v_____do__lift_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_____do__lift_102_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_103_);
v_a_105_ = lean_ctor_get(v_____do__lift_102_, 0);
lean_inc(v_a_105_);
lean_dec_ref(v_____do__lift_102_);
v___x_106_ = lean_apply_2(v_h__2_104_, v_a_105_, lean_box(0));
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_104_);
v_a_107_ = lean_ctor_get(v_____do__lift_102_, 0);
lean_inc(v_a_107_);
lean_dec_ref(v_____do__lift_102_);
v___x_108_ = lean_apply_2(v_h__1_103_, v_a_107_, lean_box(0));
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object* v_00_u03b2_109_, lean_object* v_00_u03b3_110_, lean_object* v_init_111_, lean_object* v_PlausibleForInStep_112_, lean_object* v_out_113_, lean_object* v_motive_114_, lean_object* v_____do__lift_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_109_, v_00_u03b3_110_, v_init_111_, v_PlausibleForInStep_112_, v_out_113_, v_motive_114_, v_____do__lift_115_, v_h__1_116_, v_h__2_117_);
lean_dec(v_out_113_);
lean_dec(v_init_111_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_, lean_object* v_h__3_122_){
_start:
{
switch(lean_obj_tag(v_x_119_))
{
case 0:
{
lean_object* v_it_123_; lean_object* v_out_124_; lean_object* v___x_125_; 
lean_dec(v_h__3_122_);
lean_dec(v_h__2_121_);
v_it_123_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_it_123_);
v_out_124_ = lean_ctor_get(v_x_119_, 1);
lean_inc(v_out_124_);
lean_dec_ref(v_x_119_);
v___x_125_ = lean_apply_2(v_h__1_120_, v_it_123_, v_out_124_);
return v___x_125_;
}
case 1:
{
lean_object* v_it_126_; lean_object* v___x_127_; 
lean_dec(v_h__3_122_);
lean_dec(v_h__1_120_);
v_it_126_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_it_126_);
lean_dec_ref(v_x_119_);
v___x_127_ = lean_apply_1(v_h__2_121_, v_it_126_);
return v___x_127_;
}
default: 
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_121_);
lean_dec(v_h__1_120_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__3_122_, v___x_128_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_motive_132_, lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_, lean_object* v_h__3_136_){
_start:
{
switch(lean_obj_tag(v_x_133_))
{
case 0:
{
lean_object* v_it_137_; lean_object* v_out_138_; lean_object* v___x_139_; 
lean_dec(v_h__3_136_);
lean_dec(v_h__2_135_);
v_it_137_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_it_137_);
v_out_138_ = lean_ctor_get(v_x_133_, 1);
lean_inc(v_out_138_);
lean_dec_ref(v_x_133_);
v___x_139_ = lean_apply_2(v_h__1_134_, v_it_137_, v_out_138_);
return v___x_139_;
}
case 1:
{
lean_object* v_it_140_; lean_object* v___x_141_; 
lean_dec(v_h__3_136_);
lean_dec(v_h__1_134_);
v_it_140_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_it_140_);
lean_dec_ref(v_x_133_);
v___x_141_ = lean_apply_1(v_h__2_135_, v_it_140_);
return v___x_141_;
}
default: 
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_h__2_135_);
lean_dec(v_h__1_134_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_1(v_h__3_136_, v___x_142_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
if (lean_obj_tag(v_b_144_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_145_);
v_a_147_ = lean_ctor_get(v_b_144_, 0);
lean_inc(v_a_147_);
lean_dec_ref(v_b_144_);
v___x_148_ = lean_apply_1(v_h__2_146_, v_a_147_);
return v___x_148_;
}
else
{
lean_object* v_a_149_; lean_object* v___x_150_; 
lean_dec(v_h__2_146_);
v_a_149_ = lean_ctor_get(v_b_144_, 0);
lean_inc(v_a_149_);
lean_dec_ref(v_b_144_);
v___x_150_ = lean_apply_1(v_h__1_145_, v_a_149_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_151_, lean_object* v_motive_152_, lean_object* v_b_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
if (lean_obj_tag(v_b_153_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; 
lean_dec(v_h__1_154_);
v_a_156_ = lean_ctor_get(v_b_153_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v_b_153_);
v___x_157_ = lean_apply_1(v_h__2_155_, v_a_156_);
return v___x_157_;
}
else
{
lean_object* v_a_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_155_);
v_a_158_ = lean_ctor_get(v_b_153_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v_b_153_);
v___x_159_ = lean_apply_1(v_h__1_154_, v_a_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_, lean_object* v_h__3_163_){
_start:
{
switch(lean_obj_tag(v_x_160_))
{
case 0:
{
lean_object* v_it_164_; lean_object* v_out_165_; lean_object* v___x_166_; 
lean_dec(v_h__3_163_);
lean_dec(v_h__2_162_);
v_it_164_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_it_164_);
v_out_165_ = lean_ctor_get(v_x_160_, 1);
lean_inc(v_out_165_);
lean_dec_ref(v_x_160_);
v___x_166_ = lean_apply_2(v_h__1_161_, v_it_164_, v_out_165_);
return v___x_166_;
}
case 1:
{
lean_object* v_it_167_; lean_object* v___x_168_; 
lean_dec(v_h__3_163_);
lean_dec(v_h__1_161_);
v_it_167_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_it_167_);
lean_dec_ref(v_x_160_);
v___x_168_ = lean_apply_1(v_h__2_162_, v_it_167_);
return v___x_168_;
}
default: 
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_h__2_162_);
lean_dec(v_h__1_161_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_apply_1(v_h__3_163_, v___x_169_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_motive_173_, lean_object* v_x_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_, lean_object* v_h__3_177_){
_start:
{
switch(lean_obj_tag(v_x_174_))
{
case 0:
{
lean_object* v_it_178_; lean_object* v_out_179_; lean_object* v___x_180_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__2_176_);
v_it_178_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_it_178_);
v_out_179_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_out_179_);
lean_dec_ref(v_x_174_);
v___x_180_ = lean_apply_2(v_h__1_175_, v_it_178_, v_out_179_);
return v___x_180_;
}
case 1:
{
lean_object* v_it_181_; lean_object* v___x_182_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__1_175_);
v_it_181_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_it_181_);
lean_dec_ref(v_x_174_);
v___x_182_ = lean_apply_1(v_h__2_176_, v_it_181_);
return v___x_182_;
}
default: 
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_176_);
lean_dec(v_h__1_175_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__3_177_, v___x_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_, lean_object* v_h__3_188_){
_start:
{
switch(lean_obj_tag(v_x_185_))
{
case 0:
{
lean_object* v_it_189_; lean_object* v_out_190_; lean_object* v___x_191_; 
lean_dec(v_h__3_188_);
lean_dec(v_h__2_187_);
v_it_189_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_it_189_);
v_out_190_ = lean_ctor_get(v_x_185_, 1);
lean_inc(v_out_190_);
lean_dec_ref(v_x_185_);
v___x_191_ = lean_apply_2(v_h__1_186_, v_it_189_, v_out_190_);
return v___x_191_;
}
case 1:
{
lean_object* v_it_192_; lean_object* v___x_193_; 
lean_dec(v_h__3_188_);
lean_dec(v_h__1_186_);
v_it_192_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_it_192_);
lean_dec_ref(v_x_185_);
v___x_193_ = lean_apply_1(v_h__2_187_, v_it_192_);
return v___x_193_;
}
default: 
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_h__2_187_);
lean_dec(v_h__1_186_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_apply_1(v_h__3_188_, v___x_194_);
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_m_198_, lean_object* v_motive_199_, lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_, lean_object* v_h__3_203_){
_start:
{
switch(lean_obj_tag(v_x_200_))
{
case 0:
{
lean_object* v_it_204_; lean_object* v_out_205_; lean_object* v___x_206_; 
lean_dec(v_h__3_203_);
lean_dec(v_h__2_202_);
v_it_204_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_it_204_);
v_out_205_ = lean_ctor_get(v_x_200_, 1);
lean_inc(v_out_205_);
lean_dec_ref(v_x_200_);
v___x_206_ = lean_apply_2(v_h__1_201_, v_it_204_, v_out_205_);
return v___x_206_;
}
case 1:
{
lean_object* v_it_207_; lean_object* v___x_208_; 
lean_dec(v_h__3_203_);
lean_dec(v_h__1_201_);
v_it_207_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_it_207_);
lean_dec_ref(v_x_200_);
v___x_208_ = lean_apply_1(v_h__2_202_, v_it_207_);
return v___x_208_;
}
default: 
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_h__2_202_);
lean_dec(v_h__1_201_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_apply_1(v_h__3_203_, v___x_209_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_){
_start:
{
if (lean_obj_tag(v_____do__lift_211_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_h__2_213_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_1(v_h__1_212_, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v_val_216_; lean_object* v___x_217_; 
lean_dec(v_h__1_212_);
v_val_216_ = lean_ctor_get(v_____do__lift_211_, 0);
lean_inc(v_val_216_);
lean_dec_ref(v_____do__lift_211_);
v___x_217_ = lean_apply_1(v_h__2_213_, v_val_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b3_218_, lean_object* v_motive_219_, lean_object* v_____do__lift_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
if (lean_obj_tag(v_____do__lift_220_) == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__2_222_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__1_221_, v___x_223_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; 
lean_dec(v_h__1_221_);
v_val_225_ = lean_ctor_get(v_____do__lift_220_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v_____do__lift_220_);
v___x_226_ = lean_apply_1(v_h__2_222_, v_val_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_227_, lean_object* v_h__1_228_, lean_object* v_h__2_229_){
_start:
{
if (lean_obj_tag(v_____do__lift_227_) == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v_h__2_229_);
v___x_230_ = lean_box(0);
v___x_231_ = lean_apply_1(v_h__1_228_, v___x_230_);
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_233_; 
lean_dec(v_h__1_228_);
v_val_232_ = lean_ctor_get(v_____do__lift_227_, 0);
lean_inc(v_val_232_);
lean_dec_ref(v_____do__lift_227_);
v___x_233_ = lean_apply_1(v_h__2_229_, v_val_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_234_, lean_object* v_motive_235_, lean_object* v_____do__lift_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
_start:
{
if (lean_obj_tag(v_____do__lift_236_) == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v_h__2_238_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_apply_1(v_h__1_237_, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_242_; 
lean_dec(v_h__1_237_);
v_val_241_ = lean_ctor_get(v_____do__lift_236_, 0);
lean_inc(v_val_241_);
lean_dec_ref(v_____do__lift_236_);
v___x_242_ = lean_apply_1(v_h__2_238_, v_val_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(lean_object* v_____do__lift_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (lean_obj_tag(v_____do__lift_243_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__1_244_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__2_245_, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v_val_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_245_);
v_val_248_ = lean_ctor_get(v_____do__lift_243_, 0);
lean_inc(v_val_248_);
lean_dec_ref(v_____do__lift_243_);
v___x_249_ = lean_apply_1(v_h__1_244_, v_val_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter(lean_object* v_00_u03b2_250_, lean_object* v_motive_251_, lean_object* v_____do__lift_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
if (lean_obj_tag(v_____do__lift_252_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_h__1_253_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_apply_1(v_h__2_254_, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v_val_257_; lean_object* v___x_258_; 
lean_dec(v_h__2_254_);
v_val_257_ = lean_ctor_get(v_____do__lift_252_, 0);
lean_inc(v_val_257_);
lean_dec_ref(v_____do__lift_252_);
v___x_258_ = lean_apply_1(v_h__1_253_, v_val_257_);
return v___x_258_;
}
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
}
#ifdef __cplusplus
}
#endif
