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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterStep_successor_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_1_, 2);
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
lean_dec_ref_known(v_x_1_, 1);
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
lean_dec_ref_known(v_x_16_, 2);
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
lean_dec_ref_known(v_x_16_, 1);
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
lean_dec_ref_known(v_____do__lift_36_, 1);
v___x_40_ = lean_apply_1(v_h__2_38_, v_a_39_);
return v___x_40_;
}
else
{
lean_object* v_a_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_38_);
v_a_41_ = lean_ctor_get(v_____do__lift_36_, 0);
lean_inc(v_a_41_);
lean_dec_ref_known(v_____do__lift_36_, 1);
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
lean_dec_ref_known(v_____do__lift_45_, 1);
v___x_49_ = lean_apply_1(v_h__2_47_, v_a_48_);
return v___x_49_;
}
else
{
lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_47_);
v_a_50_ = lean_ctor_get(v_____do__lift_45_, 0);
lean_inc(v_a_50_);
lean_dec_ref_known(v_____do__lift_45_, 1);
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
lean_dec_ref_known(v_x_52_, 2);
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
lean_dec_ref_known(v_x_52_, 1);
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
lean_dec_ref_known(v_x_68_, 2);
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
lean_dec_ref_known(v_x_68_, 1);
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
lean_dec_ref_known(v_____do__lift_89_, 1);
v___x_93_ = lean_apply_2(v_h__2_91_, v_a_92_, lean_box(0));
return v___x_93_;
}
else
{
lean_object* v_a_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_91_);
v_a_94_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v_____do__lift_89_, 1);
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
lean_dec_ref_known(v_____do__lift_102_, 1);
v___x_106_ = lean_apply_2(v_h__2_104_, v_a_105_, lean_box(0));
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_104_);
v_a_107_ = lean_ctor_get(v_____do__lift_102_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v_____do__lift_102_, 1);
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
lean_dec_ref_known(v_x_119_, 2);
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
lean_dec_ref_known(v_x_119_, 1);
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
lean_dec_ref_known(v_x_133_, 2);
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
lean_dec_ref_known(v_x_133_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_, lean_object* v_h__3_147_){
_start:
{
switch(lean_obj_tag(v_x_144_))
{
case 0:
{
lean_object* v_it_148_; lean_object* v_out_149_; lean_object* v___x_150_; 
lean_dec(v_h__3_147_);
lean_dec(v_h__2_146_);
v_it_148_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_it_148_);
v_out_149_ = lean_ctor_get(v_x_144_, 1);
lean_inc(v_out_149_);
lean_dec_ref_known(v_x_144_, 2);
v___x_150_ = lean_apply_2(v_h__1_145_, v_it_148_, v_out_149_);
return v___x_150_;
}
case 1:
{
lean_object* v_it_151_; lean_object* v___x_152_; 
lean_dec(v_h__3_147_);
lean_dec(v_h__1_145_);
v_it_151_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_it_151_);
lean_dec_ref_known(v_x_144_, 1);
v___x_152_ = lean_apply_1(v_h__2_146_, v_it_151_);
return v___x_152_;
}
default: 
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_h__2_146_);
lean_dec(v_h__1_145_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_apply_1(v_h__3_147_, v___x_153_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterStep_successor_match__1_splitter(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_motive_157_, lean_object* v_x_158_, lean_object* v_h__1_159_, lean_object* v_h__2_160_, lean_object* v_h__3_161_){
_start:
{
switch(lean_obj_tag(v_x_158_))
{
case 0:
{
lean_object* v_it_162_; lean_object* v_out_163_; lean_object* v___x_164_; 
lean_dec(v_h__3_161_);
lean_dec(v_h__2_160_);
v_it_162_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_it_162_);
v_out_163_ = lean_ctor_get(v_x_158_, 1);
lean_inc(v_out_163_);
lean_dec_ref_known(v_x_158_, 2);
v___x_164_ = lean_apply_2(v_h__1_159_, v_it_162_, v_out_163_);
return v___x_164_;
}
case 1:
{
lean_object* v_it_165_; lean_object* v___x_166_; 
lean_dec(v_h__3_161_);
lean_dec(v_h__1_159_);
v_it_165_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_it_165_);
lean_dec_ref_known(v_x_158_, 1);
v___x_166_ = lean_apply_1(v_h__2_160_, v_it_165_);
return v___x_166_;
}
default: 
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_h__2_160_);
lean_dec(v_h__1_159_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_apply_1(v_h__3_161_, v___x_167_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_){
_start:
{
if (lean_obj_tag(v_b_169_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; 
lean_dec(v_h__1_170_);
v_a_172_ = lean_ctor_get(v_b_169_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v_b_169_, 1);
v___x_173_ = lean_apply_1(v_h__2_171_, v_a_172_);
return v___x_173_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_175_; 
lean_dec(v_h__2_171_);
v_a_174_ = lean_ctor_get(v_b_169_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v_b_169_, 1);
v___x_175_ = lean_apply_1(v_h__1_170_, v_a_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_176_, lean_object* v_motive_177_, lean_object* v_b_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
_start:
{
if (lean_obj_tag(v_b_178_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
lean_dec(v_h__1_179_);
v_a_181_ = lean_ctor_get(v_b_178_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v_b_178_, 1);
v___x_182_ = lean_apply_1(v_h__2_180_, v_a_181_);
return v___x_182_;
}
else
{
lean_object* v_a_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_180_);
v_a_183_ = lean_ctor_get(v_b_178_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v_b_178_, 1);
v___x_184_ = lean_apply_1(v_h__1_179_, v_a_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_, lean_object* v_h__3_188_){
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
lean_dec_ref_known(v_x_185_, 2);
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
lean_dec_ref_known(v_x_185_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_motive_198_, lean_object* v_x_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_, lean_object* v_h__3_202_){
_start:
{
switch(lean_obj_tag(v_x_199_))
{
case 0:
{
lean_object* v_it_203_; lean_object* v_out_204_; lean_object* v___x_205_; 
lean_dec(v_h__3_202_);
lean_dec(v_h__2_201_);
v_it_203_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_it_203_);
v_out_204_ = lean_ctor_get(v_x_199_, 1);
lean_inc(v_out_204_);
lean_dec_ref_known(v_x_199_, 2);
v___x_205_ = lean_apply_2(v_h__1_200_, v_it_203_, v_out_204_);
return v___x_205_;
}
case 1:
{
lean_object* v_it_206_; lean_object* v___x_207_; 
lean_dec(v_h__3_202_);
lean_dec(v_h__1_200_);
v_it_206_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_it_206_);
lean_dec_ref_known(v_x_199_, 1);
v___x_207_ = lean_apply_1(v_h__2_201_, v_it_206_);
return v___x_207_;
}
default: 
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_h__2_201_);
lean_dec(v_h__1_200_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_apply_1(v_h__3_202_, v___x_208_);
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_, lean_object* v_h__3_213_){
_start:
{
switch(lean_obj_tag(v_x_210_))
{
case 0:
{
lean_object* v_it_214_; lean_object* v_out_215_; lean_object* v___x_216_; 
lean_dec(v_h__3_213_);
lean_dec(v_h__2_212_);
v_it_214_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_it_214_);
v_out_215_ = lean_ctor_get(v_x_210_, 1);
lean_inc(v_out_215_);
lean_dec_ref_known(v_x_210_, 2);
v___x_216_ = lean_apply_2(v_h__1_211_, v_it_214_, v_out_215_);
return v___x_216_;
}
case 1:
{
lean_object* v_it_217_; lean_object* v___x_218_; 
lean_dec(v_h__3_213_);
lean_dec(v_h__1_211_);
v_it_217_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_it_217_);
lean_dec_ref_known(v_x_210_, 1);
v___x_218_ = lean_apply_1(v_h__2_212_, v_it_217_);
return v___x_218_;
}
default: 
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_h__2_212_);
lean_dec(v_h__1_211_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_apply_1(v_h__3_213_, v___x_219_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_m_223_, lean_object* v_motive_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_, lean_object* v_h__3_228_){
_start:
{
switch(lean_obj_tag(v_x_225_))
{
case 0:
{
lean_object* v_it_229_; lean_object* v_out_230_; lean_object* v___x_231_; 
lean_dec(v_h__3_228_);
lean_dec(v_h__2_227_);
v_it_229_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_it_229_);
v_out_230_ = lean_ctor_get(v_x_225_, 1);
lean_inc(v_out_230_);
lean_dec_ref_known(v_x_225_, 2);
v___x_231_ = lean_apply_2(v_h__1_226_, v_it_229_, v_out_230_);
return v___x_231_;
}
case 1:
{
lean_object* v_it_232_; lean_object* v___x_233_; 
lean_dec(v_h__3_228_);
lean_dec(v_h__1_226_);
v_it_232_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_it_232_);
lean_dec_ref_known(v_x_225_, 1);
v___x_233_ = lean_apply_1(v_h__2_227_, v_it_232_);
return v___x_233_;
}
default: 
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_h__2_227_);
lean_dec(v_h__1_226_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_apply_1(v_h__3_228_, v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
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
lean_dec_ref_known(v_____do__lift_236_, 1);
v___x_242_ = lean_apply_1(v_h__2_238_, v_val_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b3_243_, lean_object* v_motive_244_, lean_object* v_____do__lift_245_, lean_object* v_h__1_246_, lean_object* v_h__2_247_){
_start:
{
if (lean_obj_tag(v_____do__lift_245_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_247_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_apply_1(v_h__1_246_, v___x_248_);
return v___x_249_;
}
else
{
lean_object* v_val_250_; lean_object* v___x_251_; 
lean_dec(v_h__1_246_);
v_val_250_ = lean_ctor_get(v_____do__lift_245_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v_____do__lift_245_, 1);
v___x_251_ = lean_apply_1(v_h__2_247_, v_val_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
if (lean_obj_tag(v_____do__lift_252_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_h__2_254_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_apply_1(v_h__1_253_, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v_val_257_; lean_object* v___x_258_; 
lean_dec(v_h__1_253_);
v_val_257_ = lean_ctor_get(v_____do__lift_252_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v_____do__lift_252_, 1);
v___x_258_ = lean_apply_1(v_h__2_254_, v_val_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_259_, lean_object* v_motive_260_, lean_object* v_____do__lift_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_){
_start:
{
if (lean_obj_tag(v_____do__lift_261_) == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_h__2_263_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_1(v_h__1_262_, v___x_264_);
return v___x_265_;
}
else
{
lean_object* v_val_266_; lean_object* v___x_267_; 
lean_dec(v_h__1_262_);
v_val_266_ = lean_ctor_get(v_____do__lift_261_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v_____do__lift_261_, 1);
v___x_267_ = lean_apply_1(v_h__2_263_, v_val_266_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(lean_object* v_____do__lift_268_, lean_object* v_h__1_269_, lean_object* v_h__2_270_){
_start:
{
if (lean_obj_tag(v_____do__lift_268_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_h__1_269_);
v___x_271_ = lean_box(0);
v___x_272_ = lean_apply_1(v_h__2_270_, v___x_271_);
return v___x_272_;
}
else
{
lean_object* v_val_273_; lean_object* v___x_274_; 
lean_dec(v_h__2_270_);
v_val_273_ = lean_ctor_get(v_____do__lift_268_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v_____do__lift_268_, 1);
v___x_274_ = lean_apply_1(v_h__1_269_, v_val_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter(lean_object* v_00_u03b2_275_, lean_object* v_motive_276_, lean_object* v_____do__lift_277_, lean_object* v_h__1_278_, lean_object* v_h__2_279_){
_start:
{
if (lean_obj_tag(v_____do__lift_277_) == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_h__1_278_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_apply_1(v_h__2_279_, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v_val_282_; lean_object* v___x_283_; 
lean_dec(v_h__2_279_);
v_val_282_ = lean_ctor_get(v_____do__lift_277_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v_____do__lift_277_, 1);
v___x_283_ = lean_apply_1(v_h__1_278_, v_val_282_);
return v___x_283_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
