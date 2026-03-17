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
lean_object* v___x_20_; 
v___x_20_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(v_x_16_, v_h__1_17_, v_h__2_18_, v_h__3_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_inst_23_, lean_object* v_it_24_, lean_object* v_motive_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_, lean_object* v_h__3_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_21_, v_00_u03b2_22_, v_inst_23_, v_it_24_, v_motive_25_, v_x_26_, v_h__1_27_, v_h__2_28_, v_h__3_29_);
lean_dec(v_it_24_);
lean_dec(v_inst_23_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
if (lean_obj_tag(v_____do__lift_31_) == 0)
{
lean_object* v_a_34_; lean_object* v___x_35_; 
lean_dec(v_h__1_32_);
v_a_34_ = lean_ctor_get(v_____do__lift_31_, 0);
lean_inc(v_a_34_);
lean_dec_ref(v_____do__lift_31_);
v___x_35_ = lean_apply_1(v_h__2_33_, v_a_34_);
return v___x_35_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_33_);
v_a_36_ = lean_ctor_get(v_____do__lift_31_, 0);
lean_inc(v_a_36_);
lean_dec_ref(v_____do__lift_31_);
v___x_37_ = lean_apply_1(v_h__1_32_, v_a_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_38_, lean_object* v_motive_39_, lean_object* v_____do__lift_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(v_____do__lift_40_, v_h__1_41_, v_h__2_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
_start:
{
switch(lean_obj_tag(v_x_44_))
{
case 0:
{
lean_object* v_it_48_; lean_object* v_out_49_; lean_object* v___x_50_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__2_46_);
v_it_48_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_it_48_);
v_out_49_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_out_49_);
lean_dec_ref(v_x_44_);
v___x_50_ = lean_apply_3(v_h__1_45_, v_it_48_, v_out_49_, lean_box(0));
return v___x_50_;
}
case 1:
{
lean_object* v_it_51_; lean_object* v___x_52_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__1_45_);
v_it_51_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_it_51_);
lean_dec_ref(v_x_44_);
v___x_52_ = lean_apply_2(v_h__2_46_, v_it_51_, lean_box(0));
return v___x_52_;
}
default: 
{
lean_object* v___x_53_; 
lean_dec(v_h__2_46_);
lean_dec(v_h__1_45_);
v___x_53_ = lean_apply_1(v_h__3_47_, lean_box(0));
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_m_56_, lean_object* v_inst_57_, lean_object* v_it_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(v_x_60_, v_h__1_61_, v_h__2_62_, v_h__3_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_65_, lean_object* v_00_u03b2_66_, lean_object* v_m_67_, lean_object* v_inst_68_, lean_object* v_it_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_, lean_object* v_h__3_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_65_, v_00_u03b2_66_, v_m_67_, v_inst_68_, v_it_69_, v_motive_70_, v_x_71_, v_h__1_72_, v_h__2_73_, v_h__3_74_);
lean_dec(v_it_69_);
lean_dec(v_inst_68_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_){
_start:
{
if (lean_obj_tag(v_____do__lift_76_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec(v_h__1_77_);
v_a_79_ = lean_ctor_get(v_____do__lift_76_, 0);
lean_inc(v_a_79_);
lean_dec_ref(v_____do__lift_76_);
v___x_80_ = lean_apply_2(v_h__2_78_, v_a_79_, lean_box(0));
return v___x_80_;
}
else
{
lean_object* v_a_81_; lean_object* v___x_82_; 
lean_dec(v_h__2_78_);
v_a_81_ = lean_ctor_get(v_____do__lift_76_, 0);
lean_inc(v_a_81_);
lean_dec_ref(v_____do__lift_76_);
v___x_82_ = lean_apply_2(v_h__1_77_, v_a_81_, lean_box(0));
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b2_83_, lean_object* v_00_u03b3_84_, lean_object* v_init_85_, lean_object* v_PlausibleForInStep_86_, lean_object* v_out_87_, lean_object* v_motive_88_, lean_object* v_____do__lift_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(v_____do__lift_89_, v_h__1_90_, v_h__2_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object* v_00_u03b2_93_, lean_object* v_00_u03b3_94_, lean_object* v_init_95_, lean_object* v_PlausibleForInStep_96_, lean_object* v_out_97_, lean_object* v_motive_98_, lean_object* v_____do__lift_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_93_, v_00_u03b3_94_, v_init_95_, v_PlausibleForInStep_96_, v_out_97_, v_motive_98_, v_____do__lift_99_, v_h__1_100_, v_h__2_101_);
lean_dec(v_out_97_);
lean_dec(v_init_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_, lean_object* v_h__3_106_){
_start:
{
switch(lean_obj_tag(v_x_103_))
{
case 0:
{
lean_object* v_it_107_; lean_object* v_out_108_; lean_object* v___x_109_; 
lean_dec(v_h__3_106_);
lean_dec(v_h__2_105_);
v_it_107_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_it_107_);
v_out_108_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_out_108_);
lean_dec_ref(v_x_103_);
v___x_109_ = lean_apply_2(v_h__1_104_, v_it_107_, v_out_108_);
return v___x_109_;
}
case 1:
{
lean_object* v_it_110_; lean_object* v___x_111_; 
lean_dec(v_h__3_106_);
lean_dec(v_h__1_104_);
v_it_110_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_it_110_);
lean_dec_ref(v_x_103_);
v___x_111_ = lean_apply_1(v_h__2_105_, v_it_110_);
return v___x_111_;
}
default: 
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_h__2_105_);
lean_dec(v_h__1_104_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_apply_1(v_h__3_106_, v___x_112_);
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_motive_116_, lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_, lean_object* v_h__3_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(v_x_117_, v_h__1_118_, v_h__2_119_, v_h__3_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
if (lean_obj_tag(v_b_122_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; 
lean_dec(v_h__1_123_);
v_a_125_ = lean_ctor_get(v_b_122_, 0);
lean_inc(v_a_125_);
lean_dec_ref(v_b_122_);
v___x_126_ = lean_apply_1(v_h__2_124_, v_a_125_);
return v___x_126_;
}
else
{
lean_object* v_a_127_; lean_object* v___x_128_; 
lean_dec(v_h__2_124_);
v_a_127_ = lean_ctor_get(v_b_122_, 0);
lean_inc(v_a_127_);
lean_dec_ref(v_b_122_);
v___x_128_ = lean_apply_1(v_h__1_123_, v_a_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_129_, lean_object* v_motive_130_, lean_object* v_b_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(v_b_131_, v_h__1_132_, v_h__2_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_, lean_object* v_h__3_138_){
_start:
{
switch(lean_obj_tag(v_x_135_))
{
case 0:
{
lean_object* v_it_139_; lean_object* v_out_140_; lean_object* v___x_141_; 
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
v_it_139_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_it_139_);
v_out_140_ = lean_ctor_get(v_x_135_, 1);
lean_inc(v_out_140_);
lean_dec_ref(v_x_135_);
v___x_141_ = lean_apply_2(v_h__1_136_, v_it_139_, v_out_140_);
return v___x_141_;
}
case 1:
{
lean_object* v_it_142_; lean_object* v___x_143_; 
lean_dec(v_h__3_138_);
lean_dec(v_h__1_136_);
v_it_142_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_it_142_);
lean_dec_ref(v_x_135_);
v___x_143_ = lean_apply_1(v_h__2_137_, v_it_142_);
return v___x_143_;
}
default: 
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_apply_1(v_h__3_138_, v___x_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_, lean_object* v_h__3_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(v_x_149_, v_h__1_150_, v_h__2_151_, v_h__3_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_, lean_object* v_h__3_157_){
_start:
{
switch(lean_obj_tag(v_x_154_))
{
case 0:
{
lean_object* v_it_158_; lean_object* v_out_159_; lean_object* v___x_160_; 
lean_dec(v_h__3_157_);
lean_dec(v_h__2_156_);
v_it_158_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_it_158_);
v_out_159_ = lean_ctor_get(v_x_154_, 1);
lean_inc(v_out_159_);
lean_dec_ref(v_x_154_);
v___x_160_ = lean_apply_2(v_h__1_155_, v_it_158_, v_out_159_);
return v___x_160_;
}
case 1:
{
lean_object* v_it_161_; lean_object* v___x_162_; 
lean_dec(v_h__3_157_);
lean_dec(v_h__1_155_);
v_it_161_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_it_161_);
lean_dec_ref(v_x_154_);
v___x_162_ = lean_apply_1(v_h__2_156_, v_it_161_);
return v___x_162_;
}
default: 
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_h__2_156_);
lean_dec(v_h__1_155_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_apply_1(v_h__3_157_, v___x_163_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_m_167_, lean_object* v_motive_168_, lean_object* v_x_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_, lean_object* v_h__3_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(v_x_169_, v_h__1_170_, v_h__2_171_, v_h__3_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_){
_start:
{
if (lean_obj_tag(v_____do__lift_174_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__2_176_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__1_175_, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v_val_179_; lean_object* v___x_180_; 
lean_dec(v_h__1_175_);
v_val_179_ = lean_ctor_get(v_____do__lift_174_, 0);
lean_inc(v_val_179_);
lean_dec_ref(v_____do__lift_174_);
v___x_180_ = lean_apply_1(v_h__2_176_, v_val_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b3_181_, lean_object* v_motive_182_, lean_object* v_____do__lift_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(v_____do__lift_183_, v_h__1_184_, v_h__2_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
if (lean_obj_tag(v_____do__lift_187_) == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_h__2_189_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_apply_1(v_h__1_188_, v___x_190_);
return v___x_191_;
}
else
{
lean_object* v_val_192_; lean_object* v___x_193_; 
lean_dec(v_h__1_188_);
v_val_192_ = lean_ctor_get(v_____do__lift_187_, 0);
lean_inc(v_val_192_);
lean_dec_ref(v_____do__lift_187_);
v___x_193_ = lean_apply_1(v_h__2_189_, v_val_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_194_, lean_object* v_motive_195_, lean_object* v_____do__lift_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(v_____do__lift_196_, v_h__1_197_, v_h__2_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(lean_object* v_____do__lift_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
if (lean_obj_tag(v_____do__lift_200_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__1_201_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_h__2_202_, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; 
lean_dec(v_h__2_202_);
v_val_205_ = lean_ctor_get(v_____do__lift_200_, 0);
lean_inc(v_val_205_);
lean_dec_ref(v_____do__lift_200_);
v___x_206_ = lean_apply_1(v_h__1_201_, v_val_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter(lean_object* v_00_u03b2_207_, lean_object* v_motive_208_, lean_object* v_____do__lift_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(v_____do__lift_209_, v_h__1_210_, v_h__2_211_);
return v___x_212_;
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
