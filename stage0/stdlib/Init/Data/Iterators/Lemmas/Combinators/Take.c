// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Take
// Imports: public import Init.Data.Iterators.Combinators.Take public import Init.Data.Iterators.Lemmas.Combinators.Monadic.Take public import Init.Data.Iterators.Consumers.Access public import Init.Data.Iterators.Consumers.Collect import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Access import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.List.Nat.TakeDrop
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg(lean_object* v_n_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_n_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_2_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_n_1_, v_one_8_);
v___x_10_ = lean_apply_1(v_h__2_3_, v_n_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(lean_object* v_n_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_11_, v_h__1_12_, v_h__2_13_);
lean_dec(v_n_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter(lean_object* v_motive_15_, lean_object* v_n_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v_zero_19_; uint8_t v_isZero_20_; 
v_zero_19_ = lean_unsigned_to_nat(0u);
v_isZero_20_ = lean_nat_dec_eq(v_n_16_, v_zero_19_);
if (v_isZero_20_ == 1)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_18_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_17_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_17_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_n_16_, v_one_23_);
v___x_25_ = lean_apply_1(v_h__2_18_, v_n_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___boxed(lean_object* v_motive_26_, lean_object* v_n_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_26_, v_n_27_, v_h__1_28_, v_h__2_29_);
lean_dec(v_n_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___redArg(lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_, lean_object* v_h__3_34_){
_start:
{
switch(lean_obj_tag(v_x_31_))
{
case 0:
{
lean_object* v_it_35_; lean_object* v_out_36_; lean_object* v___x_37_; 
lean_dec(v_h__3_34_);
lean_dec(v_h__2_33_);
v_it_35_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_it_35_);
v_out_36_ = lean_ctor_get(v_x_31_, 1);
lean_inc(v_out_36_);
lean_dec_ref(v_x_31_);
v___x_37_ = lean_apply_3(v_h__1_32_, v_it_35_, v_out_36_, lean_box(0));
return v___x_37_;
}
case 1:
{
lean_object* v_it_38_; lean_object* v___x_39_; 
lean_dec(v_h__3_34_);
lean_dec(v_h__1_32_);
v_it_38_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_it_38_);
lean_dec_ref(v_x_31_);
v___x_39_ = lean_apply_2(v_h__2_33_, v_it_38_, lean_box(0));
return v___x_39_;
}
default: 
{
lean_object* v___x_40_; 
lean_dec(v_h__2_33_);
lean_dec(v_h__1_32_);
v___x_40_ = lean_apply_1(v_h__3_34_, lean_box(0));
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter(lean_object* v_00_u03b1_41_, lean_object* v_m_42_, lean_object* v_00_u03b2_43_, lean_object* v_inst_44_, lean_object* v_it_45_, lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_, lean_object* v_h__3_50_){
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
v___x_53_ = lean_apply_3(v_h__1_48_, v_it_51_, v_out_52_, lean_box(0));
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
v___x_55_ = lean_apply_2(v_h__2_49_, v_it_54_, lean_box(0));
return v___x_55_;
}
default: 
{
lean_object* v___x_56_; 
lean_dec(v_h__2_49_);
lean_dec(v_h__1_48_);
v___x_56_ = lean_apply_1(v_h__3_50_, lean_box(0));
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___boxed(lean_object* v_00_u03b1_57_, lean_object* v_m_58_, lean_object* v_00_u03b2_59_, lean_object* v_inst_60_, lean_object* v_it_61_, lean_object* v_motive_62_, lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_, lean_object* v_h__3_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_57_, v_m_58_, v_00_u03b2_59_, v_inst_60_, v_it_61_, v_motive_62_, v_x_63_, v_h__1_64_, v_h__2_65_, v_h__3_66_);
lean_dec(v_it_61_);
lean_dec(v_inst_60_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(lean_object* v_n_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
lean_object* v_zero_71_; uint8_t v_isZero_72_; 
v_zero_71_ = lean_unsigned_to_nat(0u);
v_isZero_72_ = lean_nat_dec_eq(v_n_68_, v_zero_71_);
if (v_isZero_72_ == 1)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_70_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__1_69_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_one_75_; lean_object* v_n_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_69_);
v_one_75_ = lean_unsigned_to_nat(1u);
v_n_76_ = lean_nat_sub(v_n_68_, v_one_75_);
v___x_77_ = lean_apply_1(v_h__2_70_, v_n_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg___boxed(lean_object* v_n_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(v_n_78_, v_h__1_79_, v_h__2_80_);
lean_dec(v_n_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter(lean_object* v_motive_82_, lean_object* v_n_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
lean_object* v_zero_86_; uint8_t v_isZero_87_; 
v_zero_86_ = lean_unsigned_to_nat(0u);
v_isZero_87_ = lean_nat_dec_eq(v_n_83_, v_zero_86_);
if (v_isZero_87_ == 1)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_85_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__1_84_, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v_one_90_; lean_object* v_n_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_84_);
v_one_90_ = lean_unsigned_to_nat(1u);
v_n_91_ = lean_nat_sub(v_n_83_, v_one_90_);
v___x_92_ = lean_apply_1(v_h__2_85_, v_n_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___boxed(lean_object* v_motive_93_, lean_object* v_n_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter(v_motive_93_, v_n_94_, v_h__1_95_, v_h__2_96_);
lean_dec(v_n_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___redArg(lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_, lean_object* v_h__3_101_){
_start:
{
switch(lean_obj_tag(v_x_98_))
{
case 0:
{
lean_object* v_it_102_; lean_object* v_out_103_; lean_object* v___x_104_; 
lean_dec(v_h__3_101_);
lean_dec(v_h__2_100_);
v_it_102_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_it_102_);
v_out_103_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_out_103_);
lean_dec_ref(v_x_98_);
v___x_104_ = lean_apply_3(v_h__1_99_, v_it_102_, v_out_103_, lean_box(0));
return v___x_104_;
}
case 1:
{
lean_object* v_it_105_; lean_object* v___x_106_; 
lean_dec(v_h__3_101_);
lean_dec(v_h__1_99_);
v_it_105_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_it_105_);
lean_dec_ref(v_x_98_);
v___x_106_ = lean_apply_2(v_h__2_100_, v_it_105_, lean_box(0));
return v___x_106_;
}
default: 
{
lean_object* v___x_107_; 
lean_dec(v_h__2_100_);
lean_dec(v_h__1_99_);
v___x_107_ = lean_apply_1(v_h__3_101_, lean_box(0));
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_inst_110_, lean_object* v_it_111_, lean_object* v_motive_112_, lean_object* v_x_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_, lean_object* v_h__3_116_){
_start:
{
switch(lean_obj_tag(v_x_113_))
{
case 0:
{
lean_object* v_it_117_; lean_object* v_out_118_; lean_object* v___x_119_; 
lean_dec(v_h__3_116_);
lean_dec(v_h__2_115_);
v_it_117_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_it_117_);
v_out_118_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_out_118_);
lean_dec_ref(v_x_113_);
v___x_119_ = lean_apply_3(v_h__1_114_, v_it_117_, v_out_118_, lean_box(0));
return v___x_119_;
}
case 1:
{
lean_object* v_it_120_; lean_object* v___x_121_; 
lean_dec(v_h__3_116_);
lean_dec(v_h__1_114_);
v_it_120_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_it_120_);
lean_dec_ref(v_x_113_);
v___x_121_ = lean_apply_2(v_h__2_115_, v_it_120_, lean_box(0));
return v___x_121_;
}
default: 
{
lean_object* v___x_122_; 
lean_dec(v_h__2_115_);
lean_dec(v_h__1_114_);
v___x_122_ = lean_apply_1(v_h__3_116_, lean_box(0));
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_inst_125_, lean_object* v_it_126_, lean_object* v_motive_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_, lean_object* v_h__3_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter(v_00_u03b1_123_, v_00_u03b2_124_, v_inst_125_, v_it_126_, v_motive_127_, v_x_128_, v_h__1_129_, v_h__2_130_, v_h__3_131_);
lean_dec(v_it_126_);
lean_dec(v_inst_125_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_, lean_object* v_h__3_136_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_motive_146_, lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_, lean_object* v_h__3_150_){
_start:
{
switch(lean_obj_tag(v_x_147_))
{
case 0:
{
lean_object* v_it_151_; lean_object* v_out_152_; lean_object* v___x_153_; 
lean_dec(v_h__3_150_);
lean_dec(v_h__2_149_);
v_it_151_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_it_151_);
v_out_152_ = lean_ctor_get(v_x_147_, 1);
lean_inc(v_out_152_);
lean_dec_ref(v_x_147_);
v___x_153_ = lean_apply_2(v_h__1_148_, v_it_151_, v_out_152_);
return v___x_153_;
}
case 1:
{
lean_object* v_it_154_; lean_object* v___x_155_; 
lean_dec(v_h__3_150_);
lean_dec(v_h__1_148_);
v_it_154_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_it_154_);
lean_dec_ref(v_x_147_);
v___x_155_ = lean_apply_1(v_h__2_149_, v_it_154_);
return v___x_155_;
}
default: 
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_h__2_149_);
lean_dec(v_h__1_148_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_1(v_h__3_150_, v___x_156_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object* v_n_158_, lean_object* v_h__1_159_, lean_object* v_h__2_160_){
_start:
{
lean_object* v_zero_161_; uint8_t v_isZero_162_; 
v_zero_161_ = lean_unsigned_to_nat(0u);
v_isZero_162_ = lean_nat_dec_eq(v_n_158_, v_zero_161_);
if (v_isZero_162_ == 1)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_h__2_160_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_apply_1(v_h__1_159_, v___x_163_);
return v___x_164_;
}
else
{
lean_object* v_one_165_; lean_object* v_n_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_159_);
v_one_165_ = lean_unsigned_to_nat(1u);
v_n_166_ = lean_nat_sub(v_n_158_, v_one_165_);
v___x_167_ = lean_apply_1(v_h__2_160_, v_n_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object* v_n_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_168_, v_h__1_169_, v_h__2_170_);
lean_dec(v_n_168_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object* v_motive_172_, lean_object* v_n_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
lean_object* v_zero_176_; uint8_t v_isZero_177_; 
v_zero_176_ = lean_unsigned_to_nat(0u);
v_isZero_177_ = lean_nat_dec_eq(v_n_173_, v_zero_176_);
if (v_isZero_177_ == 1)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_h__2_175_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_apply_1(v_h__1_174_, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_one_180_; lean_object* v_n_181_; lean_object* v___x_182_; 
lean_dec(v_h__1_174_);
v_one_180_ = lean_unsigned_to_nat(1u);
v_n_181_ = lean_nat_sub(v_n_173_, v_one_180_);
v___x_182_ = lean_apply_1(v_h__2_175_, v_n_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object* v_motive_183_, lean_object* v_n_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_183_, v_n_184_, v_h__1_185_, v_h__2_186_);
lean_dec(v_n_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_, lean_object* v_h__3_191_){
_start:
{
switch(lean_obj_tag(v_x_188_))
{
case 0:
{
lean_object* v_it_192_; lean_object* v_out_193_; lean_object* v___x_194_; 
lean_dec(v_h__3_191_);
lean_dec(v_h__2_190_);
v_it_192_ = lean_ctor_get(v_x_188_, 0);
lean_inc(v_it_192_);
v_out_193_ = lean_ctor_get(v_x_188_, 1);
lean_inc(v_out_193_);
lean_dec_ref(v_x_188_);
v___x_194_ = lean_apply_2(v_h__1_189_, v_it_192_, v_out_193_);
return v___x_194_;
}
case 1:
{
lean_object* v_it_195_; lean_object* v___x_196_; 
lean_dec(v_h__3_191_);
lean_dec(v_h__1_189_);
v_it_195_ = lean_ctor_get(v_x_188_, 0);
lean_inc(v_it_195_);
lean_dec_ref(v_x_188_);
v___x_196_ = lean_apply_1(v_h__2_190_, v_it_195_);
return v___x_196_;
}
default: 
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__2_190_);
lean_dec(v_h__1_189_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_apply_1(v_h__3_191_, v___x_197_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_motive_201_, lean_object* v_x_202_, lean_object* v_h__1_203_, lean_object* v_h__2_204_, lean_object* v_h__3_205_){
_start:
{
switch(lean_obj_tag(v_x_202_))
{
case 0:
{
lean_object* v_it_206_; lean_object* v_out_207_; lean_object* v___x_208_; 
lean_dec(v_h__3_205_);
lean_dec(v_h__2_204_);
v_it_206_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_it_206_);
v_out_207_ = lean_ctor_get(v_x_202_, 1);
lean_inc(v_out_207_);
lean_dec_ref(v_x_202_);
v___x_208_ = lean_apply_2(v_h__1_203_, v_it_206_, v_out_207_);
return v___x_208_;
}
case 1:
{
lean_object* v_it_209_; lean_object* v___x_210_; 
lean_dec(v_h__3_205_);
lean_dec(v_h__1_203_);
v_it_209_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_it_209_);
lean_dec_ref(v_x_202_);
v___x_210_ = lean_apply_1(v_h__2_204_, v_it_209_);
return v___x_210_;
}
default: 
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__2_204_);
lean_dec(v_h__1_203_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_1(v_h__3_205_, v___x_211_);
return v___x_212_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
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
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
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
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
}
#ifdef __cplusplus
}
#endif
