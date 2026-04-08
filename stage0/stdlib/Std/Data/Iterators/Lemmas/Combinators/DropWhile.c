// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.DropWhile
// Imports: public import Std.Data.Iterators.Combinators.DropWhile public import Std.Data.Iterators.Lemmas.Combinators.Monadic.DropWhile public import Init.Data.Iterators.Lemmas.Consumers import Init.Data.Bool import Init.Data.Iterators.Lemmas.Basic import Init.Data.List.TakeDrop
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_11_, lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
switch(lean_obj_tag(v_x_17_))
{
case 0:
{
lean_object* v_it_21_; lean_object* v_out_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__2_19_);
v_it_21_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_21_);
v_out_22_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_out_22_);
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_3(v_h__1_18_, v_it_21_, v_out_22_, lean_box(0));
return v___x_23_;
}
case 1:
{
lean_object* v_it_24_; lean_object* v___x_25_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__1_18_);
v_it_24_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_24_);
lean_dec_ref(v_x_17_);
v___x_25_ = lean_apply_2(v_h__2_19_, v_it_24_, lean_box(0));
return v___x_25_;
}
default: 
{
lean_object* v___x_26_; 
lean_dec(v_h__2_19_);
lean_dec(v_h__1_18_);
v___x_26_ = lean_apply_1(v_h__3_20_, lean_box(0));
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_m_28_, lean_object* v_00_u03b2_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(v_00_u03b1_27_, v_m_28_, v_00_u03b2_29_, v_inst_30_, v_it_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec(v_it_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(uint8_t v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
if (v_x_38_ == 0)
{
lean_object* v___x_41_; 
lean_dec(v_h__1_39_);
v___x_41_ = lean_apply_1(v_h__2_40_, lean_box(0));
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
lean_dec(v_h__2_40_);
v___x_42_ = lean_apply_1(v_h__1_39_, lean_box(0));
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
uint8_t v_x_26__boxed_46_; lean_object* v_res_47_; 
v_x_26__boxed_46_ = lean_unbox(v_x_43_);
v_res_47_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_46_, v_h__1_44_, v_h__2_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(lean_object* v_motive_48_, uint8_t v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (v_x_49_ == 0)
{
lean_object* v___x_52_; 
lean_dec(v_h__1_50_);
v___x_52_ = lean_apply_1(v_h__2_51_, lean_box(0));
return v___x_52_;
}
else
{
lean_object* v___x_53_; 
lean_dec(v_h__2_51_);
v___x_53_ = lean_apply_1(v_h__1_50_, lean_box(0));
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___boxed(lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
uint8_t v_x_33__boxed_58_; lean_object* v_res_59_; 
v_x_33__boxed_58_ = lean_unbox(v_x_55_);
v_res_59_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(v_motive_54_, v_x_33__boxed_58_, v_h__1_56_, v_h__2_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___redArg(lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_){
_start:
{
switch(lean_obj_tag(v_x_60_))
{
case 0:
{
lean_object* v_it_64_; lean_object* v_out_65_; lean_object* v___x_66_; 
lean_dec(v_h__3_63_);
lean_dec(v_h__2_62_);
v_it_64_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_it_64_);
v_out_65_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_out_65_);
lean_dec_ref(v_x_60_);
v___x_66_ = lean_apply_3(v_h__1_61_, v_it_64_, v_out_65_, lean_box(0));
return v___x_66_;
}
case 1:
{
lean_object* v_it_67_; lean_object* v___x_68_; 
lean_dec(v_h__3_63_);
lean_dec(v_h__1_61_);
v_it_67_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_it_67_);
lean_dec_ref(v_x_60_);
v___x_68_ = lean_apply_2(v_h__2_62_, v_it_67_, lean_box(0));
return v___x_68_;
}
default: 
{
lean_object* v___x_69_; 
lean_dec(v_h__2_62_);
lean_dec(v_h__1_61_);
v___x_69_ = lean_apply_1(v_h__3_63_, lean_box(0));
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_inst_72_, lean_object* v_it_73_, lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
lean_object* v_it_79_; lean_object* v_out_80_; lean_object* v___x_81_; 
lean_dec(v_h__3_78_);
lean_dec(v_h__2_77_);
v_it_79_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_it_79_);
v_out_80_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_out_80_);
lean_dec_ref(v_x_75_);
v___x_81_ = lean_apply_3(v_h__1_76_, v_it_79_, v_out_80_, lean_box(0));
return v___x_81_;
}
case 1:
{
lean_object* v_it_82_; lean_object* v___x_83_; 
lean_dec(v_h__3_78_);
lean_dec(v_h__1_76_);
v_it_82_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_it_82_);
lean_dec_ref(v_x_75_);
v___x_83_ = lean_apply_2(v_h__2_77_, v_it_82_, lean_box(0));
return v___x_83_;
}
default: 
{
lean_object* v___x_84_; 
lean_dec(v_h__2_77_);
lean_dec(v_h__1_76_);
v___x_84_ = lean_apply_1(v_h__3_78_, lean_box(0));
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___boxed(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_inst_87_, lean_object* v_it_88_, lean_object* v_motive_89_, lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_, lean_object* v_h__3_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(v_00_u03b1_85_, v_00_u03b2_86_, v_inst_87_, v_it_88_, v_motive_89_, v_x_90_, v_h__1_91_, v_h__2_92_, v_h__3_93_);
lean_dec(v_it_88_);
lean_dec(v_inst_87_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(uint8_t v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
if (v_x_95_ == 0)
{
lean_object* v___x_98_; 
lean_dec(v_h__1_96_);
v___x_98_ = lean_apply_1(v_h__2_97_, lean_box(0));
return v___x_98_;
}
else
{
lean_object* v___x_99_; 
lean_dec(v_h__2_97_);
v___x_99_ = lean_apply_1(v_h__1_96_, lean_box(0));
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
uint8_t v_x_26__boxed_103_; lean_object* v_res_104_; 
v_x_26__boxed_103_ = lean_unbox(v_x_100_);
v_res_104_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_103_, v_h__1_101_, v_h__2_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(lean_object* v_motive_105_, uint8_t v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
if (v_x_106_ == 0)
{
lean_object* v___x_109_; 
lean_dec(v_h__1_107_);
v___x_109_ = lean_apply_1(v_h__2_108_, lean_box(0));
return v___x_109_;
}
else
{
lean_object* v___x_110_; 
lean_dec(v_h__2_108_);
v___x_110_ = lean_apply_1(v_h__1_107_, lean_box(0));
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___boxed(lean_object* v_motive_111_, lean_object* v_x_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
uint8_t v_x_33__boxed_115_; lean_object* v_res_116_; 
v_x_33__boxed_115_ = lean_unbox(v_x_112_);
v_res_116_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(v_motive_111_, v_x_33__boxed_115_, v_h__1_113_, v_h__2_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(uint8_t v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_){
_start:
{
if (v_x_117_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__1_118_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__2_119_, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_h__2_119_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_1(v_h__1_118_, v___x_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object* v_x_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
uint8_t v_x_26__boxed_127_; lean_object* v_res_128_; 
v_x_26__boxed_127_ = lean_unbox(v_x_124_);
v_res_128_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_127_, v_h__1_125_, v_h__2_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(lean_object* v_motive_129_, uint8_t v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
if (v_x_130_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__1_131_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_1(v_h__2_132_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_132_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__1_131_, v___x_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___boxed(lean_object* v_motive_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
uint8_t v_x_37__boxed_141_; lean_object* v_res_142_; 
v_x_37__boxed_141_ = lean_unbox(v_x_138_);
v_res_142_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(v_motive_137_, v_x_37__boxed_141_, v_h__1_139_, v_h__2_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter___redArg(lean_object* v_x_143_, lean_object* v_h__1_144_, lean_object* v_h__2_145_, lean_object* v_h__3_146_){
_start:
{
switch(lean_obj_tag(v_x_143_))
{
case 0:
{
lean_object* v_it_147_; lean_object* v_out_148_; lean_object* v___x_149_; 
lean_dec(v_h__3_146_);
lean_dec(v_h__2_145_);
v_it_147_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_it_147_);
v_out_148_ = lean_ctor_get(v_x_143_, 1);
lean_inc(v_out_148_);
lean_dec_ref(v_x_143_);
v___x_149_ = lean_apply_2(v_h__1_144_, v_it_147_, v_out_148_);
return v___x_149_;
}
case 1:
{
lean_object* v_it_150_; lean_object* v___x_151_; 
lean_dec(v_h__3_146_);
lean_dec(v_h__1_144_);
v_it_150_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_it_150_);
lean_dec_ref(v_x_143_);
v___x_151_ = lean_apply_1(v_h__2_145_, v_it_150_);
return v___x_151_;
}
default: 
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_h__2_145_);
lean_dec(v_h__1_144_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_apply_1(v_h__3_146_, v___x_152_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter(lean_object* v_00_u03b1_154_, lean_object* v_00_u03b2_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_, lean_object* v_h__3_160_){
_start:
{
switch(lean_obj_tag(v_x_157_))
{
case 0:
{
lean_object* v_it_161_; lean_object* v_out_162_; lean_object* v___x_163_; 
lean_dec(v_h__3_160_);
lean_dec(v_h__2_159_);
v_it_161_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_it_161_);
v_out_162_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_out_162_);
lean_dec_ref(v_x_157_);
v___x_163_ = lean_apply_2(v_h__1_158_, v_it_161_, v_out_162_);
return v___x_163_;
}
case 1:
{
lean_object* v_it_164_; lean_object* v___x_165_; 
lean_dec(v_h__3_160_);
lean_dec(v_h__1_158_);
v_it_164_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_it_164_);
lean_dec_ref(v_x_157_);
v___x_165_ = lean_apply_1(v_h__2_159_, v_it_164_);
return v___x_165_;
}
default: 
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_159_);
lean_dec(v_h__1_158_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__3_160_, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_, lean_object* v_h__3_171_){
_start:
{
switch(lean_obj_tag(v_x_168_))
{
case 0:
{
lean_object* v_it_172_; lean_object* v_out_173_; lean_object* v___x_174_; 
lean_dec(v_h__3_171_);
lean_dec(v_h__2_170_);
v_it_172_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_it_172_);
v_out_173_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_out_173_);
lean_dec_ref(v_x_168_);
v___x_174_ = lean_apply_2(v_h__1_169_, v_it_172_, v_out_173_);
return v___x_174_;
}
case 1:
{
lean_object* v_it_175_; lean_object* v___x_176_; 
lean_dec(v_h__3_171_);
lean_dec(v_h__1_169_);
v_it_175_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_it_175_);
lean_dec_ref(v_x_168_);
v___x_176_ = lean_apply_1(v_h__2_170_, v_it_175_);
return v___x_176_;
}
default: 
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__2_170_);
lean_dec(v_h__1_169_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__3_171_, v___x_177_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_motive_181_, lean_object* v_x_182_, lean_object* v_h__1_183_, lean_object* v_h__2_184_, lean_object* v_h__3_185_){
_start:
{
switch(lean_obj_tag(v_x_182_))
{
case 0:
{
lean_object* v_it_186_; lean_object* v_out_187_; lean_object* v___x_188_; 
lean_dec(v_h__3_185_);
lean_dec(v_h__2_184_);
v_it_186_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_it_186_);
v_out_187_ = lean_ctor_get(v_x_182_, 1);
lean_inc(v_out_187_);
lean_dec_ref(v_x_182_);
v___x_188_ = lean_apply_2(v_h__1_183_, v_it_186_, v_out_187_);
return v___x_188_;
}
case 1:
{
lean_object* v_it_189_; lean_object* v___x_190_; 
lean_dec(v_h__3_185_);
lean_dec(v_h__1_183_);
v_it_189_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_it_189_);
lean_dec_ref(v_x_182_);
v___x_190_ = lean_apply_1(v_h__2_184_, v_it_189_);
return v___x_190_;
}
default: 
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_h__2_184_);
lean_dec(v_h__1_183_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_1(v_h__3_185_, v___x_191_);
return v___x_192_;
}
}
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_DropWhile(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
}
#ifdef __cplusplus
}
#endif
