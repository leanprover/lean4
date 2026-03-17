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
lean_object* v___x_21_; 
v___x_21_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_, v_h__3_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_m_23_, lean_object* v_00_u03b2_24_, lean_object* v_inst_25_, lean_object* v_it_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(v_00_u03b1_22_, v_m_23_, v_00_u03b2_24_, v_inst_25_, v_it_26_, v_motive_27_, v_x_28_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
lean_dec(v_it_26_);
lean_dec(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(uint8_t v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (v_x_33_ == 0)
{
lean_object* v___x_36_; 
lean_dec(v_h__1_34_);
v___x_36_ = lean_apply_1(v_h__2_35_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v___x_37_; 
lean_dec(v_h__2_35_);
v___x_37_ = lean_apply_1(v_h__1_34_, lean_box(0));
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
uint8_t v_x_24__boxed_41_; lean_object* v_res_42_; 
v_x_24__boxed_41_ = lean_unbox(v_x_38_);
v_res_42_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(v_x_24__boxed_41_, v_h__1_39_, v_h__2_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(lean_object* v_motive_43_, uint8_t v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(v_x_44_, v_h__1_45_, v_h__2_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___boxed(lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
uint8_t v_x_31__boxed_52_; lean_object* v_res_53_; 
v_x_31__boxed_52_ = lean_unbox(v_x_49_);
v_res_53_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(v_motive_48_, v_x_31__boxed_52_, v_h__1_50_, v_h__2_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___redArg(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
switch(lean_obj_tag(v_x_54_))
{
case 0:
{
lean_object* v_it_58_; lean_object* v_out_59_; lean_object* v___x_60_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__2_56_);
v_it_58_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_it_58_);
v_out_59_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_out_59_);
lean_dec_ref(v_x_54_);
v___x_60_ = lean_apply_3(v_h__1_55_, v_it_58_, v_out_59_, lean_box(0));
return v___x_60_;
}
case 1:
{
lean_object* v_it_61_; lean_object* v___x_62_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__1_55_);
v_it_61_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_it_61_);
lean_dec_ref(v_x_54_);
v___x_62_ = lean_apply_2(v_h__2_56_, v_it_61_, lean_box(0));
return v___x_62_;
}
default: 
{
lean_object* v___x_63_; 
lean_dec(v_h__2_56_);
lean_dec(v_h__1_55_);
v___x_63_ = lean_apply_1(v_h__3_57_, lean_box(0));
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_inst_66_, lean_object* v_it_67_, lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_, lean_object* v_h__3_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___redArg(v_x_69_, v_h__1_70_, v_h__2_71_, v_h__3_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___boxed(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_inst_76_, lean_object* v_it_77_, lean_object* v_motive_78_, lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_, lean_object* v_h__3_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(v_00_u03b1_74_, v_00_u03b2_75_, v_inst_76_, v_it_77_, v_motive_78_, v_x_79_, v_h__1_80_, v_h__2_81_, v_h__3_82_);
lean_dec(v_it_77_);
lean_dec(v_inst_76_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(uint8_t v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
if (v_x_84_ == 0)
{
lean_object* v___x_87_; 
lean_dec(v_h__1_85_);
v___x_87_ = lean_apply_1(v_h__2_86_, lean_box(0));
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec(v_h__2_86_);
v___x_88_ = lean_apply_1(v_h__1_85_, lean_box(0));
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
uint8_t v_x_24__boxed_92_; lean_object* v_res_93_; 
v_x_24__boxed_92_ = lean_unbox(v_x_89_);
v_res_93_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(v_x_24__boxed_92_, v_h__1_90_, v_h__2_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(lean_object* v_motive_94_, uint8_t v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(v_x_95_, v_h__1_96_, v_h__2_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___boxed(lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
uint8_t v_x_31__boxed_103_; lean_object* v_res_104_; 
v_x_31__boxed_103_ = lean_unbox(v_x_100_);
v_res_104_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(v_motive_99_, v_x_31__boxed_103_, v_h__1_101_, v_h__2_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(uint8_t v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (v_x_105_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_106_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_1(v_h__2_107_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_107_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_apply_1(v_h__1_106_, v___x_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg___boxed(lean_object* v_x_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
uint8_t v_x_22__boxed_115_; lean_object* v_res_116_; 
v_x_22__boxed_115_ = lean_unbox(v_x_112_);
v_res_116_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(v_x_22__boxed_115_, v_h__1_113_, v_h__2_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(lean_object* v_motive_117_, uint8_t v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(v_x_118_, v_h__1_119_, v_h__2_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___boxed(lean_object* v_motive_122_, lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
uint8_t v_x_33__boxed_126_; lean_object* v_res_127_; 
v_x_33__boxed_126_ = lean_unbox(v_x_123_);
v_res_127_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(v_motive_122_, v_x_33__boxed_126_, v_h__1_124_, v_h__2_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter___redArg(lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_, lean_object* v_h__3_131_){
_start:
{
switch(lean_obj_tag(v_x_128_))
{
case 0:
{
lean_object* v_it_132_; lean_object* v_out_133_; lean_object* v___x_134_; 
lean_dec(v_h__3_131_);
lean_dec(v_h__2_130_);
v_it_132_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_it_132_);
v_out_133_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_out_133_);
lean_dec_ref(v_x_128_);
v___x_134_ = lean_apply_2(v_h__1_129_, v_it_132_, v_out_133_);
return v___x_134_;
}
case 1:
{
lean_object* v_it_135_; lean_object* v___x_136_; 
lean_dec(v_h__3_131_);
lean_dec(v_h__1_129_);
v_it_135_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_it_135_);
lean_dec_ref(v_x_128_);
v___x_136_ = lean_apply_1(v_h__2_130_, v_it_135_);
return v___x_136_;
}
default: 
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_130_);
lean_dec(v_h__1_129_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__3_131_, v___x_137_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_, lean_object* v_h__3_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter___redArg(v_x_142_, v_h__1_143_, v_h__2_144_, v_h__3_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_, lean_object* v_h__3_150_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_158_, lean_object* v_00_u03b2_159_, lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_, lean_object* v_h__3_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(v_x_161_, v_h__1_162_, v_h__2_163_, v_h__3_164_);
return v___x_165_;
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
