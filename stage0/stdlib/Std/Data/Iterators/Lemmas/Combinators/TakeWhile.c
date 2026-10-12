// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.TakeWhile
// Imports: public import Std.Data.Iterators.Combinators.TakeWhile public import Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile public import Std.Data.Iterators.Lemmas.Consumers import Init.Data.List.TakeDrop import Init.Data.List.ToArray import Init.Data.Option.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_11_, lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
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
lean_dec_ref_known(v_x_17_, 2);
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
lean_dec_ref_known(v_x_17_, 1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_m_28_, lean_object* v_00_u03b2_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(v_00_u03b1_27_, v_m_28_, v_00_u03b2_29_, v_inst_30_, v_it_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec(v_it_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(uint8_t v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
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
LEAN_EXPORT void l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_38_ = stack[0].m_num;
lean_object* v_h__1_39_ = stack[1].m_obj;
lean_object* v_h__2_40_ = stack[2].m_obj;
lean_object* v_res_43_;
v_res_43_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(v_x_38_, v_h__1_39_, v_h__2_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg___boxed(lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
uint8_t v_x_26__boxed_47_; lean_object* v_res_48_; 
v_x_26__boxed_47_ = lean_unbox(v_x_44_);
v_res_48_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_47_, v_h__1_45_, v_h__2_46_);
return v_res_48_;
}
}
lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(lean_object* v_motive_49_, uint8_t v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (v_x_50_ == 0)
{
lean_object* v___x_53_; 
lean_dec(v_h__1_51_);
v___x_53_ = lean_apply_1(v_h__2_52_, lean_box(0));
return v___x_53_;
}
else
{
lean_object* v___x_54_; 
lean_dec(v_h__2_52_);
v___x_54_ = lean_apply_1(v_h__1_51_, lean_box(0));
return v___x_54_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_50_ = stack[1].m_num;
lean_object* v_h__1_51_ = stack[2].m_obj;
lean_object* v_h__2_52_ = stack[3].m_obj;
lean_object* v_res_55_;
v_res_55_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(lean_box(0), v_x_50_, v_h__1_51_, v_h__2_52_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___boxed(lean_object* v_motive_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
uint8_t v_x_37__boxed_60_; lean_object* v_res_61_; 
v_x_37__boxed_60_ = lean_unbox(v_x_57_);
v_res_61_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(v_motive_56_, v_x_37__boxed_60_, v_h__1_58_, v_h__2_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___redArg(lean_object* v_x_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_, lean_object* v_h__3_65_){
_start:
{
switch(lean_obj_tag(v_x_62_))
{
case 0:
{
lean_object* v_it_66_; lean_object* v_out_67_; lean_object* v___x_68_; 
lean_dec(v_h__3_65_);
lean_dec(v_h__2_64_);
v_it_66_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_it_66_);
v_out_67_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_out_67_);
lean_dec_ref_known(v_x_62_, 2);
v___x_68_ = lean_apply_3(v_h__1_63_, v_it_66_, v_out_67_, lean_box(0));
return v___x_68_;
}
case 1:
{
lean_object* v_it_69_; lean_object* v___x_70_; 
lean_dec(v_h__3_65_);
lean_dec(v_h__1_63_);
v_it_69_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_it_69_);
lean_dec_ref_known(v_x_62_, 1);
v___x_70_ = lean_apply_2(v_h__2_64_, v_it_69_, lean_box(0));
return v___x_70_;
}
default: 
{
lean_object* v___x_71_; 
lean_dec(v_h__2_64_);
lean_dec(v_h__1_63_);
v___x_71_ = lean_apply_1(v_h__3_65_, lean_box(0));
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_inst_74_, lean_object* v_it_75_, lean_object* v_motive_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_, lean_object* v_h__3_80_){
_start:
{
switch(lean_obj_tag(v_x_77_))
{
case 0:
{
lean_object* v_it_81_; lean_object* v_out_82_; lean_object* v___x_83_; 
lean_dec(v_h__3_80_);
lean_dec(v_h__2_79_);
v_it_81_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_it_81_);
v_out_82_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_out_82_);
lean_dec_ref_known(v_x_77_, 2);
v___x_83_ = lean_apply_3(v_h__1_78_, v_it_81_, v_out_82_, lean_box(0));
return v___x_83_;
}
case 1:
{
lean_object* v_it_84_; lean_object* v___x_85_; 
lean_dec(v_h__3_80_);
lean_dec(v_h__1_78_);
v_it_84_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_it_84_);
lean_dec_ref_known(v_x_77_, 1);
v___x_85_ = lean_apply_2(v_h__2_79_, v_it_84_, lean_box(0));
return v___x_85_;
}
default: 
{
lean_object* v___x_86_; 
lean_dec(v_h__2_79_);
lean_dec(v_h__1_78_);
v___x_86_ = lean_apply_1(v_h__3_80_, lean_box(0));
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___boxed(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_inst_89_, lean_object* v_it_90_, lean_object* v_motive_91_, lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter(v_00_u03b1_87_, v_00_u03b2_88_, v_inst_89_, v_it_90_, v_motive_91_, v_x_92_, v_h__1_93_, v_h__2_94_, v_h__3_95_);
lean_dec(v_it_90_);
lean_dec(v_inst_89_);
return v_res_96_;
}
}
lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(uint8_t v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
if (v_x_97_ == 0)
{
lean_object* v___x_100_; 
lean_dec(v_h__1_98_);
v___x_100_ = lean_apply_1(v_h__2_99_, lean_box(0));
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
lean_dec(v_h__2_99_);
v___x_101_ = lean_apply_1(v_h__1_98_, lean_box(0));
return v___x_101_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_97_ = stack[0].m_num;
lean_object* v_h__1_98_ = stack[1].m_obj;
lean_object* v_h__2_99_ = stack[2].m_obj;
lean_object* v_res_102_;
v_res_102_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(v_x_97_, v_h__1_98_, v_h__2_99_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg___boxed(lean_object* v_x_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_){
_start:
{
uint8_t v_x_26__boxed_106_; lean_object* v_res_107_; 
v_x_26__boxed_106_ = lean_unbox(v_x_103_);
v_res_107_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_106_, v_h__1_104_, v_h__2_105_);
return v_res_107_;
}
}
lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(lean_object* v_motive_108_, uint8_t v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
if (v_x_109_ == 0)
{
lean_object* v___x_112_; 
lean_dec(v_h__1_110_);
v___x_112_ = lean_apply_1(v_h__2_111_, lean_box(0));
return v___x_112_;
}
else
{
lean_object* v___x_113_; 
lean_dec(v_h__2_111_);
v___x_113_ = lean_apply_1(v_h__1_110_, lean_box(0));
return v___x_113_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_109_ = stack[1].m_num;
lean_object* v_h__1_110_ = stack[2].m_obj;
lean_object* v_h__2_111_ = stack[3].m_obj;
lean_object* v_res_114_;
v_res_114_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(lean_box(0), v_x_109_, v_h__1_110_, v_h__2_111_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___boxed(lean_object* v_motive_115_, lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
uint8_t v_x_37__boxed_119_; lean_object* v_res_120_; 
v_x_37__boxed_119_ = lean_unbox(v_x_116_);
v_res_120_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(v_motive_115_, v_x_37__boxed_119_, v_h__1_117_, v_h__2_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter___redArg(lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_, lean_object* v_h__3_124_){
_start:
{
switch(lean_obj_tag(v_x_121_))
{
case 0:
{
lean_object* v_it_125_; lean_object* v_out_126_; lean_object* v___x_127_; 
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
v_it_125_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_it_125_);
v_out_126_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_out_126_);
lean_dec_ref_known(v_x_121_, 2);
v___x_127_ = lean_apply_2(v_h__1_122_, v_it_125_, v_out_126_);
return v___x_127_;
}
case 1:
{
lean_object* v_it_128_; lean_object* v___x_129_; 
lean_dec(v_h__3_124_);
lean_dec(v_h__1_122_);
v_it_128_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_it_128_);
lean_dec_ref_known(v_x_121_, 1);
v___x_129_ = lean_apply_1(v_h__2_123_, v_it_128_);
return v___x_129_;
}
default: 
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__3_124_, v___x_130_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_motive_134_, lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_, lean_object* v_h__3_138_){
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
lean_dec_ref_known(v_x_135_, 2);
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
lean_dec_ref_known(v_x_135_, 1);
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
lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(uint8_t v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
if (v_x_146_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_147_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v_h__2_148_, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_h__2_148_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_1(v_h__1_147_, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_146_ = stack[0].m_num;
lean_object* v_h__1_147_ = stack[1].m_obj;
lean_object* v_h__2_148_ = stack[2].m_obj;
lean_object* v_res_153_;
v_res_153_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(v_x_146_, v_h__1_147_, v_h__2_148_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg___boxed(lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
uint8_t v_x_24__boxed_157_; lean_object* v_res_158_; 
v_x_24__boxed_157_ = lean_unbox(v_x_154_);
v_res_158_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(v_x_24__boxed_157_, v_h__1_155_, v_h__2_156_);
return v_res_158_;
}
}
lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(lean_object* v_motive_159_, uint8_t v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_){
_start:
{
if (v_x_160_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_h__1_161_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_apply_1(v_h__2_162_, v___x_163_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_h__2_162_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v_h__1_161_, v___x_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_160_ = stack[1].m_num;
lean_object* v_h__1_161_ = stack[2].m_obj;
lean_object* v_h__2_162_ = stack[3].m_obj;
lean_object* v_res_167_;
v_res_167_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(lean_box(0), v_x_160_, v_h__1_161_, v_h__2_162_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___boxed(lean_object* v_motive_168_, lean_object* v_x_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_){
_start:
{
uint8_t v_x_41__boxed_172_; lean_object* v_res_173_; 
v_x_41__boxed_172_ = lean_unbox(v_x_169_);
v_res_173_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(v_motive_168_, v_x_41__boxed_172_, v_h__1_170_, v_h__2_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(lean_object* v_x_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_, lean_object* v_h__3_177_){
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
lean_dec_ref_known(v_x_174_, 2);
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
lean_dec_ref_known(v_x_174_, 1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(lean_object* v_00_u03b1_185_, lean_object* v_00_u03b2_186_, lean_object* v_motive_187_, lean_object* v_x_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_, lean_object* v_h__3_191_){
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
lean_dec_ref_known(v_x_188_, 2);
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
lean_dec_ref_known(v_x_188_, 1);
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object* v_n_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
lean_object* v_zero_202_; uint8_t v_isZero_203_; 
v_zero_202_ = lean_unsigned_to_nat(0u);
v_isZero_203_ = lean_nat_dec_eq(v_n_199_, v_zero_202_);
if (v_isZero_203_ == 1)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_h__2_201_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_apply_1(v_h__1_200_, v___x_204_);
return v___x_205_;
}
else
{
lean_object* v_one_206_; lean_object* v_n_207_; lean_object* v___x_208_; 
lean_dec(v_h__1_200_);
v_one_206_ = lean_unsigned_to_nat(1u);
v_n_207_ = lean_nat_sub(v_n_199_, v_one_206_);
v___x_208_ = lean_apply_1(v_h__2_201_, v_n_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object* v_n_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_209_, v_h__1_210_, v_h__2_211_);
lean_dec(v_n_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object* v_motive_213_, lean_object* v_n_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_){
_start:
{
lean_object* v_zero_217_; uint8_t v_isZero_218_; 
v_zero_217_ = lean_unsigned_to_nat(0u);
v_isZero_218_ = lean_nat_dec_eq(v_n_214_, v_zero_217_);
if (v_isZero_218_ == 1)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_h__2_216_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_apply_1(v_h__1_215_, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v_one_221_; lean_object* v_n_222_; lean_object* v___x_223_; 
lean_dec(v_h__1_215_);
v_one_221_ = lean_unsigned_to_nat(1u);
v_n_222_ = lean_nat_sub(v_n_214_, v_one_221_);
v___x_223_ = lean_apply_1(v_h__2_216_, v_n_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object* v_motive_224_, lean_object* v_n_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_224_, v_n_225_, v_h__1_226_, v_h__2_227_);
lean_dec(v_n_225_);
return v_res_228_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_TakeWhile(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Consumers(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
}
#ifdef __cplusplus
}
#endif
