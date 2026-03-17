// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Zip
// Imports: public import Std.Data.Iterators.Combinators.Zip public import Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip public import Init.Data.Iterators.Lemmas.Combinators.Take import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Access import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.List.ToArray import Init.Data.List.Zip
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(lean_object* v_memo_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_memo_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_memo_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_memo_1_);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(lean_object* v_00_u03b1_u2081_8_, lean_object* v_00_u03b2_u2081_9_, lean_object* v_m_10_, lean_object* v_inst_11_, lean_object* v_motive_12_, lean_object* v_memo_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(v_memo_13_, v_h__1_14_, v_h__2_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(lean_object* v_00_u03b1_u2081_17_, lean_object* v_00_u03b2_u2081_18_, lean_object* v_m_19_, lean_object* v_inst_20_, lean_object* v_motive_21_, lean_object* v_memo_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_17_, v_00_u03b2_u2081_18_, v_m_19_, v_inst_20_, v_motive_21_, v_memo_22_, v_h__1_23_, v_h__2_24_);
lean_dec(v_inst_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_, lean_object* v_h__3_29_){
_start:
{
switch(lean_obj_tag(v_x_26_))
{
case 0:
{
lean_object* v_it_30_; lean_object* v_out_31_; lean_object* v___x_32_; 
lean_dec(v_h__3_29_);
lean_dec(v_h__2_28_);
v_it_30_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_it_30_);
v_out_31_ = lean_ctor_get(v_x_26_, 1);
lean_inc(v_out_31_);
lean_dec_ref(v_x_26_);
v___x_32_ = lean_apply_3(v_h__1_27_, v_it_30_, v_out_31_, lean_box(0));
return v___x_32_;
}
case 1:
{
lean_object* v_it_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_29_);
lean_dec(v_h__1_27_);
v_it_33_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_it_33_);
lean_dec_ref(v_x_26_);
v___x_34_ = lean_apply_2(v_h__2_28_, v_it_33_, lean_box(0));
return v___x_34_;
}
default: 
{
lean_object* v___x_35_; 
lean_dec(v_h__2_28_);
lean_dec(v_h__1_27_);
v___x_35_ = lean_apply_1(v_h__3_29_, lean_box(0));
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(lean_object* v_00_u03b1_u2081_36_, lean_object* v_00_u03b2_u2081_37_, lean_object* v_m_38_, lean_object* v_inst_39_, lean_object* v_it_u2081_40_, lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_, lean_object* v_h__3_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(v_x_42_, v_h__1_43_, v_h__2_44_, v_h__3_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(lean_object* v_00_u03b1_u2081_47_, lean_object* v_00_u03b2_u2081_48_, lean_object* v_m_49_, lean_object* v_inst_50_, lean_object* v_it_u2081_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_47_, v_00_u03b2_u2081_48_, v_m_49_, v_inst_50_, v_it_u2081_51_, v_motive_52_, v_x_53_, v_h__1_54_, v_h__2_55_, v_h__3_56_);
lean_dec(v_it_u2081_51_);
lean_dec(v_inst_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(lean_object* v_memo_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_memo_58_) == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_60_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_apply_1(v_h__1_59_, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v_val_63_; lean_object* v___x_64_; 
lean_dec(v_h__1_59_);
v_val_63_ = lean_ctor_get(v_memo_58_, 0);
lean_inc(v_val_63_);
lean_dec_ref(v_memo_58_);
v___x_64_ = lean_apply_1(v_h__2_60_, v_val_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(lean_object* v_00_u03b1_u2081_65_, lean_object* v_00_u03b2_u2081_66_, lean_object* v_inst_67_, lean_object* v_motive_68_, lean_object* v_memo_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(v_memo_69_, v_h__1_70_, v_h__2_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___boxed(lean_object* v_00_u03b1_u2081_73_, lean_object* v_00_u03b2_u2081_74_, lean_object* v_inst_75_, lean_object* v_motive_76_, lean_object* v_memo_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_73_, v_00_u03b2_u2081_74_, v_inst_75_, v_motive_76_, v_memo_77_, v_h__1_78_, v_h__2_79_);
lean_dec(v_inst_75_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
_start:
{
switch(lean_obj_tag(v_x_81_))
{
case 0:
{
lean_object* v_it_85_; lean_object* v_out_86_; lean_object* v___x_87_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__2_83_);
v_it_85_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_it_85_);
v_out_86_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_out_86_);
lean_dec_ref(v_x_81_);
v___x_87_ = lean_apply_3(v_h__1_82_, v_it_85_, v_out_86_, lean_box(0));
return v___x_87_;
}
case 1:
{
lean_object* v_it_88_; lean_object* v___x_89_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__1_82_);
v_it_88_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_it_88_);
lean_dec_ref(v_x_81_);
v___x_89_ = lean_apply_2(v_h__2_83_, v_it_88_, lean_box(0));
return v___x_89_;
}
default: 
{
lean_object* v___x_90_; 
lean_dec(v_h__2_83_);
lean_dec(v_h__1_82_);
v___x_90_ = lean_apply_1(v_h__3_84_, lean_box(0));
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(lean_object* v_00_u03b1_u2081_91_, lean_object* v_00_u03b2_u2081_92_, lean_object* v_inst_93_, lean_object* v_it_u2081_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(v_x_96_, v_h__1_97_, v_h__2_98_, v_h__3_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___boxed(lean_object* v_00_u03b1_u2081_101_, lean_object* v_00_u03b2_u2081_102_, lean_object* v_inst_103_, lean_object* v_it_u2081_104_, lean_object* v_motive_105_, lean_object* v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_, lean_object* v_h__3_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_101_, v_00_u03b2_u2081_102_, v_inst_103_, v_it_u2081_104_, v_motive_105_, v_x_106_, v_h__1_107_, v_h__2_108_, v_h__3_109_);
lean_dec(v_it_u2081_104_);
lean_dec(v_inst_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_){
_start:
{
switch(lean_obj_tag(v_x_111_))
{
case 0:
{
lean_object* v_it_115_; lean_object* v_out_116_; lean_object* v___x_117_; 
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
v_it_115_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_it_115_);
v_out_116_ = lean_ctor_get(v_x_111_, 1);
lean_inc(v_out_116_);
lean_dec_ref(v_x_111_);
v___x_117_ = lean_apply_3(v_h__1_112_, v_it_115_, v_out_116_, lean_box(0));
return v___x_117_;
}
case 1:
{
lean_object* v_it_118_; lean_object* v___x_119_; 
lean_dec(v_h__3_114_);
lean_dec(v_h__1_112_);
v_it_118_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_it_118_);
lean_dec_ref(v_x_111_);
v___x_119_ = lean_apply_2(v_h__2_113_, v_it_118_, lean_box(0));
return v___x_119_;
}
default: 
{
lean_object* v___x_120_; 
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v___x_120_ = lean_apply_1(v_h__3_114_, lean_box(0));
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_inst_123_, lean_object* v_it_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_, lean_object* v_h__3_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(v_x_126_, v_h__1_127_, v_h__2_128_, v_h__3_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object* v_00_u03b1_131_, lean_object* v_00_u03b2_132_, lean_object* v_inst_133_, lean_object* v_it_134_, lean_object* v_motive_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_, lean_object* v_h__3_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_131_, v_00_u03b2_132_, v_inst_133_, v_it_134_, v_motive_135_, v_x_136_, v_h__1_137_, v_h__2_138_, v_h__3_139_);
lean_dec(v_it_134_);
lean_dec(v_inst_133_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object* v_n_141_, lean_object* v_recur_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
lean_object* v_zero_145_; uint8_t v_isZero_146_; 
v_zero_145_ = lean_unsigned_to_nat(0u);
v_isZero_146_ = lean_nat_dec_eq(v_n_141_, v_zero_145_);
if (v_isZero_146_ == 1)
{
lean_object* v___x_147_; 
lean_dec(v_h__2_144_);
v___x_147_ = lean_apply_1(v_h__1_143_, v_recur_142_);
return v___x_147_;
}
else
{
lean_object* v_one_148_; lean_object* v_n_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_143_);
v_one_148_ = lean_unsigned_to_nat(1u);
v_n_149_ = lean_nat_sub(v_n_141_, v_one_148_);
v___x_150_ = lean_apply_2(v_h__2_144_, v_n_149_, v_recur_142_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object* v_n_151_, lean_object* v_recur_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_151_, v_recur_152_, v_h__1_153_, v_h__2_154_);
lean_dec(v_n_151_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_inst_158_, lean_object* v_it_159_, lean_object* v_motive_160_, lean_object* v_n_161_, lean_object* v_recur_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_161_, v_recur_162_, v_h__1_163_, v_h__2_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_, lean_object* v_it_169_, lean_object* v_motive_170_, lean_object* v_n_171_, lean_object* v_recur_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_166_, v_00_u03b2_167_, v_inst_168_, v_it_169_, v_motive_170_, v_n_171_, v_recur_172_, v_h__1_173_, v_h__2_174_);
lean_dec(v_n_171_);
lean_dec(v_it_169_);
lean_dec(v_inst_168_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(lean_object* v_n_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_){
_start:
{
lean_object* v_zero_179_; uint8_t v_isZero_180_; 
v_zero_179_ = lean_unsigned_to_nat(0u);
v_isZero_180_ = lean_nat_dec_eq(v_n_176_, v_zero_179_);
if (v_isZero_180_ == 1)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_h__2_178_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_1(v_h__1_177_, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_one_183_; lean_object* v_n_184_; lean_object* v___x_185_; 
lean_dec(v_h__1_177_);
v_one_183_ = lean_unsigned_to_nat(1u);
v_n_184_ = lean_nat_sub(v_n_176_, v_one_183_);
v___x_185_ = lean_apply_1(v_h__2_178_, v_n_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg___boxed(lean_object* v_n_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(v_n_186_, v_h__1_187_, v_h__2_188_);
lean_dec(v_n_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(lean_object* v_motive_190_, lean_object* v_n_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(v_n_191_, v_h__1_192_, v_h__2_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___boxed(lean_object* v_motive_195_, lean_object* v_n_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(v_motive_195_, v_n_196_, v_h__1_197_, v_h__2_198_);
lean_dec(v_n_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object* v_n_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
lean_object* v_zero_203_; uint8_t v_isZero_204_; 
v_zero_203_ = lean_unsigned_to_nat(0u);
v_isZero_204_ = lean_nat_dec_eq(v_n_200_, v_zero_203_);
if (v_isZero_204_ == 1)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_h__2_202_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_apply_1(v_h__1_201_, v___x_205_);
return v___x_206_;
}
else
{
lean_object* v_one_207_; lean_object* v_n_208_; lean_object* v___x_209_; 
lean_dec(v_h__1_201_);
v_one_207_ = lean_unsigned_to_nat(1u);
v_n_208_ = lean_nat_sub(v_n_200_, v_one_207_);
v___x_209_ = lean_apply_1(v_h__2_202_, v_n_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object* v_n_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_210_, v_h__1_211_, v_h__2_212_);
lean_dec(v_n_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object* v_motive_214_, lean_object* v_n_215_, lean_object* v_h__1_216_, lean_object* v_h__2_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_215_, v_h__1_216_, v_h__2_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object* v_motive_219_, lean_object* v_n_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_219_, v_n_220_, v_h__1_221_, v_h__2_222_);
lean_dec(v_n_220_);
return v_res_223_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
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
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
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
res = initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
}
#ifdef __cplusplus
}
#endif
