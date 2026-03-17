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
lean_object* v___x_19_; 
v___x_19_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_16_, v_h__1_17_, v_h__2_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter___boxed(lean_object* v_motive_20_, lean_object* v_n_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_20_, v_n_21_, v_h__1_22_, v_h__2_23_);
lean_dec(v_n_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___redArg(lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_, lean_object* v_h__3_28_){
_start:
{
switch(lean_obj_tag(v_x_25_))
{
case 0:
{
lean_object* v_it_29_; lean_object* v_out_30_; lean_object* v___x_31_; 
lean_dec(v_h__3_28_);
lean_dec(v_h__2_27_);
v_it_29_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_it_29_);
v_out_30_ = lean_ctor_get(v_x_25_, 1);
lean_inc(v_out_30_);
lean_dec_ref(v_x_25_);
v___x_31_ = lean_apply_3(v_h__1_26_, v_it_29_, v_out_30_, lean_box(0));
return v___x_31_;
}
case 1:
{
lean_object* v_it_32_; lean_object* v___x_33_; 
lean_dec(v_h__3_28_);
lean_dec(v_h__1_26_);
v_it_32_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_it_32_);
lean_dec_ref(v_x_25_);
v___x_33_ = lean_apply_2(v_h__2_27_, v_it_32_, lean_box(0));
return v___x_33_;
}
default: 
{
lean_object* v___x_34_; 
lean_dec(v_h__2_27_);
lean_dec(v_h__1_26_);
v___x_34_ = lean_apply_1(v_h__3_28_, lean_box(0));
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter(lean_object* v_00_u03b1_35_, lean_object* v_m_36_, lean_object* v_00_u03b2_37_, lean_object* v_inst_38_, lean_object* v_it_39_, lean_object* v_motive_40_, lean_object* v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_, lean_object* v_h__3_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___redArg(v_x_41_, v_h__1_42_, v_h__2_43_, v_h__3_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter___boxed(lean_object* v_00_u03b1_46_, lean_object* v_m_47_, lean_object* v_00_u03b2_48_, lean_object* v_inst_49_, lean_object* v_it_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_, lean_object* v_h__3_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_46_, v_m_47_, v_00_u03b2_48_, v_inst_49_, v_it_50_, v_motive_51_, v_x_52_, v_h__1_53_, v_h__2_54_, v_h__3_55_);
lean_dec(v_it_50_);
lean_dec(v_inst_49_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(lean_object* v_n_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
lean_object* v_zero_60_; uint8_t v_isZero_61_; 
v_zero_60_ = lean_unsigned_to_nat(0u);
v_isZero_61_ = lean_nat_dec_eq(v_n_57_, v_zero_60_);
if (v_isZero_61_ == 1)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_59_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__1_58_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v_one_64_; lean_object* v_n_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_58_);
v_one_64_ = lean_unsigned_to_nat(1u);
v_n_65_ = lean_nat_sub(v_n_57_, v_one_64_);
v___x_66_ = lean_apply_1(v_h__2_59_, v_n_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg___boxed(lean_object* v_n_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(v_n_67_, v_h__1_68_, v_h__2_69_);
lean_dec(v_n_67_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter(lean_object* v_motive_71_, lean_object* v_n_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___redArg(v_n_72_, v_h__1_73_, v_h__2_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter___boxed(lean_object* v_motive_76_, lean_object* v_n_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__3_splitter(v_motive_76_, v_n_77_, v_h__1_78_, v_h__2_79_);
lean_dec(v_n_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___redArg(lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_inst_93_, lean_object* v_it_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___redArg(v_x_96_, v_h__1_97_, v_h__2_98_, v_h__3_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter___boxed(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_inst_103_, lean_object* v_it_104_, lean_object* v_motive_105_, lean_object* v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_, lean_object* v_h__3_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_step__take_match__1_splitter(v_00_u03b1_101_, v_00_u03b2_102_, v_inst_103_, v_it_104_, v_motive_105_, v_x_106_, v_h__1_107_, v_h__2_108_, v_h__3_109_);
lean_dec(v_it_104_);
lean_dec(v_inst_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_){
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
v___x_117_ = lean_apply_2(v_h__1_112_, v_it_115_, v_out_116_);
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
v___x_119_ = lean_apply_1(v_h__2_113_, v_it_118_);
return v___x_119_;
}
default: 
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__3_114_, v___x_120_);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_motive_124_, lean_object* v_x_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_, lean_object* v_h__3_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(v_x_125_, v_h__1_126_, v_h__2_127_, v_h__3_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object* v_n_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
lean_object* v_zero_133_; uint8_t v_isZero_134_; 
v_zero_133_ = lean_unsigned_to_nat(0u);
v_isZero_134_ = lean_nat_dec_eq(v_n_130_, v_zero_133_);
if (v_isZero_134_ == 1)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_132_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__1_131_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_one_137_; lean_object* v_n_138_; lean_object* v___x_139_; 
lean_dec(v_h__1_131_);
v_one_137_ = lean_unsigned_to_nat(1u);
v_n_138_ = lean_nat_sub(v_n_130_, v_one_137_);
v___x_139_ = lean_apply_1(v_h__2_132_, v_n_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object* v_n_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_140_, v_h__1_141_, v_h__2_142_);
lean_dec(v_n_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object* v_motive_144_, lean_object* v_n_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_145_, v_h__1_146_, v_h__2_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object* v_motive_149_, lean_object* v_n_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_149_, v_n_150_, v_h__1_151_, v_h__2_152_);
lean_dec(v_n_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_, lean_object* v_h__3_157_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_motive_167_, lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_, lean_object* v_h__3_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Take_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(v_x_168_, v_h__1_169_, v_h__2_170_, v_h__3_171_);
return v___x_172_;
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
