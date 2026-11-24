// Lean compiler output
// Module: Init.Data.List.Find
// Imports: import all Init.Data.List.Attach public import Init.Data.List.Attach import Init.Data.Fin.Lemmas import Init.Data.List.Impl import Init.Data.List.Range import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas import Init.Data.Prod import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__2_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_19_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_apply_1(v_h__1_18_, v___x_20_);
return v___x_21_;
}
else
{
lean_object* v_head_22_; lean_object* v_tail_23_; lean_object* v___x_24_; 
lean_dec(v_h__1_18_);
v_head_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_head_22_);
v_tail_23_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_tail_23_);
lean_dec_ref_known(v_x_17_, 2);
v___x_24_ = lean_apply_2(v_h__2_19_, v_head_22_, v_tail_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; 
lean_dec(v_h__2_29_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_apply_1(v_h__1_28_, v___x_30_);
return v___x_31_;
}
else
{
lean_object* v_head_32_; lean_object* v_tail_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_28_);
v_head_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_head_32_);
v_tail_33_ = lean_ctor_get(v_x_27_, 1);
lean_inc(v_tail_33_);
lean_dec_ref_known(v_x_27_, 2);
v___x_34_ = lean_apply_2(v_h__2_29_, v_head_32_, v_tail_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(uint8_t v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (v_x_35_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_36_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__2_37_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_37_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_36_, v___x_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
uint8_t v_x_24__boxed_45_; lean_object* v_res_46_; 
v_x_24__boxed_45_ = lean_unbox(v_x_42_);
v_res_46_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_45_, v_h__1_43_, v_h__2_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(lean_object* v_motive_47_, uint8_t v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
if (v_x_48_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__1_49_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__2_50_, v___x_51_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__2_50_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__1_49_, v___x_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
uint8_t v_x_35__boxed_59_; lean_object* v_res_60_; 
v_x_35__boxed_59_ = lean_unbox(v_x_56_);
v_res_60_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(v_motive_55_, v_x_35__boxed_59_, v_h__1_57_, v_h__2_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_63_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_1(v_h__1_62_, v___x_64_);
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_62_);
v_val_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_val_66_);
lean_dec_ref_known(v_x_61_, 1);
v___x_67_ = lean_apply_1(v_h__2_63_, v_val_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_68_, lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_72_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__1_71_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_71_);
v_val_75_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v_x_70_, 1);
v___x_76_ = lean_apply_1(v_h__2_72_, v_val_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_77_, lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_81_; 
lean_dec(v_h__2_80_);
v___x_81_ = lean_apply_1(v_h__1_79_, v_x_78_);
return v___x_81_;
}
else
{
lean_object* v_head_82_; lean_object* v_tail_83_; lean_object* v___x_84_; 
lean_dec(v_h__1_79_);
v_head_82_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_head_82_);
v_tail_83_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_tail_83_);
lean_dec_ref_known(v_x_77_, 2);
v___x_84_ = lean_apply_3(v_h__2_80_, v_head_82_, v_tail_83_, v_x_78_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_85_, lean_object* v_motive_86_, lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_91_; 
lean_dec(v_h__2_90_);
v___x_91_ = lean_apply_1(v_h__1_89_, v_x_88_);
return v___x_91_;
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_89_);
v_head_92_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_92_);
v_tail_93_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_tail_93_);
lean_dec_ref_known(v_x_87_, 2);
v___x_94_ = lean_apply_3(v_h__2_90_, v_head_92_, v_tail_93_, v_x_88_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_h__1_96_);
v___x_98_ = lean_box(0);
v___x_99_ = lean_apply_1(v_h__2_97_, v___x_98_);
return v___x_99_;
}
else
{
lean_object* v_val_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_97_);
v_val_100_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_val_100_);
lean_dec_ref_known(v_x_95_, 1);
v___x_101_ = lean_apply_1(v_h__1_96_, v_val_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object* v_00_u03b1_102_, lean_object* v_motive_103_, lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_h__1_105_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_1(v_h__2_106_, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_106_);
v_val_109_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v_x_104_, 1);
v___x_110_ = lean_apply_1(v_h__1_105_, v_val_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object* v_x_111_, lean_object* v_x_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
lean_object* v___x_115_; 
lean_dec(v_h__2_114_);
v___x_115_ = lean_apply_2(v_h__1_113_, v_x_112_, lean_box(0));
return v___x_115_;
}
else
{
lean_object* v_head_116_; lean_object* v_tail_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_113_);
v_head_116_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_head_116_);
v_tail_117_ = lean_ctor_get(v_x_111_, 1);
lean_inc(v_tail_117_);
lean_dec_ref_known(v_x_111_, 2);
v___x_118_ = lean_apply_4(v_h__2_114_, v_head_116_, v_tail_117_, v_x_112_, lean_box(0));
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object* v_00_u03b1_119_, lean_object* v_l_120_, lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v___x_127_; 
lean_dec(v_h__2_126_);
v___x_127_ = lean_apply_2(v_h__1_125_, v_x_123_, lean_box(0));
return v___x_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_tail_129_; lean_object* v___x_130_; 
lean_dec(v_h__1_125_);
v_head_128_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_head_128_);
v_tail_129_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_tail_129_);
lean_dec_ref_known(v_x_122_, 2);
v___x_130_ = lean_apply_4(v_h__2_126_, v_head_128_, v_tail_129_, v_x_123_, lean_box(0));
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object* v_00_u03b1_131_, lean_object* v_l_132_, lean_object* v_motive_133_, lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(v_00_u03b1_131_, v_l_132_, v_motive_133_, v_x_134_, v_x_135_, v_x_136_, v_h__1_137_, v_h__2_138_);
lean_dec(v_l_132_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object* v_o_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
if (lean_obj_tag(v_o_140_) == 0)
{
lean_object* v___x_143_; 
lean_dec(v_h__2_142_);
v___x_143_ = lean_apply_1(v_h__1_141_, lean_box(0));
return v___x_143_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_145_; 
lean_dec(v_h__1_141_);
v_val_144_ = lean_ctor_get(v_o_140_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v_o_140_, 1);
v___x_145_ = lean_apply_2(v_h__2_142_, v_val_144_, lean_box(0));
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(lean_object* v_00_u03b1_146_, lean_object* v_p_147_, lean_object* v_o_x27_148_, lean_object* v_motive_149_, lean_object* v_o_150_, lean_object* v_h_151_, lean_object* v_h__1_152_, lean_object* v_h__2_153_){
_start:
{
if (lean_obj_tag(v_o_150_) == 0)
{
lean_object* v___x_154_; 
lean_dec(v_h__2_153_);
v___x_154_ = lean_apply_1(v_h__1_152_, lean_box(0));
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_156_; 
lean_dec(v_h__1_152_);
v_val_155_ = lean_ctor_get(v_o_150_, 0);
lean_inc(v_val_155_);
lean_dec_ref_known(v_o_150_, 1);
v___x_156_ = lean_apply_2(v_h__2_153_, v_val_155_, lean_box(0));
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object* v_00_u03b1_157_, lean_object* v_p_158_, lean_object* v_o_x27_159_, lean_object* v_motive_160_, lean_object* v_o_161_, lean_object* v_h_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(v_00_u03b1_157_, v_p_158_, v_o_x27_159_, v_motive_160_, v_o_161_, v_h_162_, v_h__1_163_, v_h__2_164_);
lean_dec(v_o_x27_159_);
return v_res_165_;
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Find(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Find(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Find(builtin);
}
#ifdef __cplusplus
}
#endif
