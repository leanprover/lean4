// Lean compiler output
// Module: Std.Data.DHashMap.Internal.AssocList.Lemmas
// Imports: public import Std.Data.DHashMap.Internal.AssocList.Basic import all Std.Data.DHashMap.Internal.AssocList.Basic public import Std.Data.Internal.List.Associative import Init.ByCases import Init.Data.Array.Bootstrap
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_h__2_4_);
v___x_5_ = lean_apply_1(v_h__1_3_, v_x_1_);
return v___x_5_;
}
else
{
lean_object* v_key_6_; lean_object* v_value_7_; lean_object* v_tail_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_3_);
v_key_6_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_key_6_);
v_value_7_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_value_7_);
v_tail_8_ = lean_ctor_get(v_x_2_, 2);
lean_inc(v_tail_8_);
lean_dec_ref(v_x_2_);
v___x_9_ = lean_apply_4(v_h__2_4_, v_x_1_, v_key_6_, v_value_7_, v_tail_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_00_u03b4_12_, lean_object* v_motive_13_, lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(v_x_14_, v_x_15_, v_h__1_16_, v_h__2_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter___redArg(lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_21_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_20_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v_key_24_; lean_object* v_value_25_; lean_object* v_tail_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_20_);
v_key_24_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_key_24_);
v_value_25_ = lean_ctor_get(v_x_19_, 1);
lean_inc(v_value_25_);
v_tail_26_ = lean_ctor_get(v_x_19_, 2);
lean_inc(v_tail_26_);
lean_dec_ref(v_x_19_);
v___x_27_ = lean_apply_3(v_h__2_21_, v_key_24_, v_value_25_, v_tail_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter___redArg(v_x_31_, v_h__1_32_, v_h__2_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_37_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__1_36_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_key_40_; lean_object* v_value_41_; lean_object* v_tail_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_36_);
v_key_40_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_key_40_);
v_value_41_ = lean_ctor_get(v_x_35_, 1);
lean_inc(v_value_41_);
v_tail_42_ = lean_ctor_get(v_x_35_, 2);
lean_inc(v_tail_42_);
lean_dec_ref(v_x_35_);
v___x_43_ = lean_apply_3(v_h__2_37_, v_key_40_, v_value_41_, v_tail_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(v_x_47_, v_h__1_48_, v_h__2_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_){
_start:
{
lean_object* v_key_53_; lean_object* v_value_54_; lean_object* v_tail_55_; lean_object* v___x_56_; 
v_key_53_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_key_53_);
v_value_54_ = lean_ctor_get(v_x_51_, 1);
lean_inc(v_value_54_);
v_tail_55_ = lean_ctor_get(v_x_51_, 2);
lean_inc(v_tail_55_);
lean_dec(v_x_51_);
v___x_56_ = lean_apply_4(v_h__1_52_, v_key_53_, v_value_54_, v_tail_55_, lean_box(0));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_inst_59_, lean_object* v_a_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_h__1_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(v_x_62_, v_h__1_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___boxed(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_inst_68_, lean_object* v_a_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_h__1_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(v_00_u03b1_66_, v_00_u03b2_67_, v_inst_68_, v_a_69_, v_motive_70_, v_x_71_, v_x_72_, v_h__1_73_);
lean_dec(v_a_69_);
lean_dec_ref(v_inst_68_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_h__1_76_){
_start:
{
lean_object* v_key_77_; lean_object* v_value_78_; lean_object* v_tail_79_; lean_object* v___x_80_; 
v_key_77_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_key_77_);
v_value_78_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_value_78_);
v_tail_79_ = lean_ctor_get(v_x_75_, 2);
lean_inc(v_tail_79_);
lean_dec(v_x_75_);
v___x_80_ = lean_apply_4(v_h__1_76_, v_key_77_, v_value_78_, v_tail_79_, lean_box(0));
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_inst_83_, lean_object* v_a_84_, lean_object* v_motive_85_, lean_object* v_x_86_, lean_object* v_x_87_, lean_object* v_h__1_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(v_x_86_, v_h__1_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___boxed(lean_object* v_00_u03b1_90_, lean_object* v_00_u03b2_91_, lean_object* v_inst_92_, lean_object* v_a_93_, lean_object* v_motive_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_h__1_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(v_00_u03b1_90_, v_00_u03b2_91_, v_inst_92_, v_a_93_, v_motive_94_, v_x_95_, v_x_96_, v_h__1_97_);
lean_dec(v_a_93_);
lean_dec_ref(v_inst_92_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_h__2_101_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_apply_1(v_h__1_100_, v___x_102_);
return v___x_103_;
}
else
{
lean_object* v_val_104_; lean_object* v___x_105_; 
lean_dec(v_h__1_100_);
v_val_104_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_val_104_);
lean_dec_ref(v_x_99_);
v___x_105_ = lean_apply_1(v_h__2_101_, v_val_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_a_108_, lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(v_x_110_, v_h__1_111_, v_h__2_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_a_116_, lean_object* v_motive_117_, lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(v_00_u03b1_114_, v_00_u03b2_115_, v_a_116_, v_motive_117_, v_x_118_, v_h__1_119_, v_h__2_120_);
lean_dec(v_a_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_124_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_apply_1(v_h__1_123_, v___x_125_);
return v___x_126_;
}
else
{
lean_object* v_val_127_; lean_object* v___x_128_; 
lean_dec(v_h__1_123_);
v_val_127_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_val_127_);
lean_dec_ref(v_x_122_);
v___x_128_ = lean_apply_1(v_h__2_124_, v_val_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_129_, lean_object* v_motive_130_, lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(v_x_131_, v_h__1_132_, v_h__2_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__2_137_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__1_136_, v___x_138_);
return v___x_139_;
}
else
{
lean_object* v_val_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_136_);
v_val_140_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v_x_135_);
v___x_141_ = lean_apply_1(v_h__2_137_, v_val_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_k_144_, lean_object* v_motive_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(v_x_146_, v_h__1_147_, v_h__2_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_k_152_, lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_150_, v_00_u03b2_151_, v_k_152_, v_motive_153_, v_x_154_, v_h__1_155_, v_h__2_156_);
lean_dec(v_k_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(lean_object* v_x_158_, lean_object* v_h__1_159_, lean_object* v_h__2_160_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_h__2_160_);
v___x_161_ = lean_box(0);
v___x_162_ = lean_apply_1(v_h__1_159_, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v_val_163_; lean_object* v___x_164_; 
lean_dec(v_h__1_159_);
v_val_163_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_val_163_);
lean_dec_ref(v_x_158_);
v___x_164_ = lean_apply_1(v_h__2_160_, v_val_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter(lean_object* v_00_u03b2_165_, lean_object* v_motive_166_, lean_object* v_x_167_, lean_object* v_h__1_168_, lean_object* v_h__2_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(v_x_167_, v_h__1_168_, v_h__2_169_);
return v___x_170_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
