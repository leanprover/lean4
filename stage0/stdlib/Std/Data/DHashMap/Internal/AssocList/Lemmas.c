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
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_18_; 
lean_dec(v_h__2_17_);
v___x_18_ = lean_apply_1(v_h__1_16_, v_x_14_);
return v___x_18_;
}
else
{
lean_object* v_key_19_; lean_object* v_value_20_; lean_object* v_tail_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_16_);
v_key_19_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_key_19_);
v_value_20_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_value_20_);
v_tail_21_ = lean_ctor_get(v_x_15_, 2);
lean_inc(v_tail_21_);
lean_dec_ref(v_x_15_);
v___x_22_ = lean_apply_4(v_h__2_17_, v_x_14_, v_key_19_, v_value_20_, v_tail_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter___redArg(lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_25_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_1(v_h__1_24_, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v_key_28_; lean_object* v_value_29_; lean_object* v_tail_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_24_);
v_key_28_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_key_28_);
v_value_29_ = lean_ctor_get(v_x_23_, 1);
lean_inc(v_value_29_);
v_tail_30_ = lean_ctor_get(v_x_23_, 2);
lean_inc(v_tail_30_);
lean_dec_ref(v_x_23_);
v___x_31_ = lean_apply_3(v_h__2_25_, v_key_28_, v_value_29_, v_tail_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_x3f_match__1_splitter(lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_motive_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_46_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__1_45_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_key_49_; lean_object* v_value_50_; lean_object* v_tail_51_; lean_object* v___x_52_; 
lean_dec(v_h__1_45_);
v_key_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_key_49_);
v_value_50_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_value_50_);
v_tail_51_ = lean_ctor_get(v_x_44_, 2);
lean_inc(v_tail_51_);
lean_dec_ref(v_x_44_);
v___x_52_ = lean_apply_3(v_h__2_46_, v_key_49_, v_value_50_, v_tail_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_58_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_57_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_key_61_; lean_object* v_value_62_; lean_object* v_tail_63_; lean_object* v___x_64_; 
lean_dec(v_h__1_57_);
v_key_61_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_key_61_);
v_value_62_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_value_62_);
v_tail_63_ = lean_ctor_get(v_x_56_, 2);
lean_inc(v_tail_63_);
lean_dec_ref(v_x_56_);
v___x_64_ = lean_apply_3(v_h__2_58_, v_key_61_, v_value_62_, v_tail_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(lean_object* v_x_65_, lean_object* v_h__1_66_){
_start:
{
lean_object* v_key_67_; lean_object* v_value_68_; lean_object* v_tail_69_; lean_object* v___x_70_; 
v_key_67_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_key_67_);
v_value_68_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_value_68_);
v_tail_69_ = lean_ctor_get(v_x_65_, 2);
lean_inc(v_tail_69_);
lean_dec(v_x_65_);
v___x_70_ = lean_apply_4(v_h__1_66_, v_key_67_, v_value_68_, v_tail_69_, lean_box(0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_inst_73_, lean_object* v_a_74_, lean_object* v_motive_75_, lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_h__1_78_){
_start:
{
lean_object* v_key_79_; lean_object* v_value_80_; lean_object* v_tail_81_; lean_object* v___x_82_; 
v_key_79_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_key_79_);
v_value_80_ = lean_ctor_get(v_x_76_, 1);
lean_inc(v_value_80_);
v_tail_81_ = lean_ctor_get(v_x_76_, 2);
lean_inc(v_tail_81_);
lean_dec(v_x_76_);
v___x_82_ = lean_apply_4(v_h__1_78_, v_key_79_, v_value_80_, v_tail_81_, lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___boxed(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_inst_85_, lean_object* v_a_86_, lean_object* v_motive_87_, lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_h__1_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(v_00_u03b1_83_, v_00_u03b2_84_, v_inst_85_, v_a_86_, v_motive_87_, v_x_88_, v_x_89_, v_h__1_90_);
lean_dec(v_a_86_);
lean_dec_ref(v_inst_85_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(lean_object* v_x_92_, lean_object* v_h__1_93_){
_start:
{
lean_object* v_key_94_; lean_object* v_value_95_; lean_object* v_tail_96_; lean_object* v___x_97_; 
v_key_94_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_key_94_);
v_value_95_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_value_95_);
v_tail_96_ = lean_ctor_get(v_x_92_, 2);
lean_inc(v_tail_96_);
lean_dec(v_x_92_);
v___x_97_ = lean_apply_4(v_h__1_93_, v_key_94_, v_value_95_, v_tail_96_, lean_box(0));
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_a_101_, lean_object* v_motive_102_, lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_h__1_105_){
_start:
{
lean_object* v_key_106_; lean_object* v_value_107_; lean_object* v_tail_108_; lean_object* v___x_109_; 
v_key_106_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_key_106_);
v_value_107_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_value_107_);
v_tail_108_ = lean_ctor_get(v_x_103_, 2);
lean_inc(v_tail_108_);
lean_dec(v_x_103_);
v___x_109_ = lean_apply_4(v_h__1_105_, v_key_106_, v_value_107_, v_tail_108_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___boxed(lean_object* v_00_u03b1_110_, lean_object* v_00_u03b2_111_, lean_object* v_inst_112_, lean_object* v_a_113_, lean_object* v_motive_114_, lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_h__1_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(v_00_u03b1_110_, v_00_u03b2_111_, v_inst_112_, v_a_113_, v_motive_114_, v_x_115_, v_x_116_, v_h__1_117_);
lean_dec(v_a_113_);
lean_dec_ref(v_inst_112_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_h__2_121_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_1(v_h__1_120_, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_120_);
v_val_124_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_val_124_);
lean_dec_ref(v_x_119_);
v___x_125_ = lean_apply_1(v_h__2_121_, v_val_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_a_128_, lean_object* v_motive_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__2_132_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_1(v_h__1_131_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_131_);
v_val_135_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v_x_130_);
v___x_136_ = lean_apply_1(v_h__2_132_, v_val_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v_a_139_, lean_object* v_motive_140_, lean_object* v_x_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(v_00_u03b1_137_, v_00_u03b2_138_, v_a_139_, v_motive_140_, v_x_141_, v_h__1_142_, v_h__2_143_);
lean_dec(v_a_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_h__2_147_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_h__1_146_, v___x_148_);
return v___x_149_;
}
else
{
lean_object* v_val_150_; lean_object* v___x_151_; 
lean_dec(v_h__1_146_);
v_val_150_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_150_);
lean_dec_ref(v_x_145_);
v___x_151_ = lean_apply_1(v_h__2_147_, v_val_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_152_, lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__2_156_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__1_155_, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_160_; 
lean_dec(v_h__1_155_);
v_val_159_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_val_159_);
lean_dec_ref(v_x_154_);
v___x_160_ = lean_apply_1(v_h__2_156_, v_val_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_h__2_163_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_1(v_h__1_162_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_162_);
v_val_166_ = lean_ctor_get(v_x_161_, 0);
lean_inc(v_val_166_);
lean_dec_ref(v_x_161_);
v___x_167_ = lean_apply_1(v_h__2_163_, v_val_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_k_170_, lean_object* v_motive_171_, lean_object* v_x_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_h__2_174_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_1(v_h__1_173_, v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_178_; 
lean_dec(v_h__1_173_);
v_val_177_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v_x_172_);
v___x_178_ = lean_apply_1(v_h__2_174_, v_val_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_k_181_, lean_object* v_motive_182_, lean_object* v_x_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_179_, v_00_u03b2_180_, v_k_181_, v_motive_182_, v_x_183_, v_h__1_184_, v_h__2_185_);
lean_dec(v_k_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
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
v_val_192_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_val_192_);
lean_dec_ref(v_x_187_);
v___x_193_ = lean_apply_1(v_h__2_189_, v_val_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter(lean_object* v_00_u03b2_194_, lean_object* v_motive_195_, lean_object* v_x_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__2_198_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_h__1_197_, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_202_; 
lean_dec(v_h__1_197_);
v_val_201_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_val_201_);
lean_dec_ref(v_x_196_);
v___x_202_ = lean_apply_1(v_h__2_198_, v_val_201_);
return v___x_202_;
}
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
