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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_2_, 3);
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
lean_dec_ref_known(v_x_15_, 3);
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
lean_dec_ref_known(v_x_23_, 3);
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
lean_dec_ref_known(v_x_35_, 3);
v___x_43_ = lean_apply_3(v_h__2_37_, v_key_40_, v_value_41_, v_tail_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
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
lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v_fst_51_; lean_object* v_snd_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_45_);
v_head_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_head_49_);
v_tail_50_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_tail_50_);
lean_dec_ref_known(v_x_44_, 2);
v_fst_51_ = lean_ctor_get(v_head_49_, 0);
lean_inc(v_fst_51_);
v_snd_52_ = lean_ctor_get(v_head_49_, 1);
lean_inc(v_snd_52_);
lean_dec(v_head_49_);
v___x_53_ = lean_apply_3(v_h__2_46_, v_fst_51_, v_snd_52_, v_tail_50_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_motive_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v_h__2_59_);
v___x_60_ = lean_box(0);
v___x_61_ = lean_apply_1(v_h__1_58_, v___x_60_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_58_);
v_head_62_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_head_62_);
v_tail_63_ = lean_ctor_get(v_x_57_, 1);
lean_inc(v_tail_63_);
lean_dec_ref_known(v_x_57_, 2);
v_fst_64_ = lean_ctor_get(v_head_62_, 0);
lean_inc(v_fst_64_);
v_snd_65_ = lean_ctor_get(v_head_62_, 1);
lean_inc(v_snd_65_);
lean_dec(v_head_62_);
v___x_66_ = lean_apply_3(v_h__2_59_, v_fst_64_, v_snd_65_, v_tail_63_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_69_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_apply_1(v_h__1_68_, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v_key_72_; lean_object* v_value_73_; lean_object* v_tail_74_; lean_object* v___x_75_; 
lean_dec(v_h__1_68_);
v_key_72_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_key_72_);
v_value_73_ = lean_ctor_get(v_x_67_, 1);
lean_inc(v_value_73_);
v_tail_74_ = lean_ctor_get(v_x_67_, 2);
lean_inc(v_tail_74_);
lean_dec_ref_known(v_x_67_, 3);
v___x_75_ = lean_apply_3(v_h__2_69_, v_key_72_, v_value_73_, v_tail_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_motive_78_, lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_81_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__1_80_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_key_84_; lean_object* v_value_85_; lean_object* v_tail_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_80_);
v_key_84_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_key_84_);
v_value_85_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_value_85_);
v_tail_86_ = lean_ctor_get(v_x_79_, 2);
lean_inc(v_tail_86_);
lean_dec_ref_known(v_x_79_, 3);
v___x_87_ = lean_apply_3(v_h__2_81_, v_key_84_, v_value_85_, v_tail_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_90_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__1_89_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_head_93_; lean_object* v_tail_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_97_; 
lean_dec(v_h__1_89_);
v_head_93_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_head_93_);
v_tail_94_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_tail_94_);
lean_dec_ref_known(v_x_88_, 2);
v_fst_95_ = lean_ctor_get(v_head_93_, 0);
lean_inc(v_fst_95_);
v_snd_96_ = lean_ctor_get(v_head_93_, 1);
lean_inc(v_snd_96_);
lean_dec(v_head_93_);
v___x_97_ = lean_apply_3(v_h__2_90_, v_fst_95_, v_snd_96_, v_tail_94_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_motive_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_h__2_103_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_apply_1(v_h__1_102_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v_head_106_; lean_object* v_tail_107_; lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v___x_110_; 
lean_dec(v_h__1_102_);
v_head_106_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_head_106_);
v_tail_107_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_tail_107_);
lean_dec_ref_known(v_x_101_, 2);
v_fst_108_ = lean_ctor_get(v_head_106_, 0);
lean_inc(v_fst_108_);
v_snd_109_ = lean_ctor_get(v_head_106_, 1);
lean_inc(v_snd_109_);
lean_dec(v_head_106_);
v___x_110_ = lean_apply_3(v_h__2_103_, v_fst_108_, v_snd_109_, v_tail_107_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___redArg(lean_object* v_x_111_, lean_object* v_h__1_112_){
_start:
{
lean_object* v_key_113_; lean_object* v_value_114_; lean_object* v_tail_115_; lean_object* v___x_116_; 
v_key_113_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_key_113_);
v_value_114_ = lean_ctor_get(v_x_111_, 1);
lean_inc(v_value_114_);
v_tail_115_ = lean_ctor_get(v_x_111_, 2);
lean_inc(v_tail_115_);
lean_dec(v_x_111_);
v___x_116_ = lean_apply_4(v_h__1_112_, v_key_113_, v_value_114_, v_tail_115_, lean_box(0));
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_inst_119_, lean_object* v_a_120_, lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_h__1_124_){
_start:
{
lean_object* v_key_125_; lean_object* v_value_126_; lean_object* v_tail_127_; lean_object* v___x_128_; 
v_key_125_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_key_125_);
v_value_126_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_value_126_);
v_tail_127_ = lean_ctor_get(v_x_122_, 2);
lean_inc(v_tail_127_);
lean_dec(v_x_122_);
v___x_128_ = lean_apply_4(v_h__1_124_, v_key_125_, v_value_126_, v_tail_127_, lean_box(0));
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter___boxed(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_inst_131_, lean_object* v_a_132_, lean_object* v_motive_133_, lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_h__1_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_getCast_match__1_splitter(v_00_u03b1_129_, v_00_u03b2_130_, v_inst_131_, v_a_132_, v_motive_133_, v_x_134_, v_x_135_, v_h__1_136_);
lean_dec(v_a_132_);
lean_dec_ref(v_inst_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___redArg(lean_object* v_x_138_, lean_object* v_h__1_139_){
_start:
{
lean_object* v_key_140_; lean_object* v_value_141_; lean_object* v_tail_142_; lean_object* v___x_143_; 
v_key_140_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_key_140_);
v_value_141_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_value_141_);
v_tail_142_ = lean_ctor_get(v_x_138_, 2);
lean_inc(v_tail_142_);
lean_dec(v_x_138_);
v___x_143_ = lean_apply_4(v_h__1_139_, v_key_140_, v_value_141_, v_tail_142_, lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_inst_146_, lean_object* v_a_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_){
_start:
{
lean_object* v_key_152_; lean_object* v_value_153_; lean_object* v_tail_154_; lean_object* v___x_155_; 
v_key_152_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_key_152_);
v_value_153_ = lean_ctor_get(v_x_149_, 1);
lean_inc(v_value_153_);
v_tail_154_ = lean_ctor_get(v_x_149_, 2);
lean_inc(v_tail_154_);
lean_dec(v_x_149_);
v___x_155_ = lean_apply_4(v_h__1_151_, v_key_152_, v_value_153_, v_tail_154_, lean_box(0));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter___boxed(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_inst_158_, lean_object* v_a_159_, lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_h__1_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_get_match__1_splitter(v_00_u03b1_156_, v_00_u03b2_157_, v_inst_158_, v_a_159_, v_motive_160_, v_x_161_, v_x_162_, v_h__1_163_);
lean_dec(v_a_159_);
lean_dec_ref(v_inst_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___redArg(lean_object* v_x_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_h__2_167_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_apply_1(v_h__1_166_, v___x_168_);
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_166_);
v_val_170_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_val_170_);
lean_dec_ref_known(v_x_165_, 1);
v___x_171_ = lean_apply_1(v_h__2_167_, v_val_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(lean_object* v_00_u03b1_172_, lean_object* v_00_u03b2_173_, lean_object* v_a_174_, lean_object* v_motive_175_, lean_object* v_x_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__2_178_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_apply_1(v_h__1_177_, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; 
lean_dec(v_h__1_177_);
v_val_181_ = lean_ctor_get(v_x_176_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v_x_176_, 1);
v___x_182_ = lean_apply_1(v_h__2_178_, v_val_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_a_185_, lean_object* v_motive_186_, lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_alter_match__1_splitter(v_00_u03b1_183_, v_00_u03b2_184_, v_a_185_, v_motive_186_, v_x_187_, v_h__1_188_, v_h__2_189_);
lean_dec(v_a_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_h__2_193_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_apply_1(v_h__1_192_, v___x_194_);
return v___x_195_;
}
else
{
lean_object* v_val_196_; lean_object* v___x_197_; 
lean_dec(v_h__1_192_);
v_val_196_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v_x_191_, 1);
v___x_197_ = lean_apply_1(v_h__2_193_, v_val_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_198_, lean_object* v_motive_199_, lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__2_202_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_h__1_201_, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; 
lean_dec(v_h__1_201_);
v_val_205_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v_x_200_, 1);
v___x_206_ = lean_apply_1(v_h__2_202_, v_val_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_h__2_209_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_1(v_h__1_208_, v___x_210_);
return v___x_211_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_213_; 
lean_dec(v_h__1_208_);
v_val_212_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v_x_207_, 1);
v___x_213_ = lean_apply_1(v_h__2_209_, v_val_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_k_216_, lean_object* v_motive_217_, lean_object* v_x_218_, lean_object* v_h__1_219_, lean_object* v_h__2_220_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_h__2_220_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_apply_1(v_h__1_219_, v___x_221_);
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v___x_224_; 
lean_dec(v_h__1_219_);
v_val_223_ = lean_ctor_get(v_x_218_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v_x_218_, 1);
v___x_224_ = lean_apply_1(v_h__2_220_, v_val_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_k_227_, lean_object* v_motive_228_, lean_object* v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_225_, v_00_u03b2_226_, v_k_227_, v_motive_228_, v_x_229_, v_h__1_230_, v_h__2_231_);
lean_dec(v_k_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter___redArg(lean_object* v_x_233_, lean_object* v_h__1_234_, lean_object* v_h__2_235_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_h__2_235_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_h__1_234_, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_239_; 
lean_dec(v_h__1_234_);
v_val_238_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v_x_233_, 1);
v___x_239_ = lean_apply_1(v_h__2_235_, v_val_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Lemmas_0__Std_DHashMap_Internal_AssocList_Const_alter_match__1_splitter(lean_object* v_00_u03b2_240_, lean_object* v_motive_241_, lean_object* v_x_242_, lean_object* v_h__1_243_, lean_object* v_h__2_244_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v_h__2_244_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_apply_1(v_h__1_243_, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v_val_247_; lean_object* v___x_248_; 
lean_dec(v_h__1_243_);
v_val_247_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v_x_242_, 1);
v___x_248_ = lean_apply_1(v_h__2_244_, v_val_247_);
return v___x_248_;
}
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
