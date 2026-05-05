// Lean compiler output
// Module: Std.Internal.Do.WP.Lemmas
// Imports: public import Std.Internal.Do.WP.Basic
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Except_toBool_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Except_toBool_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_bindCont_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_run__tryCatch_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_run__tryCatch_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_tryCatch_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__OptionT_orElse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_adaptExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_orElse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_orElse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Except_toBool_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref(v_x_1_);
v___x_5_ = lean_apply_1(v_h__2_3_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Except_toBool_match__1_splitter(lean_object* v_00_u03b5_8_, lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_12_);
v_a_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v_x_11_);
v___x_15_ = lean_apply_1(v_h__2_13_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_13_);
v_a_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_16_);
lean_dec_ref(v_x_11_);
v___x_17_ = lean_apply_1(v_h__1_12_, v_a_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_19_);
v_a_21_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_21_);
lean_dec_ref(v_x_18_);
v___x_22_ = lean_apply_1(v_h__2_20_, v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_h__2_20_);
v_a_23_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref(v_x_18_);
v___x_24_ = lean_apply_1(v_h__1_19_, v_a_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter(lean_object* v_00_u03b5_25_, lean_object* v_00_u03b1_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_29_);
v_a_31_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v_x_28_);
v___x_32_ = lean_apply_1(v_h__2_30_, v_a_31_);
return v___x_32_;
}
else
{
lean_object* v_a_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_30_);
v_a_33_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_33_);
lean_dec_ref(v_x_28_);
v___x_34_ = lean_apply_1(v_h__1_29_, v_a_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_36_);
v_a_38_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_a_38_);
lean_dec_ref(v_x_35_);
v___x_39_ = lean_apply_1(v_h__2_37_, v_a_38_);
return v___x_39_;
}
else
{
lean_object* v_a_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_37_);
v_a_40_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_a_40_);
lean_dec_ref(v_x_35_);
v___x_41_ = lean_apply_1(v_h__1_36_, v_a_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_42_, lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_46_);
v_a_48_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v_x_45_);
v___x_49_ = lean_apply_1(v_h__2_47_, v_a_48_);
return v___x_49_;
}
else
{
lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_47_);
v_a_50_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v_x_45_);
v___x_51_ = lean_apply_1(v_h__1_46_, v_a_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_run__tryCatch_match__1_splitter___redArg(lean_object* v_r_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_r_52_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
lean_dec(v_h__1_53_);
v_a_55_ = lean_ctor_get(v_r_52_, 0);
lean_inc(v_a_55_);
lean_dec_ref(v_r_52_);
v___x_56_ = lean_apply_1(v_h__2_54_, v_a_55_);
return v___x_56_;
}
else
{
lean_object* v_a_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_54_);
v_a_57_ = lean_ctor_get(v_r_52_, 0);
lean_inc(v_a_57_);
lean_dec_ref(v_r_52_);
v___x_58_ = lean_apply_1(v_h__1_53_, v_a_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_run__tryCatch_match__1_splitter(lean_object* v_00_u03b5_59_, lean_object* v_00_u03b1_60_, lean_object* v_motive_61_, lean_object* v_r_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
if (lean_obj_tag(v_r_62_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_63_);
v_a_65_ = lean_ctor_get(v_r_62_, 0);
lean_inc(v_a_65_);
lean_dec_ref(v_r_62_);
v___x_66_ = lean_apply_1(v_h__2_64_, v_a_65_);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v___x_68_; 
lean_dec(v_h__2_64_);
v_a_67_ = lean_ctor_get(v_r_62_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v_r_62_);
v___x_68_ = lean_apply_1(v_h__1_63_, v_a_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_70_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__2_71_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_75_; 
lean_dec(v_h__2_71_);
v_val_74_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_val_74_);
lean_dec_ref(v_x_69_);
v___x_75_ = lean_apply_1(v_h__1_70_, v_val_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_76_, lean_object* v_motive_77_, lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_h__1_79_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_h__2_80_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_val_83_; lean_object* v___x_84_; 
lean_dec(v_h__2_80_);
v_val_83_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_val_83_);
lean_dec_ref(v_x_78_);
v___x_84_ = lean_apply_1(v_h__1_79_, v_val_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_x_85_) == 1)
{
lean_object* v_a_88_; lean_object* v_a_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_87_);
v_a_88_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_a_88_);
v_a_89_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_a_89_);
lean_dec_ref(v_x_85_);
v___x_90_ = lean_apply_2(v_h__1_86_, v_a_88_, v_a_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_dec(v_h__1_86_);
v___x_91_ = lean_apply_2(v_h__2_87_, v_x_85_, lean_box(0));
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_tryCatch_match__1_splitter(lean_object* v_00_u03b5_92_, lean_object* v_00_u03c3_93_, lean_object* v_00_u03b1_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
if (lean_obj_tag(v_x_96_) == 1)
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_98_);
v_a_99_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_a_99_);
v_a_100_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_a_100_);
lean_dec_ref(v_x_96_);
v___x_101_ = lean_apply_2(v_h__1_97_, v_a_99_, v_a_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
lean_dec(v_h__1_97_);
v___x_102_ = lean_apply_2(v_h__2_98_, v_x_96_, lean_box(0));
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter___redArg(lean_object* v_x_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_){
_start:
{
if (lean_obj_tag(v_x_103_) == 0)
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_105_);
v_a_106_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_a_106_);
v_a_107_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_a_107_);
lean_dec_ref(v_x_103_);
v___x_108_ = lean_apply_2(v_h__1_104_, v_a_106_, v_a_107_);
return v___x_108_;
}
else
{
lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v___x_111_; 
lean_dec(v_h__1_104_);
v_a_109_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_a_109_);
v_a_110_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_a_110_);
lean_dec_ref(v_x_103_);
v___x_111_ = lean_apply_2(v_h__2_105_, v_a_109_, v_a_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter(lean_object* v_00_u03b5_112_, lean_object* v_00_u03c3_113_, lean_object* v_00_u03b1_114_, lean_object* v_motive_115_, lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v_a_119_; lean_object* v_a_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_118_);
v_a_119_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_a_119_);
v_a_120_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_a_120_);
lean_dec_ref(v_x_116_);
v___x_121_ = lean_apply_2(v_h__1_117_, v_a_119_, v_a_120_);
return v___x_121_;
}
else
{
lean_object* v_a_122_; lean_object* v_a_123_; lean_object* v___x_124_; 
lean_dec(v_h__1_117_);
v_a_122_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_a_122_);
v_a_123_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_a_123_);
lean_dec_ref(v_x_116_);
v___x_124_ = lean_apply_2(v_h__2_118_, v_a_122_, v_a_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object* v_____do__lift_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_){
_start:
{
if (lean_obj_tag(v_____do__lift_125_) == 1)
{
lean_object* v_val_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_127_);
v_val_128_ = lean_ctor_get(v_____do__lift_125_, 0);
lean_inc(v_val_128_);
lean_dec_ref(v_____do__lift_125_);
v___x_129_ = lean_apply_1(v_h__1_126_, v_val_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
lean_dec(v_h__1_126_);
v___x_130_ = lean_apply_2(v_h__2_127_, v_____do__lift_125_, lean_box(0));
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__OptionT_orElse_match__1_splitter(lean_object* v_00_u03b1_131_, lean_object* v_motive_132_, lean_object* v_____do__lift_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (lean_obj_tag(v_____do__lift_133_) == 1)
{
lean_object* v_val_136_; lean_object* v___x_137_; 
lean_dec(v_h__2_135_);
v_val_136_ = lean_ctor_get(v_____do__lift_133_, 0);
lean_inc(v_val_136_);
lean_dec_ref(v_____do__lift_133_);
v___x_137_ = lean_apply_1(v_h__1_134_, v_val_136_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; 
lean_dec(v_h__1_134_);
v___x_138_ = lean_apply_2(v_h__2_135_, v_____do__lift_133_, lean_box(0));
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v_a_142_; lean_object* v_a_143_; lean_object* v___x_144_; 
lean_dec(v_h__1_140_);
v_a_142_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_a_142_);
v_a_143_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_a_143_);
lean_dec_ref(v_x_139_);
v___x_144_ = lean_apply_2(v_h__2_141_, v_a_142_, v_a_143_);
return v___x_144_;
}
else
{
lean_object* v_a_145_; lean_object* v_a_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_141_);
v_a_145_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_a_145_);
v_a_146_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_a_146_);
lean_dec_ref(v_x_139_);
v___x_147_ = lean_apply_2(v_h__1_140_, v_a_145_, v_a_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_adaptExcept_match__1_splitter(lean_object* v_00_u03b5_148_, lean_object* v_00_u03c3_149_, lean_object* v_00_u03b1_150_, lean_object* v_motive_151_, lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v_a_155_; lean_object* v_a_156_; lean_object* v___x_157_; 
lean_dec(v_h__1_153_);
v_a_155_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_a_155_);
v_a_156_ = lean_ctor_get(v_x_152_, 1);
lean_inc(v_a_156_);
lean_dec_ref(v_x_152_);
v___x_157_ = lean_apply_2(v_h__2_154_, v_a_155_, v_a_156_);
return v___x_157_;
}
else
{
lean_object* v_a_158_; lean_object* v_a_159_; lean_object* v___x_160_; 
lean_dec(v_h__2_154_);
v_a_158_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_a_158_);
v_a_159_ = lean_ctor_get(v_x_152_, 1);
lean_inc(v_a_159_);
lean_dec_ref(v_x_152_);
v___x_160_ = lean_apply_2(v_h__1_153_, v_a_158_, v_a_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_orElse_match__1_splitter___redArg(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_object* v___x_165_; 
lean_dec(v_h__1_163_);
v___x_165_ = lean_apply_1(v_h__2_164_, v_x_162_);
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_164_);
v_val_166_ = lean_ctor_get(v_x_161_, 0);
lean_inc(v_val_166_);
lean_dec_ref(v_x_161_);
v___x_167_ = lean_apply_2(v_h__1_163_, v_val_166_, v_x_162_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Lemmas_0__Option_orElse_match__1_splitter(lean_object* v_00_u03b1_168_, lean_object* v_motive_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_h__1_172_, lean_object* v_h__2_173_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_174_; 
lean_dec(v_h__1_172_);
v___x_174_ = lean_apply_1(v_h__2_173_, v_x_171_);
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_176_; 
lean_dec(v_h__2_173_);
v_val_175_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_val_175_);
lean_dec_ref(v_x_170_);
v___x_176_ = lean_apply_2(v_h__1_172_, v_val_175_, v_x_171_);
return v___x_176_;
}
}
}
lean_object* runtime_initialize_Std_Internal_Do_WP_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_WP_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_WP_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_WP_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_WP_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_WP_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_WP_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_WP_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
