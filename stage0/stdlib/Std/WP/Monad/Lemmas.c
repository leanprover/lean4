// Lean compiler output
// Module: Std.WP.Monad.Lemmas
// Imports: public import Std.WP.Monad.Instances
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_Except_wpInst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_Except_wpInst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__2_3_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b5_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_12_);
v_a_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v_x_11_, 1);
v___x_15_ = lean_apply_1(v_h__2_13_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_13_);
v_a_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v_x_11_, 1);
v___x_17_ = lean_apply_1(v_h__1_12_, v_a_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushOption_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_19_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__2_20_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_val_23_; lean_object* v___x_24_; 
lean_dec(v_h__2_20_);
v_val_23_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_val_23_);
lean_dec_ref_known(v_x_18_, 1);
v___x_24_ = lean_apply_1(v_h__1_19_, v_val_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EPost_Cons_pushOption_match__1_splitter(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_28_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_apply_1(v_h__2_29_, v___x_30_);
return v___x_31_;
}
else
{
lean_object* v_val_32_; lean_object* v___x_33_; 
lean_dec(v_h__2_29_);
v_val_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_val_32_);
lean_dec_ref_known(v_x_27_, 1);
v___x_33_ = lean_apply_1(v_h__1_28_, v_val_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter___redArg(lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_38_; 
lean_dec(v_h__1_35_);
v_a_37_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_a_37_);
lean_dec_ref_known(v_x_34_, 1);
v___x_38_ = lean_apply_1(v_h__2_36_, v_a_37_);
return v___x_38_;
}
else
{
lean_object* v_a_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_36_);
v_a_39_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_a_39_);
lean_dec_ref_known(v_x_34_, 1);
v___x_40_ = lean_apply_1(v_h__1_35_, v_a_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter(lean_object* v_00_u03b5_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_45_);
v_a_47_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v_x_44_, 1);
v___x_48_ = lean_apply_1(v_h__2_46_, v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_46_);
v_a_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_a_49_);
lean_dec_ref_known(v_x_44_, 1);
v___x_50_ = lean_apply_1(v_h__1_45_, v_a_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_Except_wpInst_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_52_);
v_a_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v_x_51_, 1);
v___x_55_ = lean_apply_1(v_h__2_53_, v_a_54_);
return v___x_55_;
}
else
{
lean_object* v_a_56_; lean_object* v___x_57_; 
lean_dec(v_h__2_53_);
v_a_56_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_56_);
lean_dec_ref_known(v_x_51_, 1);
v___x_57_ = lean_apply_1(v_h__1_52_, v_a_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_Except_wpInst_match__1_splitter(lean_object* v_00_u03b5_58_, lean_object* v_00_u03b1_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_62_);
v_a_64_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_a_64_);
lean_dec_ref_known(v_x_61_, 1);
v___x_65_ = lean_apply_1(v_h__2_63_, v_a_64_);
return v___x_65_;
}
else
{
lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_63_);
v_a_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v_x_61_, 1);
v___x_67_ = lean_apply_1(v_h__1_62_, v_a_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_69_);
v_a_71_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v_x_68_, 1);
v___x_72_ = lean_apply_1(v_h__2_70_, v_a_71_);
return v___x_72_;
}
else
{
lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_70_);
v_a_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v_x_68_, 1);
v___x_74_ = lean_apply_1(v_h__1_69_, v_a_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter(lean_object* v_00_u03b5_75_, lean_object* v_00_u03b1_76_, lean_object* v_motive_77_, lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_82_; 
lean_dec(v_h__1_79_);
v_a_81_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v_x_78_, 1);
v___x_82_ = lean_apply_1(v_h__2_80_, v_a_81_);
return v___x_82_;
}
else
{
lean_object* v_a_83_; lean_object* v___x_84_; 
lean_dec(v_h__2_80_);
v_a_83_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_a_83_);
lean_dec_ref_known(v_x_78_, 1);
v___x_84_ = lean_apply_1(v_h__1_79_, v_a_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__1_86_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__2_87_, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v_val_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_87_);
v_val_90_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_val_90_);
lean_dec_ref_known(v_x_85_, 1);
v___x_91_ = lean_apply_1(v_h__1_86_, v_val_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_92_, lean_object* v_motive_93_, lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_h__1_95_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_apply_1(v_h__2_96_, v___x_97_);
return v___x_98_;
}
else
{
lean_object* v_val_99_; lean_object* v___x_100_; 
lean_dec(v_h__2_96_);
v_val_99_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v_x_94_, 1);
v___x_100_ = lean_apply_1(v_h__1_95_, v_val_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
if (lean_obj_tag(v_x_101_) == 1)
{
lean_object* v_a_104_; lean_object* v_a_105_; lean_object* v___x_106_; 
lean_dec(v_h__2_103_);
v_a_104_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_a_104_);
v_a_105_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_a_105_);
lean_dec_ref_known(v_x_101_, 2);
v___x_106_ = lean_apply_2(v_h__1_102_, v_a_104_, v_a_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
lean_dec(v_h__1_102_);
v___x_107_ = lean_apply_2(v_h__2_103_, v_x_101_, lean_box(0));
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter(lean_object* v_00_u03b5_108_, lean_object* v_00_u03c3_109_, lean_object* v_00_u03b1_110_, lean_object* v_motive_111_, lean_object* v_x_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
if (lean_obj_tag(v_x_112_) == 1)
{
lean_object* v_a_115_; lean_object* v_a_116_; lean_object* v___x_117_; 
lean_dec(v_h__2_114_);
v_a_115_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_a_115_);
v_a_116_ = lean_ctor_get(v_x_112_, 1);
lean_inc(v_a_116_);
lean_dec_ref_known(v_x_112_, 2);
v___x_117_ = lean_apply_2(v_h__1_113_, v_a_115_, v_a_116_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; 
lean_dec(v_h__1_113_);
v___x_118_ = lean_apply_2(v_h__2_114_, v_x_112_, lean_box(0));
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter___redArg(lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v_a_122_; lean_object* v_a_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_121_);
v_a_122_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_a_122_);
v_a_123_ = lean_ctor_get(v_x_119_, 1);
lean_inc(v_a_123_);
lean_dec_ref_known(v_x_119_, 2);
v___x_124_ = lean_apply_2(v_h__1_120_, v_a_122_, v_a_123_);
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v___x_127_; 
lean_dec(v_h__1_120_);
v_a_125_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_a_125_);
v_a_126_ = lean_ctor_get(v_x_119_, 1);
lean_inc(v_a_126_);
lean_dec_ref_known(v_x_119_, 2);
v___x_127_ = lean_apply_2(v_h__2_121_, v_a_125_, v_a_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter(lean_object* v_00_u03b5_128_, lean_object* v_00_u03c3_129_, lean_object* v_00_u03b1_130_, lean_object* v_motive_131_, lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v_a_135_; lean_object* v_a_136_; lean_object* v___x_137_; 
lean_dec(v_h__2_134_);
v_a_135_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_a_135_);
v_a_136_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_a_136_);
lean_dec_ref_known(v_x_132_, 2);
v___x_137_ = lean_apply_2(v_h__1_133_, v_a_135_, v_a_136_);
return v___x_137_;
}
else
{
lean_object* v_a_138_; lean_object* v_a_139_; lean_object* v___x_140_; 
lean_dec(v_h__1_133_);
v_a_138_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_a_138_);
v_a_139_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_a_139_);
lean_dec_ref_known(v_x_132_, 2);
v___x_140_ = lean_apply_2(v_h__2_134_, v_a_138_, v_a_139_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object* v_____do__lift_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_){
_start:
{
if (lean_obj_tag(v_____do__lift_141_) == 1)
{
lean_object* v_val_144_; lean_object* v___x_145_; 
lean_dec(v_h__2_143_);
v_val_144_ = lean_ctor_get(v_____do__lift_141_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v_____do__lift_141_, 1);
v___x_145_ = lean_apply_1(v_h__1_142_, v_val_144_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; 
lean_dec(v_h__1_142_);
v___x_146_ = lean_apply_2(v_h__2_143_, v_____do__lift_141_, lean_box(0));
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter(lean_object* v_00_u03b1_147_, lean_object* v_motive_148_, lean_object* v_____do__lift_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
if (lean_obj_tag(v_____do__lift_149_) == 1)
{
lean_object* v_val_152_; lean_object* v___x_153_; 
lean_dec(v_h__2_151_);
v_val_152_ = lean_ctor_get(v_____do__lift_149_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v_____do__lift_149_, 1);
v___x_153_ = lean_apply_1(v_h__1_150_, v_val_152_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
lean_dec(v_h__1_150_);
v___x_154_ = lean_apply_2(v_h__2_151_, v_____do__lift_149_, lean_box(0));
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v_a_158_; lean_object* v_a_159_; lean_object* v___x_160_; 
lean_dec(v_h__1_156_);
v_a_158_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_158_);
v_a_159_ = lean_ctor_get(v_x_155_, 1);
lean_inc(v_a_159_);
lean_dec_ref_known(v_x_155_, 2);
v___x_160_ = lean_apply_2(v_h__2_157_, v_a_158_, v_a_159_);
return v___x_160_;
}
else
{
lean_object* v_a_161_; lean_object* v_a_162_; lean_object* v___x_163_; 
lean_dec(v_h__2_157_);
v_a_161_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_161_);
v_a_162_ = lean_ctor_get(v_x_155_, 1);
lean_inc(v_a_162_);
lean_dec_ref_known(v_x_155_, 2);
v___x_163_ = lean_apply_2(v_h__1_156_, v_a_161_, v_a_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter(lean_object* v_00_u03b5_164_, lean_object* v_00_u03c3_165_, lean_object* v_00_u03b1_166_, lean_object* v_motive_167_, lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_a_171_; lean_object* v_a_172_; lean_object* v___x_173_; 
lean_dec(v_h__1_169_);
v_a_171_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_a_171_);
v_a_172_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_a_172_);
lean_dec_ref_known(v_x_168_, 2);
v___x_173_ = lean_apply_2(v_h__2_170_, v_a_171_, v_a_172_);
return v___x_173_;
}
else
{
lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___x_176_; 
lean_dec(v_h__2_170_);
v_a_174_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_a_174_);
v_a_175_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_a_175_);
lean_dec_ref_known(v_x_168_, 2);
v___x_176_ = lean_apply_2(v_h__1_169_, v_a_174_, v_a_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter___redArg(lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_181_; 
lean_dec(v_h__1_179_);
v___x_181_ = lean_apply_1(v_h__2_180_, v_x_178_);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_180_);
v_val_182_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v_x_177_, 1);
v___x_183_ = lean_apply_2(v_h__1_179_, v_val_182_, v_x_178_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter(lean_object* v_00_u03b1_184_, lean_object* v_motive_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
lean_object* v___x_190_; 
lean_dec(v_h__1_188_);
v___x_190_ = lean_apply_1(v_h__2_189_, v_x_187_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_192_; 
lean_dec(v_h__2_189_);
v_val_191_ = lean_ctor_get(v_x_186_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v_x_186_, 1);
v___x_192_ = lean_apply_2(v_h__1_188_, v_val_191_, v_x_187_);
return v___x_192_;
}
}
}
lean_object* runtime_initialize_Std_WP_Monad_Instances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_WP_Monad_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_WP_Monad_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_WP_Monad_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_WP_Monad_Instances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_WP_Monad_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_WP_Monad_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Monad_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_WP_Monad_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_WP_Monad_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
