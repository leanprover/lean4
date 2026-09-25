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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushExcept_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushExcept_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b5_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushOption_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Lean_Order_pushOption_match__1_splitter(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter(lean_object* v_00_u03b5_58_, lean_object* v_00_u03b1_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_69_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__2_70_, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_70_);
v_val_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v_x_68_, 1);
v___x_74_ = lean_apply_1(v_h__1_69_, v_val_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_75_, lean_object* v_motive_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_78_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__2_79_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_79_);
v_val_82_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v_x_77_, 1);
v___x_83_ = lean_apply_1(v_h__1_78_, v_val_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
if (lean_obj_tag(v_x_84_) == 1)
{
lean_object* v_a_87_; lean_object* v_a_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_86_);
v_a_87_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_a_87_);
v_a_88_ = lean_ctor_get(v_x_84_, 1);
lean_inc(v_a_88_);
lean_dec_ref_known(v_x_84_, 2);
v___x_89_ = lean_apply_2(v_h__1_85_, v_a_87_, v_a_88_);
return v___x_89_;
}
else
{
lean_object* v___x_90_; 
lean_dec(v_h__1_85_);
v___x_90_ = lean_apply_2(v_h__2_86_, v_x_84_, lean_box(0));
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter(lean_object* v_00_u03b5_91_, lean_object* v_00_u03c3_92_, lean_object* v_00_u03b1_93_, lean_object* v_motive_94_, lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
if (lean_obj_tag(v_x_95_) == 1)
{
lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v___x_100_; 
lean_dec(v_h__2_97_);
v_a_98_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_a_98_);
v_a_99_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_a_99_);
lean_dec_ref_known(v_x_95_, 2);
v___x_100_ = lean_apply_2(v_h__1_96_, v_a_98_, v_a_99_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
lean_dec(v_h__1_96_);
v___x_101_ = lean_apply_2(v_h__2_97_, v_x_95_, lean_box(0));
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter___redArg(lean_object* v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_h__2_104_);
v_a_105_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_a_105_);
v_a_106_ = lean_ctor_get(v_x_102_, 1);
lean_inc(v_a_106_);
lean_dec_ref_known(v_x_102_, 2);
v___x_107_ = lean_apply_2(v_h__1_103_, v_a_105_, v_a_106_);
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v___x_110_; 
lean_dec(v_h__1_103_);
v_a_108_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_a_108_);
v_a_109_ = lean_ctor_get(v_x_102_, 1);
lean_inc(v_a_109_);
lean_dec_ref_known(v_x_102_, 2);
v___x_110_ = lean_apply_2(v_h__2_104_, v_a_108_, v_a_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter(lean_object* v_00_u03b5_111_, lean_object* v_00_u03c3_112_, lean_object* v_00_u03b1_113_, lean_object* v_motive_114_, lean_object* v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v_a_118_; lean_object* v_a_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_117_);
v_a_118_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_a_118_);
v_a_119_ = lean_ctor_get(v_x_115_, 1);
lean_inc(v_a_119_);
lean_dec_ref_known(v_x_115_, 2);
v___x_120_ = lean_apply_2(v_h__1_116_, v_a_118_, v_a_119_);
return v___x_120_;
}
else
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_123_; 
lean_dec(v_h__1_116_);
v_a_121_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_a_121_);
v_a_122_ = lean_ctor_get(v_x_115_, 1);
lean_inc(v_a_122_);
lean_dec_ref_known(v_x_115_, 2);
v___x_123_ = lean_apply_2(v_h__2_117_, v_a_121_, v_a_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object* v_____do__lift_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
if (lean_obj_tag(v_____do__lift_124_) == 1)
{
lean_object* v_val_127_; lean_object* v___x_128_; 
lean_dec(v_h__2_126_);
v_val_127_ = lean_ctor_get(v_____do__lift_124_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v_____do__lift_124_, 1);
v___x_128_ = lean_apply_1(v_h__1_125_, v_val_127_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
lean_dec(v_h__1_125_);
v___x_129_ = lean_apply_2(v_h__2_126_, v_____do__lift_124_, lean_box(0));
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter(lean_object* v_00_u03b1_130_, lean_object* v_motive_131_, lean_object* v_____do__lift_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (lean_obj_tag(v_____do__lift_132_) == 1)
{
lean_object* v_val_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_134_);
v_val_135_ = lean_ctor_get(v_____do__lift_132_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_____do__lift_132_, 1);
v___x_136_ = lean_apply_1(v_h__1_133_, v_val_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; 
lean_dec(v_h__1_133_);
v___x_137_ = lean_apply_2(v_h__2_134_, v_____do__lift_132_, lean_box(0));
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_a_141_; lean_object* v_a_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_139_);
v_a_141_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_141_);
v_a_142_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_a_142_);
lean_dec_ref_known(v_x_138_, 2);
v___x_143_ = lean_apply_2(v_h__2_140_, v_a_141_, v_a_142_);
return v___x_143_;
}
else
{
lean_object* v_a_144_; lean_object* v_a_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_140_);
v_a_144_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_144_);
v_a_145_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_a_145_);
lean_dec_ref_known(v_x_138_, 2);
v___x_146_ = lean_apply_2(v_h__1_139_, v_a_144_, v_a_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter(lean_object* v_00_u03b5_147_, lean_object* v_00_u03c3_148_, lean_object* v_00_u03b1_149_, lean_object* v_motive_150_, lean_object* v_x_151_, lean_object* v_h__1_152_, lean_object* v_h__2_153_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v_a_154_; lean_object* v_a_155_; lean_object* v___x_156_; 
lean_dec(v_h__1_152_);
v_a_154_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_a_154_);
v_a_155_ = lean_ctor_get(v_x_151_, 1);
lean_inc(v_a_155_);
lean_dec_ref_known(v_x_151_, 2);
v___x_156_ = lean_apply_2(v_h__2_153_, v_a_154_, v_a_155_);
return v___x_156_;
}
else
{
lean_object* v_a_157_; lean_object* v_a_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_153_);
v_a_157_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_a_157_);
v_a_158_ = lean_ctor_get(v_x_151_, 1);
lean_inc(v_a_158_);
lean_dec_ref_known(v_x_151_, 2);
v___x_159_ = lean_apply_2(v_h__1_152_, v_a_157_, v_a_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter___redArg(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_164_; 
lean_dec(v_h__1_162_);
v___x_164_ = lean_apply_1(v_h__2_163_, v_x_161_);
return v___x_164_;
}
else
{
lean_object* v_val_165_; lean_object* v___x_166_; 
lean_dec(v_h__2_163_);
v_val_165_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v_x_160_, 1);
v___x_166_ = lean_apply_2(v_h__1_162_, v_val_165_, v_x_161_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter(lean_object* v_00_u03b1_167_, lean_object* v_motive_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v___x_173_; 
lean_dec(v_h__1_171_);
v___x_173_ = lean_apply_1(v_h__2_172_, v_x_170_);
return v___x_173_;
}
else
{
lean_object* v_val_174_; lean_object* v___x_175_; 
lean_dec(v_h__2_172_);
v_val_174_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v_x_169_, 1);
v___x_175_ = lean_apply_2(v_h__1_171_, v_val_174_, v_x_170_);
return v___x_175_;
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
