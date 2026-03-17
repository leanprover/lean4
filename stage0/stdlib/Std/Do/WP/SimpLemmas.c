// Lean compiler output
// Module: Std.Do.WP.SimpLemmas
// Imports: public import Std.Do.WP.Monad
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
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b5_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(v_x_11_, v_h__1_12_, v_h__2_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_h__1_16_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_apply_1(v_h__2_17_, v___x_18_);
return v___x_19_;
}
else
{
lean_object* v_val_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_17_);
v_val_20_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_val_20_);
lean_dec_ref(v_x_15_);
v___x_21_ = lean_apply_1(v_h__1_16_, v_val_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_22_, lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(v_x_24_, v_h__1_25_, v_h__2_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter___redArg(lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__2_30_);
v_a_31_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v_x_28_);
v___x_32_ = lean_apply_1(v_h__1_29_, v_a_31_);
return v___x_32_;
}
else
{
lean_object* v_a_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_29_);
v_a_33_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_33_);
lean_dec_ref(v_x_28_);
v___x_34_ = lean_apply_1(v_h__2_30_, v_a_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter(lean_object* v_00_u03b5_35_, lean_object* v_00_u03b1_36_, lean_object* v_motive_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter___redArg(v_x_38_, v_h__1_39_, v_h__2_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter___redArg(lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_a_45_; lean_object* v_a_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_44_);
v_a_45_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_a_45_);
v_a_46_ = lean_ctor_get(v_x_42_, 1);
lean_inc(v_a_46_);
lean_dec_ref(v_x_42_);
v___x_47_ = lean_apply_2(v_h__1_43_, v_a_45_, v_a_46_);
return v___x_47_;
}
else
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_43_);
v_a_48_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_a_48_);
v_a_49_ = lean_ctor_get(v_x_42_, 1);
lean_inc(v_a_49_);
lean_dec_ref(v_x_42_);
v___x_50_ = lean_apply_2(v_h__2_44_, v_a_48_, v_a_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter(lean_object* v_00_u03b5_51_, lean_object* v_00_u03c3_52_, lean_object* v_00_u03b1_53_, lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter___redArg(v_x_55_, v_h__1_56_, v_h__2_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v_a_62_; lean_object* v_a_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_61_);
v_a_62_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_62_);
v_a_63_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_a_63_);
lean_dec_ref(v_x_59_);
v___x_64_ = lean_apply_2(v_h__1_60_, v_a_62_, v_a_63_);
return v___x_64_;
}
else
{
lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_60_);
v_a_65_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_65_);
v_a_66_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_a_66_);
lean_dec_ref(v_x_59_);
v___x_67_ = lean_apply_2(v_h__2_61_, v_a_65_, v_a_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object* v_00_u03b5_68_, lean_object* v_00_u03c3_69_, lean_object* v_00_u03b1_70_, lean_object* v_motive_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(v_x_72_, v_h__1_73_, v_h__2_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter___redArg(lean_object* v_x_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec(v_h__1_77_);
v_a_79_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_a_79_);
lean_dec_ref(v_x_76_);
v___x_80_ = lean_apply_1(v_h__2_78_, v_a_79_);
return v___x_80_;
}
else
{
lean_object* v_a_81_; lean_object* v___x_82_; 
lean_dec(v_h__2_78_);
v_a_81_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_a_81_);
lean_dec_ref(v_x_76_);
v___x_82_ = lean_apply_1(v_h__1_77_, v_a_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter(lean_object* v_00_u03b5_83_, lean_object* v_00_u03b1_84_, lean_object* v_motive_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter___redArg(v_x_86_, v_h__1_87_, v_h__2_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_91_);
v_a_93_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_a_93_);
lean_dec_ref(v_x_90_);
v___x_94_ = lean_apply_1(v_h__2_92_, v_a_93_);
return v___x_94_;
}
else
{
lean_object* v_a_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_92_);
v_a_95_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_a_95_);
lean_dec_ref(v_x_90_);
v___x_96_ = lean_apply_1(v_h__1_91_, v_a_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_97_, lean_object* v_00_u03b1_98_, lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter___redArg(v_x_100_, v_h__1_101_, v_h__2_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
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
lean_dec_ref(v_x_104_);
v___x_110_ = lean_apply_1(v_h__1_105_, v_val_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_111_, lean_object* v_motive_112_, lean_object* v_x_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter___redArg(v_x_113_, v_h__1_114_, v_h__2_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object* v_____do__lift_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_){
_start:
{
if (lean_obj_tag(v_____do__lift_117_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_119_);
v_val_120_ = lean_ctor_get(v_____do__lift_117_, 0);
lean_inc(v_val_120_);
lean_dec_ref(v_____do__lift_117_);
v___x_121_ = lean_apply_1(v_h__1_118_, v_val_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_h__1_118_);
v___x_122_ = lean_apply_2(v_h__2_119_, v_____do__lift_117_, lean_box(0));
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter(lean_object* v_00_u03b1_123_, lean_object* v_motive_124_, lean_object* v_____do__lift_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_){
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
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
if (lean_obj_tag(v_x_131_) == 1)
{
lean_object* v_a_134_; lean_object* v_a_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_133_);
v_a_134_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_a_134_);
v_a_135_ = lean_ctor_get(v_x_131_, 1);
lean_inc(v_a_135_);
lean_dec_ref(v_x_131_);
v___x_136_ = lean_apply_2(v_h__1_132_, v_a_134_, v_a_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; 
lean_dec(v_h__1_132_);
v___x_137_ = lean_apply_2(v_h__2_133_, v_x_131_, lean_box(0));
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter(lean_object* v_00_u03b5_138_, lean_object* v_00_u03c3_139_, lean_object* v_00_u03b1_140_, lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
if (lean_obj_tag(v_x_142_) == 1)
{
lean_object* v_a_145_; lean_object* v_a_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_144_);
v_a_145_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_a_145_);
v_a_146_ = lean_ctor_get(v_x_142_, 1);
lean_inc(v_a_146_);
lean_dec_ref(v_x_142_);
v___x_147_ = lean_apply_2(v_h__1_143_, v_a_145_, v_a_146_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; 
lean_dec(v_h__1_143_);
v___x_148_ = lean_apply_2(v_h__2_144_, v_x_142_, lean_box(0));
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter___redArg(lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_153_; 
lean_dec(v_h__1_151_);
v___x_153_ = lean_apply_1(v_h__2_152_, v_x_150_);
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_155_; 
lean_dec(v_h__2_152_);
v_val_154_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_val_154_);
lean_dec_ref(v_x_149_);
v___x_155_ = lean_apply_2(v_h__1_151_, v_val_154_, v_x_150_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter(lean_object* v_00_u03b1_156_, lean_object* v_motive_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter___redArg(v_x_158_, v_x_159_, v_h__1_160_, v_h__2_161_);
return v___x_162_;
}
}
lean_object* runtime_initialize_Std_Do_WP_Monad(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_WP_SimpLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_WP_SimpLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_WP_Monad(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_WP_SimpLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_WP_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_WP_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_WP_SimpLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
