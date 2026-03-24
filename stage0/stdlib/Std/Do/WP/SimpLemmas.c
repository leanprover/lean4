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
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
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
lean_dec_ref(v_x_18_);
v___x_24_ = lean_apply_1(v_h__1_19_, v_val_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
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
lean_dec_ref(v_x_27_);
v___x_33_ = lean_apply_1(v_h__1_28_, v_val_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter___redArg(lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_38_; 
lean_dec(v_h__2_36_);
v_a_37_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_a_37_);
lean_dec_ref(v_x_34_);
v___x_38_ = lean_apply_1(v_h__1_35_, v_a_37_);
return v___x_38_;
}
else
{
lean_object* v_a_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_35_);
v_a_39_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_a_39_);
lean_dec_ref(v_x_34_);
v___x_40_ = lean_apply_1(v_h__2_36_, v_a_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter(lean_object* v_00_u03b5_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_46_);
v_a_47_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_a_47_);
lean_dec_ref(v_x_44_);
v___x_48_ = lean_apply_1(v_h__1_45_, v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_45_);
v_a_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_a_49_);
lean_dec_ref(v_x_44_);
v___x_50_ = lean_apply_1(v_h__2_46_, v_a_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_53_);
v_a_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_54_);
v_a_55_ = lean_ctor_get(v_x_51_, 1);
lean_inc(v_a_55_);
lean_dec_ref(v_x_51_);
v___x_56_ = lean_apply_2(v_h__1_52_, v_a_54_, v_a_55_);
return v___x_56_;
}
else
{
lean_object* v_a_57_; lean_object* v_a_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_52_);
v_a_57_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_57_);
v_a_58_ = lean_ctor_get(v_x_51_, 1);
lean_inc(v_a_58_);
lean_dec_ref(v_x_51_);
v___x_59_ = lean_apply_2(v_h__2_53_, v_a_57_, v_a_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter(lean_object* v_00_u03b5_60_, lean_object* v_00_u03c3_61_, lean_object* v_00_u03b1_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; 
lean_dec(v_h__2_66_);
v_a_67_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_a_67_);
v_a_68_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_a_68_);
lean_dec_ref(v_x_64_);
v___x_69_ = lean_apply_2(v_h__1_65_, v_a_67_, v_a_68_);
return v___x_69_;
}
else
{
lean_object* v_a_70_; lean_object* v_a_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_65_);
v_a_70_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_a_70_);
v_a_71_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_a_71_);
lean_dec_ref(v_x_64_);
v___x_72_ = lean_apply_2(v_h__2_66_, v_a_70_, v_a_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v_a_76_; lean_object* v_a_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_75_);
v_a_76_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_a_76_);
v_a_77_ = lean_ctor_get(v_x_73_, 1);
lean_inc(v_a_77_);
lean_dec_ref(v_x_73_);
v___x_78_ = lean_apply_2(v_h__1_74_, v_a_76_, v_a_77_);
return v___x_78_;
}
else
{
lean_object* v_a_79_; lean_object* v_a_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_74_);
v_a_79_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_a_79_);
v_a_80_ = lean_ctor_get(v_x_73_, 1);
lean_inc(v_a_80_);
lean_dec_ref(v_x_73_);
v___x_81_ = lean_apply_2(v_h__2_75_, v_a_79_, v_a_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object* v_00_u03b5_82_, lean_object* v_00_u03c3_83_, lean_object* v_00_u03b1_84_, lean_object* v_motive_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_88_);
v_a_89_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_a_89_);
v_a_90_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_a_90_);
lean_dec_ref(v_x_86_);
v___x_91_ = lean_apply_2(v_h__1_87_, v_a_89_, v_a_90_);
return v___x_91_;
}
else
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_87_);
v_a_92_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_a_93_);
lean_dec_ref(v_x_86_);
v___x_94_ = lean_apply_2(v_h__2_88_, v_a_92_, v_a_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter___redArg(lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; 
lean_dec(v_h__1_96_);
v_a_98_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_a_98_);
lean_dec_ref(v_x_95_);
v___x_99_ = lean_apply_1(v_h__2_97_, v_a_98_);
return v___x_99_;
}
else
{
lean_object* v_a_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_97_);
v_a_100_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_a_100_);
lean_dec_ref(v_x_95_);
v___x_101_ = lean_apply_1(v_h__1_96_, v_a_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter(lean_object* v_00_u03b5_102_, lean_object* v_00_u03b1_103_, lean_object* v_motive_104_, lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_106_);
v_a_108_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_a_108_);
lean_dec_ref(v_x_105_);
v___x_109_ = lean_apply_1(v_h__2_107_, v_a_108_);
return v___x_109_;
}
else
{
lean_object* v_a_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_107_);
v_a_110_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_a_110_);
lean_dec_ref(v_x_105_);
v___x_111_ = lean_apply_1(v_h__1_106_, v_a_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_116_; 
lean_dec(v_h__1_113_);
v_a_115_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_a_115_);
lean_dec_ref(v_x_112_);
v___x_116_ = lean_apply_1(v_h__2_114_, v_a_115_);
return v___x_116_;
}
else
{
lean_object* v_a_117_; lean_object* v___x_118_; 
lean_dec(v_h__2_114_);
v_a_117_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v_x_112_);
v___x_118_ = lean_apply_1(v_h__1_113_, v_a_117_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_119_, lean_object* v_00_u03b1_120_, lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; 
lean_dec(v_h__1_123_);
v_a_125_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_a_125_);
lean_dec_ref(v_x_122_);
v___x_126_ = lean_apply_1(v_h__2_124_, v_a_125_);
return v___x_126_;
}
else
{
lean_object* v_a_127_; lean_object* v___x_128_; 
lean_dec(v_h__2_124_);
v_a_127_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_a_127_);
lean_dec_ref(v_x_122_);
v___x_128_ = lean_apply_1(v_h__1_123_, v_a_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_130_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__2_131_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; lean_object* v___x_135_; 
lean_dec(v_h__2_131_);
v_val_134_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v_x_129_);
v___x_135_ = lean_apply_1(v_h__1_130_, v_val_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_136_, lean_object* v_motive_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_h__1_139_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_apply_1(v_h__2_140_, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_144_; 
lean_dec(v_h__2_140_);
v_val_143_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_val_143_);
lean_dec_ref(v_x_138_);
v___x_144_ = lean_apply_1(v_h__1_139_, v_val_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object* v_____do__lift_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (lean_obj_tag(v_____do__lift_145_) == 1)
{
lean_object* v_val_148_; lean_object* v___x_149_; 
lean_dec(v_h__2_147_);
v_val_148_ = lean_ctor_get(v_____do__lift_145_, 0);
lean_inc(v_val_148_);
lean_dec_ref(v_____do__lift_145_);
v___x_149_ = lean_apply_1(v_h__1_146_, v_val_148_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; 
lean_dec(v_h__1_146_);
v___x_150_ = lean_apply_2(v_h__2_147_, v_____do__lift_145_, lean_box(0));
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter(lean_object* v_00_u03b1_151_, lean_object* v_motive_152_, lean_object* v_____do__lift_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
if (lean_obj_tag(v_____do__lift_153_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_157_; 
lean_dec(v_h__2_155_);
v_val_156_ = lean_ctor_get(v_____do__lift_153_, 0);
lean_inc(v_val_156_);
lean_dec_ref(v_____do__lift_153_);
v___x_157_ = lean_apply_1(v_h__1_154_, v_val_156_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; 
lean_dec(v_h__1_154_);
v___x_158_ = lean_apply_2(v_h__2_155_, v_____do__lift_153_, lean_box(0));
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object* v_x_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_){
_start:
{
if (lean_obj_tag(v_x_159_) == 1)
{
lean_object* v_a_162_; lean_object* v_a_163_; lean_object* v___x_164_; 
lean_dec(v_h__2_161_);
v_a_162_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_a_162_);
v_a_163_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_a_163_);
lean_dec_ref(v_x_159_);
v___x_164_ = lean_apply_2(v_h__1_160_, v_a_162_, v_a_163_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; 
lean_dec(v_h__1_160_);
v___x_165_ = lean_apply_2(v_h__2_161_, v_x_159_, lean_box(0));
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter(lean_object* v_00_u03b5_166_, lean_object* v_00_u03c3_167_, lean_object* v_00_u03b1_168_, lean_object* v_motive_169_, lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
_start:
{
if (lean_obj_tag(v_x_170_) == 1)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_175_; 
lean_dec(v_h__2_172_);
v_a_173_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_a_173_);
v_a_174_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_a_174_);
lean_dec_ref(v_x_170_);
v___x_175_ = lean_apply_2(v_h__1_171_, v_a_173_, v_a_174_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
lean_dec(v_h__1_171_);
v___x_176_ = lean_apply_2(v_h__2_172_, v_x_170_, lean_box(0));
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter___redArg(lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
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
lean_dec_ref(v_x_177_);
v___x_183_ = lean_apply_2(v_h__1_179_, v_val_182_, v_x_178_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter(lean_object* v_00_u03b1_184_, lean_object* v_motive_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
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
lean_dec_ref(v_x_186_);
v___x_192_ = lean_apply_2(v_h__1_188_, v_val_191_, v_x_187_);
return v___x_192_;
}
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
