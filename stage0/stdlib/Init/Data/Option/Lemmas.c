// Lean compiler output
// Module: Init.Data.Option.Lemmas
// Imports: import all Init.Data.Option.BasicAux public import Init.Data.Option.Instances import all Init.Data.Option.Instances public import Init.Ext public import Init.Data.Option.BasicAux public import Init.PropLemmas import Init.Classical import Init.Data.BEq import Init.Data.Bool
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
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
lean_dec_ref(v_x_10_);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_21_; 
lean_dec(v_h__2_20_);
v___x_21_ = lean_apply_1(v_h__1_19_, v_x_18_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_19_);
v_val_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_val_22_);
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_2(v_h__2_20_, v_val_22_, v_x_18_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_31_; 
lean_dec(v_h__2_30_);
v___x_31_ = lean_apply_1(v_h__1_29_, v_x_28_);
return v___x_31_;
}
else
{
lean_object* v_val_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_29_);
v_val_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_val_32_);
lean_dec_ref(v_x_27_);
v___x_33_ = lean_apply_2(v_h__2_30_, v_val_32_, v_x_28_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_, lean_object* v_h__4_39_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_dec(v_h__4_39_);
lean_dec(v_h__2_37_);
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_38_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_36_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_36_);
v_val_42_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_val_42_);
lean_dec_ref(v_x_35_);
v___x_43_ = lean_apply_1(v_h__3_38_, v_val_42_);
return v___x_43_;
}
}
else
{
lean_dec(v_h__3_38_);
lean_dec(v_h__1_36_);
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_h__4_39_);
v_val_44_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_val_44_);
lean_dec_ref(v_x_34_);
v___x_45_ = lean_apply_1(v_h__2_37_, v_val_44_);
return v___x_45_;
}
else
{
lean_object* v_val_46_; lean_object* v_val_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_37_);
v_val_46_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_val_46_);
lean_dec_ref(v_x_34_);
v_val_47_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_val_47_);
lean_dec_ref(v_x_35_);
v___x_48_ = lean_apply_2(v_h__4_39_, v_val_46_, v_val_47_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter(lean_object* v_00_u03b1_49_, lean_object* v_motive_50_, lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_, lean_object* v_h__3_55_, lean_object* v_h__4_56_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_dec(v_h__4_56_);
lean_dec(v_h__2_54_);
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__3_55_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__1_53_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_53_);
v_val_59_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_val_59_);
lean_dec_ref(v_x_52_);
v___x_60_ = lean_apply_1(v_h__3_55_, v_val_59_);
return v___x_60_;
}
}
else
{
lean_dec(v_h__3_55_);
lean_dec(v_h__1_53_);
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v_val_61_; lean_object* v___x_62_; 
lean_dec(v_h__4_56_);
v_val_61_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_val_61_);
lean_dec_ref(v_x_51_);
v___x_62_ = lean_apply_1(v_h__2_54_, v_val_61_);
return v___x_62_;
}
else
{
lean_object* v_val_63_; lean_object* v_val_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_54_);
v_val_63_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_val_63_);
lean_dec_ref(v_x_51_);
v_val_64_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_val_64_);
lean_dec_ref(v_x_52_);
v___x_65_ = lean_apply_2(v_h__4_56_, v_val_63_, v_val_64_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_70_; 
lean_dec(v_h__1_68_);
v___x_70_ = lean_apply_1(v_h__2_69_, v_x_67_);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_72_; 
lean_dec(v_h__2_69_);
v_val_71_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v_x_66_);
v___x_72_ = lean_apply_2(v_h__1_68_, v_val_71_, v_x_67_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter(lean_object* v_00_u03b1_73_, lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_79_; 
lean_dec(v_h__1_77_);
v___x_79_ = lean_apply_1(v_h__2_78_, v_x_76_);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_78_);
v_val_80_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_val_80_);
lean_dec_ref(v_x_75_);
v___x_81_ = lean_apply_2(v_h__1_77_, v_val_80_, v_x_76_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_85_; 
lean_dec(v_h__2_84_);
v___x_85_ = lean_apply_1(v_h__1_83_, lean_box(0));
return v___x_85_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_83_);
v_val_86_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_val_86_);
lean_dec_ref(v_x_82_);
v___x_87_ = lean_apply_2(v_h__2_84_, v_val_86_, lean_box(0));
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter(lean_object* v_00_u03b1_88_, lean_object* v_p_89_, lean_object* v_motive_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v___x_95_; 
lean_dec(v_h__2_94_);
v___x_95_ = lean_apply_1(v_h__1_93_, lean_box(0));
return v___x_95_;
}
else
{
lean_object* v_val_96_; lean_object* v___x_97_; 
lean_dec(v_h__1_93_);
v_val_96_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_val_96_);
lean_dec_ref(v_x_91_);
v___x_97_ = lean_apply_2(v_h__2_94_, v_val_96_, lean_box(0));
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(lean_object* v_o_98_, lean_object* v_p_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
if (lean_obj_tag(v_o_98_) == 0)
{
lean_object* v___x_102_; 
lean_dec(v_h__2_101_);
v___x_102_ = lean_apply_1(v_h__1_100_, v_p_99_);
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_100_);
v_val_103_ = lean_ctor_get(v_o_98_, 0);
lean_inc(v_val_103_);
lean_dec_ref(v_o_98_);
v___x_104_ = lean_apply_2(v_h__2_101_, v_val_103_, v_p_99_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter(lean_object* v_00_u03b1_105_, lean_object* v_motive_106_, lean_object* v_o_107_, lean_object* v_p_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_){
_start:
{
if (lean_obj_tag(v_o_107_) == 0)
{
lean_object* v___x_111_; 
lean_dec(v_h__2_110_);
v___x_111_ = lean_apply_1(v_h__1_109_, v_p_108_);
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_109_);
v_val_112_ = lean_ctor_get(v_o_107_, 0);
lean_inc(v_val_112_);
lean_dec_ref(v_o_107_);
v___x_113_ = lean_apply_2(v_h__2_110_, v_val_112_, v_p_108_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_, lean_object* v_h__3_118_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_dec(v_h__2_117_);
if (lean_obj_tag(v_x_115_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_120_; 
lean_dec(v_h__3_118_);
v_val_119_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_val_119_);
lean_dec_ref(v_x_115_);
v___x_120_ = lean_apply_1(v_h__1_116_, v_val_119_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_h__1_116_);
v___x_121_ = lean_apply_4(v_h__3_118_, v_x_114_, v_x_115_, lean_box(0), lean_box(0));
return v___x_121_;
}
}
else
{
lean_dec(v_h__1_116_);
if (lean_obj_tag(v_x_115_) == 1)
{
lean_object* v_val_122_; lean_object* v_val_123_; lean_object* v___x_124_; 
lean_dec(v_h__3_118_);
v_val_122_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_val_122_);
lean_dec_ref(v_x_114_);
v_val_123_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_val_123_);
lean_dec_ref(v_x_115_);
v___x_124_ = lean_apply_2(v_h__2_117_, v_val_122_, v_val_123_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
lean_dec(v_h__2_117_);
v___x_125_ = lean_apply_4(v_h__3_118_, v_x_114_, v_x_115_, lean_box(0), lean_box(0));
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_motive_128_, lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_, lean_object* v_h__3_133_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_dec(v_h__2_132_);
if (lean_obj_tag(v_x_130_) == 1)
{
lean_object* v_val_134_; lean_object* v___x_135_; 
lean_dec(v_h__3_133_);
v_val_134_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v_x_130_);
v___x_135_ = lean_apply_1(v_h__1_131_, v_val_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
lean_dec(v_h__1_131_);
v___x_136_ = lean_apply_4(v_h__3_133_, v_x_129_, v_x_130_, lean_box(0), lean_box(0));
return v___x_136_;
}
}
else
{
lean_dec(v_h__1_131_);
if (lean_obj_tag(v_x_130_) == 1)
{
lean_object* v_val_137_; lean_object* v_val_138_; lean_object* v___x_139_; 
lean_dec(v_h__3_133_);
v_val_137_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_val_137_);
lean_dec_ref(v_x_129_);
v_val_138_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_val_138_);
lean_dec_ref(v_x_130_);
v___x_139_ = lean_apply_2(v_h__2_132_, v_val_137_, v_val_138_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; 
lean_dec(v_h__2_132_);
v___x_140_ = lean_apply_4(v_h__3_133_, v_x_129_, v_x_130_, lean_box(0), lean_box(0));
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_, lean_object* v_h__3_145_, lean_object* v_h__4_146_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_dec(v_h__4_146_);
lean_dec(v_h__3_145_);
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_143_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_1(v_h__2_144_, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_150_; 
lean_dec(v_h__2_144_);
v_val_149_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_val_149_);
lean_dec_ref(v_x_142_);
v___x_150_ = lean_apply_1(v_h__1_143_, v_val_149_);
return v___x_150_;
}
}
else
{
lean_dec(v_h__2_144_);
lean_dec(v_h__1_143_);
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v_val_151_; lean_object* v___x_152_; 
lean_dec(v_h__4_146_);
v_val_151_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v_x_141_);
v___x_152_ = lean_apply_1(v_h__3_145_, v_val_151_);
return v___x_152_;
}
else
{
lean_object* v_val_153_; lean_object* v_val_154_; lean_object* v___x_155_; 
lean_dec(v_h__3_145_);
v_val_153_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_val_153_);
lean_dec_ref(v_x_141_);
v_val_154_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_val_154_);
lean_dec_ref(v_x_142_);
v___x_155_ = lean_apply_2(v_h__4_146_, v_val_153_, v_val_154_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_motive_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_, lean_object* v_h__3_163_, lean_object* v_h__4_164_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_dec(v_h__4_164_);
lean_dec(v_h__3_163_);
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_h__1_161_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v_h__2_162_, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_val_167_; lean_object* v___x_168_; 
lean_dec(v_h__2_162_);
v_val_167_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_val_167_);
lean_dec_ref(v_x_160_);
v___x_168_ = lean_apply_1(v_h__1_161_, v_val_167_);
return v___x_168_;
}
}
else
{
lean_dec(v_h__2_162_);
lean_dec(v_h__1_161_);
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v_val_169_; lean_object* v___x_170_; 
lean_dec(v_h__4_164_);
v_val_169_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_val_169_);
lean_dec_ref(v_x_159_);
v___x_170_ = lean_apply_1(v_h__3_163_, v_val_169_);
return v___x_170_;
}
else
{
lean_object* v_val_171_; lean_object* v_val_172_; lean_object* v___x_173_; 
lean_dec(v_h__3_163_);
v_val_171_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_val_171_);
lean_dec_ref(v_x_159_);
v_val_172_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_val_172_);
lean_dec_ref(v_x_160_);
v___x_173_ = lean_apply_2(v_h__4_164_, v_val_171_, v_val_172_);
return v___x_173_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
