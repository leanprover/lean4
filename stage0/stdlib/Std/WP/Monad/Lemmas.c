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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Except_toBool_match__1_splitter(lean_object* v_00_u03b5_8_, lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_19_);
v_a_21_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v_x_18_, 1);
v___x_22_ = lean_apply_1(v_h__2_20_, v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_h__2_20_);
v_a_23_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref_known(v_x_18_, 1);
v___x_24_ = lean_apply_1(v_h__1_19_, v_a_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__ExceptT_run__bind_match__1_splitter(lean_object* v_00_u03b5_25_, lean_object* v_00_u03b1_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_29_);
v_a_31_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v_x_28_, 1);
v___x_32_ = lean_apply_1(v_h__2_30_, v_a_31_);
return v___x_32_;
}
else
{
lean_object* v_a_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_30_);
v_a_33_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_a_33_);
lean_dec_ref_known(v_x_28_, 1);
v___x_34_ = lean_apply_1(v_h__1_29_, v_a_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_36_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__2_37_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_val_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_37_);
v_val_40_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v_x_35_, 1);
v___x_41_ = lean_apply_1(v_h__1_36_, v_val_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_45_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__2_46_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_val_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_46_);
v_val_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_val_49_);
lean_dec_ref_known(v_x_44_, 1);
v___x_50_ = lean_apply_1(v_h__1_45_, v_val_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 1)
{
lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_53_);
v_a_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_54_);
v_a_55_ = lean_ctor_get(v_x_51_, 1);
lean_inc(v_a_55_);
lean_dec_ref_known(v_x_51_, 2);
v___x_56_ = lean_apply_2(v_h__1_52_, v_a_54_, v_a_55_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
lean_dec(v_h__1_52_);
v___x_57_ = lean_apply_2(v_h__2_53_, v_x_51_, lean_box(0));
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter(lean_object* v_00_u03b5_58_, lean_object* v_00_u03c3_59_, lean_object* v_00_u03b1_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
if (lean_obj_tag(v_x_62_) == 1)
{
lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_64_);
v_a_65_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_a_65_);
v_a_66_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_a_66_);
lean_dec_ref_known(v_x_62_, 2);
v___x_67_ = lean_apply_2(v_h__1_63_, v_a_65_, v_a_66_);
return v___x_67_;
}
else
{
lean_object* v___x_68_; 
lean_dec(v_h__1_63_);
v___x_68_ = lean_apply_2(v_h__2_64_, v_x_62_, lean_box(0));
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter___redArg(lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v_a_72_; lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_71_);
v_a_72_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_a_72_);
v_a_73_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_a_73_);
lean_dec_ref_known(v_x_69_, 2);
v___x_74_ = lean_apply_2(v_h__1_70_, v_a_72_, v_a_73_);
return v___x_74_;
}
else
{
lean_object* v_a_75_; lean_object* v_a_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_70_);
v_a_75_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_a_75_);
v_a_76_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_a_76_);
lean_dec_ref_known(v_x_69_, 2);
v___x_77_ = lean_apply_2(v_h__2_71_, v_a_75_, v_a_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter(lean_object* v_00_u03b5_78_, lean_object* v_00_u03c3_79_, lean_object* v_00_u03b1_80_, lean_object* v_motive_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v_a_85_; lean_object* v_a_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_84_);
v_a_85_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_a_85_);
v_a_86_ = lean_ctor_get(v_x_82_, 1);
lean_inc(v_a_86_);
lean_dec_ref_known(v_x_82_, 2);
v___x_87_ = lean_apply_2(v_h__1_83_, v_a_85_, v_a_86_);
return v___x_87_;
}
else
{
lean_object* v_a_88_; lean_object* v_a_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_83_);
v_a_88_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_a_88_);
v_a_89_ = lean_ctor_get(v_x_82_, 1);
lean_inc(v_a_89_);
lean_dec_ref_known(v_x_82_, 2);
v___x_90_ = lean_apply_2(v_h__2_84_, v_a_88_, v_a_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object* v_____do__lift_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
if (lean_obj_tag(v_____do__lift_91_) == 1)
{
lean_object* v_val_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_93_);
v_val_94_ = lean_ctor_get(v_____do__lift_91_, 0);
lean_inc(v_val_94_);
lean_dec_ref_known(v_____do__lift_91_, 1);
v___x_95_ = lean_apply_1(v_h__1_92_, v_val_94_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; 
lean_dec(v_h__1_92_);
v___x_96_ = lean_apply_2(v_h__2_93_, v_____do__lift_91_, lean_box(0));
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter(lean_object* v_00_u03b1_97_, lean_object* v_motive_98_, lean_object* v_____do__lift_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
if (lean_obj_tag(v_____do__lift_99_) == 1)
{
lean_object* v_val_102_; lean_object* v___x_103_; 
lean_dec(v_h__2_101_);
v_val_102_ = lean_ctor_get(v_____do__lift_99_, 0);
lean_inc(v_val_102_);
lean_dec_ref_known(v_____do__lift_99_, 1);
v___x_103_ = lean_apply_1(v_h__1_100_, v_val_102_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_dec(v_h__1_100_);
v___x_104_ = lean_apply_2(v_h__2_101_, v_____do__lift_99_, lean_box(0));
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v___x_110_; 
lean_dec(v_h__1_106_);
v_a_108_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_a_108_);
v_a_109_ = lean_ctor_get(v_x_105_, 1);
lean_inc(v_a_109_);
lean_dec_ref_known(v_x_105_, 2);
v___x_110_ = lean_apply_2(v_h__2_107_, v_a_108_, v_a_109_);
return v___x_110_;
}
else
{
lean_object* v_a_111_; lean_object* v_a_112_; lean_object* v___x_113_; 
lean_dec(v_h__2_107_);
v_a_111_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_a_111_);
v_a_112_ = lean_ctor_get(v_x_105_, 1);
lean_inc(v_a_112_);
lean_dec_ref_known(v_x_105_, 2);
v___x_113_ = lean_apply_2(v_h__1_106_, v_a_111_, v_a_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter(lean_object* v_00_u03b5_114_, lean_object* v_00_u03c3_115_, lean_object* v_00_u03b1_116_, lean_object* v_motive_117_, lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_123_; 
lean_dec(v_h__1_119_);
v_a_121_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_a_121_);
v_a_122_ = lean_ctor_get(v_x_118_, 1);
lean_inc(v_a_122_);
lean_dec_ref_known(v_x_118_, 2);
v___x_123_ = lean_apply_2(v_h__2_120_, v_a_121_, v_a_122_);
return v___x_123_;
}
else
{
lean_object* v_a_124_; lean_object* v_a_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_120_);
v_a_124_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_a_124_);
v_a_125_ = lean_ctor_get(v_x_118_, 1);
lean_inc(v_a_125_);
lean_dec_ref_known(v_x_118_, 2);
v___x_126_ = lean_apply_2(v_h__1_119_, v_a_124_, v_a_125_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter___redArg(lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_131_; 
lean_dec(v_h__1_129_);
v___x_131_ = lean_apply_1(v_h__2_130_, v_x_128_);
return v___x_131_;
}
else
{
lean_object* v_val_132_; lean_object* v___x_133_; 
lean_dec(v_h__2_130_);
v_val_132_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_val_132_);
lean_dec_ref_known(v_x_127_, 1);
v___x_133_ = lean_apply_2(v_h__1_129_, v_val_132_, v_x_128_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter(lean_object* v_00_u03b1_134_, lean_object* v_motive_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_140_; 
lean_dec(v_h__1_138_);
v___x_140_ = lean_apply_1(v_h__2_139_, v_x_137_);
return v___x_140_;
}
else
{
lean_object* v_val_141_; lean_object* v___x_142_; 
lean_dec(v_h__2_139_);
v_val_141_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v_x_136_, 1);
v___x_142_ = lean_apply_2(v_h__1_138_, v_val_141_, v_x_137_);
return v___x_142_;
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
