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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_){
_start:
{
if (lean_obj_tag(v_x_34_) == 1)
{
lean_object* v_a_37_; lean_object* v_a_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_36_);
v_a_37_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_a_37_);
v_a_38_ = lean_ctor_get(v_x_34_, 1);
lean_inc(v_a_38_);
lean_dec_ref_known(v_x_34_, 2);
v___x_39_ = lean_apply_2(v_h__1_35_, v_a_37_, v_a_38_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; 
lean_dec(v_h__1_35_);
v___x_40_ = lean_apply_2(v_h__2_36_, v_x_34_, lean_box(0));
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_tryCatch_match__1_splitter(lean_object* v_00_u03b5_41_, lean_object* v_00_u03c3_42_, lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_x_45_) == 1)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_47_);
v_a_48_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_a_48_);
v_a_49_ = lean_ctor_get(v_x_45_, 1);
lean_inc(v_a_49_);
lean_dec_ref_known(v_x_45_, 2);
v___x_50_ = lean_apply_2(v_h__1_46_, v_a_48_, v_a_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v___x_51_ = lean_apply_2(v_h__2_47_, v_x_45_, lean_box(0));
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter___redArg(lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v_a_55_; lean_object* v_a_56_; lean_object* v___x_57_; 
lean_dec(v_h__2_54_);
v_a_55_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_a_55_);
v_a_56_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_a_56_);
lean_dec_ref_known(v_x_52_, 2);
v___x_57_ = lean_apply_2(v_h__1_53_, v_a_55_, v_a_56_);
return v___x_57_;
}
else
{
lean_object* v_a_58_; lean_object* v_a_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_53_);
v_a_58_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_a_58_);
v_a_59_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_a_59_);
lean_dec_ref_known(v_x_52_, 2);
v___x_60_ = lean_apply_2(v_h__2_54_, v_a_58_, v_a_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Std_WP_EStateM_wpInst_match__1_splitter(lean_object* v_00_u03b5_61_, lean_object* v_00_u03c3_62_, lean_object* v_00_u03b1_63_, lean_object* v_motive_64_, lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_67_);
v_a_68_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_a_69_);
lean_dec_ref_known(v_x_65_, 2);
v___x_70_ = lean_apply_2(v_h__1_66_, v_a_68_, v_a_69_);
return v___x_70_;
}
else
{
lean_object* v_a_71_; lean_object* v_a_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_66_);
v_a_71_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_a_71_);
v_a_72_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_a_72_);
lean_dec_ref_known(v_x_65_, 2);
v___x_73_ = lean_apply_2(v_h__2_67_, v_a_71_, v_a_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(lean_object* v_____do__lift_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
if (lean_obj_tag(v_____do__lift_74_) == 1)
{
lean_object* v_val_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_76_);
v_val_77_ = lean_ctor_get(v_____do__lift_74_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v_____do__lift_74_, 1);
v___x_78_ = lean_apply_1(v_h__1_75_, v_val_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; 
lean_dec(v_h__1_75_);
v___x_79_ = lean_apply_2(v_h__2_76_, v_____do__lift_74_, lean_box(0));
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__OptionT_orElse_match__1_splitter(lean_object* v_00_u03b1_80_, lean_object* v_motive_81_, lean_object* v_____do__lift_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
if (lean_obj_tag(v_____do__lift_82_) == 1)
{
lean_object* v_val_85_; lean_object* v___x_86_; 
lean_dec(v_h__2_84_);
v_val_85_ = lean_ctor_get(v_____do__lift_82_, 0);
lean_inc(v_val_85_);
lean_dec_ref_known(v_____do__lift_82_, 1);
v___x_86_ = lean_apply_1(v_h__1_83_, v_val_85_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; 
lean_dec(v_h__1_83_);
v___x_87_ = lean_apply_2(v_h__2_84_, v_____do__lift_82_, lean_box(0));
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_89_);
v_a_91_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_a_92_);
lean_dec_ref_known(v_x_88_, 2);
v___x_93_ = lean_apply_2(v_h__2_90_, v_a_91_, v_a_92_);
return v___x_93_;
}
else
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_90_);
v_a_94_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_a_94_);
v_a_95_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_a_95_);
lean_dec_ref_known(v_x_88_, 2);
v___x_96_ = lean_apply_2(v_h__1_89_, v_a_94_, v_a_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__EStateM_adaptExcept_match__1_splitter(lean_object* v_00_u03b5_97_, lean_object* v_00_u03c3_98_, lean_object* v_00_u03b1_99_, lean_object* v_motive_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v_a_104_; lean_object* v_a_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_102_);
v_a_104_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_a_104_);
v_a_105_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_a_105_);
lean_dec_ref_known(v_x_101_, 2);
v___x_106_ = lean_apply_2(v_h__2_103_, v_a_104_, v_a_105_);
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_109_; 
lean_dec(v_h__2_103_);
v_a_107_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_a_107_);
v_a_108_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_a_108_);
lean_dec_ref_known(v_x_101_, 2);
v___x_109_ = lean_apply_2(v_h__1_102_, v_a_107_, v_a_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter___redArg(lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v___x_114_; 
lean_dec(v_h__1_112_);
v___x_114_ = lean_apply_1(v_h__2_113_, v_x_111_);
return v___x_114_;
}
else
{
lean_object* v_val_115_; lean_object* v___x_116_; 
lean_dec(v_h__2_113_);
v_val_115_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v_x_110_, 1);
v___x_116_ = lean_apply_2(v_h__1_112_, v_val_115_, v_x_111_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Lemmas_0__Option_orElse_match__1_splitter(lean_object* v_00_u03b1_117_, lean_object* v_motive_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_123_; 
lean_dec(v_h__1_121_);
v___x_123_ = lean_apply_1(v_h__2_122_, v_x_120_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; lean_object* v___x_125_; 
lean_dec(v_h__2_122_);
v_val_124_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v_x_119_, 1);
v___x_125_ = lean_apply_2(v_h__1_121_, v_val_124_, v_x_120_);
return v___x_125_;
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
