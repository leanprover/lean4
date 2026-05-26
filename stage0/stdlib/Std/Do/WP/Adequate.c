// Lean compiler output
// Module: Std.Do.WP.Adequate
// Imports: public import Std.Do.WP.Monad public import Init.Control.Ensures
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
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b5_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
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
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter___redArg(lean_object* v_r_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_r_18_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_19_);
v_a_21_ = lean_ctor_get(v_r_18_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v_r_18_, 1);
v___x_22_ = lean_apply_1(v_h__2_20_, v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_h__2_20_);
v_a_23_ = lean_ctor_get(v_r_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref_known(v_r_18_, 1);
v___x_24_ = lean_apply_1(v_h__1_19_, v_a_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter(lean_object* v_00_u03b5_25_, lean_object* v_00_u03b1_26_, lean_object* v_motive_27_, lean_object* v_r_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
if (lean_obj_tag(v_r_28_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_29_);
v_a_31_ = lean_ctor_get(v_r_28_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v_r_28_, 1);
v___x_32_ = lean_apply_1(v_h__2_30_, v_a_31_);
return v___x_32_;
}
else
{
lean_object* v_a_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_30_);
v_a_33_ = lean_ctor_get(v_r_28_, 0);
lean_inc(v_a_33_);
lean_dec_ref_known(v_r_28_, 1);
v___x_34_ = lean_apply_1(v_h__1_29_, v_a_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter___redArg(lean_object* v_r_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_r_35_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_36_);
v_a_38_ = lean_ctor_get(v_r_35_, 0);
lean_inc(v_a_38_);
lean_dec_ref_known(v_r_35_, 1);
v___x_39_ = lean_apply_2(v_h__2_37_, v_a_38_, lean_box(0));
return v___x_39_;
}
else
{
lean_object* v_a_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_37_);
v_a_40_ = lean_ctor_get(v_r_35_, 0);
lean_inc(v_a_40_);
lean_dec_ref_known(v_r_35_, 1);
v___x_41_ = lean_apply_2(v_h__1_36_, v_a_40_, lean_box(0));
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter(lean_object* v_00_u03b5_42_, lean_object* v_00_u03b1_43_, lean_object* v_P_44_, lean_object* v_motive_45_, lean_object* v_r_46_, lean_object* v_h_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
if (lean_obj_tag(v_r_46_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_48_);
v_a_50_ = lean_ctor_get(v_r_46_, 0);
lean_inc(v_a_50_);
lean_dec_ref_known(v_r_46_, 1);
v___x_51_ = lean_apply_2(v_h__2_49_, v_a_50_, lean_box(0));
return v___x_51_;
}
else
{
lean_object* v_a_52_; lean_object* v___x_53_; 
lean_dec(v_h__2_49_);
v_a_52_ = lean_ctor_get(v_r_46_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v_r_46_, 1);
v___x_53_ = lean_apply_2(v_h__1_48_, v_a_52_, lean_box(0));
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_55_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__2_56_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_56_);
v_val_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_59_);
lean_dec_ref_known(v_x_54_, 1);
v___x_60_ = lean_apply_1(v_h__1_55_, v_val_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_61_, lean_object* v_motive_62_, lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_64_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_apply_1(v_h__2_65_, v___x_66_);
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_69_; 
lean_dec(v_h__2_65_);
v_val_68_ = lean_ctor_get(v_x_63_, 0);
lean_inc(v_val_68_);
lean_dec_ref_known(v_x_63_, 1);
v___x_69_ = lean_apply_1(v_h__1_64_, v_val_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter___redArg(lean_object* v_r_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_r_70_) == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__1_71_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__2_72_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_76_; 
lean_dec(v_h__2_72_);
v_val_75_ = lean_ctor_get(v_r_70_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v_r_70_, 1);
v___x_76_ = lean_apply_1(v_h__1_71_, v_val_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter(lean_object* v_00_u03b1_77_, lean_object* v_motive_78_, lean_object* v_r_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_r_79_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__1_80_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__2_81_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_81_);
v_val_84_ = lean_ctor_get(v_r_79_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v_r_79_, 1);
v___x_85_ = lean_apply_1(v_h__1_80_, v_val_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter___redArg(lean_object* v_r_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_r_86_) == 0)
{
lean_object* v___x_89_; 
lean_dec(v_h__1_87_);
v___x_89_ = lean_apply_1(v_h__2_88_, lean_box(0));
return v___x_89_;
}
else
{
lean_object* v_val_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_88_);
v_val_90_ = lean_ctor_get(v_r_86_, 0);
lean_inc(v_val_90_);
lean_dec_ref_known(v_r_86_, 1);
v___x_91_ = lean_apply_2(v_h__1_87_, v_val_90_, lean_box(0));
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter(lean_object* v_00_u03b1_92_, lean_object* v_P_93_, lean_object* v_motive_94_, lean_object* v_r_95_, lean_object* v_h_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
if (lean_obj_tag(v_r_95_) == 0)
{
lean_object* v___x_99_; 
lean_dec(v_h__1_97_);
v___x_99_ = lean_apply_1(v_h__2_98_, lean_box(0));
return v___x_99_;
}
else
{
lean_object* v_val_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_98_);
v_val_100_ = lean_ctor_get(v_r_95_, 0);
lean_inc(v_val_100_);
lean_dec_ref_known(v_r_95_, 1);
v___x_101_ = lean_apply_2(v_h__1_97_, v_val_100_, lean_box(0));
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter___redArg(lean_object* v_____do__lift_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_____do__lift_102_) == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_103_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__2_104_, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_104_);
v_val_107_ = lean_ctor_get(v_____do__lift_102_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_____do__lift_102_, 1);
v___x_108_ = lean_apply_1(v_h__1_103_, v_val_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter(lean_object* v_00_u03b1_109_, lean_object* v_motive_110_, lean_object* v_____do__lift_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
if (lean_obj_tag(v_____do__lift_111_) == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__1_112_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__2_113_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v_val_116_; lean_object* v___x_117_; 
lean_dec(v_h__2_113_);
v_val_116_ = lean_ctor_get(v_____do__lift_111_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v_____do__lift_111_, 1);
v___x_117_ = lean_apply_1(v_h__1_112_, v_val_116_);
return v___x_117_;
}
}
}
lean_object* runtime_initialize_Std_Do_WP_Monad(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Ensures(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_WP_Adequate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Ensures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_WP_Adequate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_WP_Monad(uint8_t builtin);
lean_object* initialize_Init_Control_Ensures(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_WP_Adequate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Ensures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_WP_Adequate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_WP_Adequate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_WP_Adequate(builtin);
}
#ifdef __cplusplus
}
#endif
