// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
// Imports: public import Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap public import Std.Data.Iterators.Lemmas.Equivalence.StepCongr
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v_it_5_; lean_object* v_out_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_it_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_5_);
v_out_6_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_out_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_2(v_h__1_2_, v_it_5_, v_out_6_);
return v___x_7_;
}
case 1:
{
lean_object* v_it_8_; lean_object* v___x_9_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_it_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_8_);
lean_dec_ref(v_x_1_);
v___x_9_ = lean_apply_1(v_h__2_3_, v_it_8_);
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_apply_1(v_h__3_4_, v___x_10_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter(lean_object* v_m_12_, lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
_start:
{
switch(lean_obj_tag(v_x_16_))
{
case 0:
{
lean_object* v_it_20_; lean_object* v_out_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__2_18_);
v_it_20_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_it_20_);
v_out_21_ = lean_ctor_get(v_x_16_, 1);
lean_inc(v_out_21_);
lean_dec_ref(v_x_16_);
v___x_22_ = lean_apply_2(v_h__1_17_, v_it_20_, v_out_21_);
return v___x_22_;
}
case 1:
{
lean_object* v_it_23_; lean_object* v___x_24_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__1_17_);
v_it_23_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_it_23_);
lean_dec_ref(v_x_16_);
v___x_24_ = lean_apply_1(v_h__2_18_, v_it_23_);
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_18_);
lean_dec(v_h__1_17_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_apply_1(v_h__3_19_, v___x_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_____do__lift_27_) == 0)
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
v_val_32_ = lean_ctor_get(v_____do__lift_27_, 0);
lean_inc(v_val_32_);
lean_dec_ref(v_____do__lift_27_);
v___x_33_ = lean_apply_1(v_h__1_28_, v_val_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_34_, lean_object* v_motive_35_, lean_object* v_____do__lift_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_____do__lift_36_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__2_38_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_38_);
v_val_41_ = lean_ctor_get(v_____do__lift_36_, 0);
lean_inc(v_val_41_);
lean_dec_ref(v_____do__lift_36_);
v___x_42_ = lean_apply_1(v_h__1_37_, v_val_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 0:
{
lean_object* v_it_47_; lean_object* v_out_48_; lean_object* v___x_49_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v_it_47_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_it_47_);
v_out_48_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_out_48_);
lean_dec_ref(v_x_43_);
v___x_49_ = lean_apply_3(v_h__1_44_, v_it_47_, v_out_48_, lean_box(0));
return v___x_49_;
}
case 1:
{
lean_object* v_it_50_; lean_object* v___x_51_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__1_44_);
v_it_50_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_it_50_);
lean_dec_ref(v_x_43_);
v___x_51_ = lean_apply_2(v_h__2_45_, v_it_50_, lean_box(0));
return v___x_51_;
}
default: 
{
lean_object* v___x_52_; 
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v___x_52_ = lean_apply_1(v_h__3_46_, lean_box(0));
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_m_55_, lean_object* v_inst_56_, lean_object* v_it_57_, lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_, lean_object* v_h__3_62_){
_start:
{
switch(lean_obj_tag(v_x_59_))
{
case 0:
{
lean_object* v_it_63_; lean_object* v_out_64_; lean_object* v___x_65_; 
lean_dec(v_h__3_62_);
lean_dec(v_h__2_61_);
v_it_63_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_it_63_);
v_out_64_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_out_64_);
lean_dec_ref(v_x_59_);
v___x_65_ = lean_apply_3(v_h__1_60_, v_it_63_, v_out_64_, lean_box(0));
return v___x_65_;
}
case 1:
{
lean_object* v_it_66_; lean_object* v___x_67_; 
lean_dec(v_h__3_62_);
lean_dec(v_h__1_60_);
v_it_66_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_it_66_);
lean_dec_ref(v_x_59_);
v___x_67_ = lean_apply_2(v_h__2_61_, v_it_66_, lean_box(0));
return v___x_67_;
}
default: 
{
lean_object* v___x_68_; 
lean_dec(v_h__2_61_);
lean_dec(v_h__1_60_);
v___x_68_ = lean_apply_1(v_h__3_62_, lean_box(0));
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_m_71_, lean_object* v_inst_72_, lean_object* v_it_73_, lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_69_, v_00_u03b2_70_, v_m_71_, v_inst_72_, v_it_73_, v_motive_74_, v_x_75_, v_h__1_76_, v_h__2_77_, v_h__3_78_);
lean_dec(v_it_73_);
lean_dec(v_inst_72_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_){
_start:
{
if (lean_obj_tag(v_____do__lift_80_) == 0)
{
lean_object* v___x_83_; 
lean_dec(v_h__2_82_);
v___x_83_ = lean_apply_1(v_h__1_81_, lean_box(0));
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_85_; 
lean_dec(v_h__1_81_);
v_val_84_ = lean_ctor_get(v_____do__lift_80_, 0);
lean_inc(v_val_84_);
lean_dec_ref(v_____do__lift_80_);
v___x_85_ = lean_apply_2(v_h__2_82_, v_val_84_, lean_box(0));
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_86_, lean_object* v_00_u03b2_x27_87_, lean_object* v_n_88_, lean_object* v_f_89_, lean_object* v_out_90_, lean_object* v_motive_91_, lean_object* v_____do__lift_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
if (lean_obj_tag(v_____do__lift_92_) == 0)
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
v_val_96_ = lean_ctor_get(v_____do__lift_92_, 0);
lean_inc(v_val_96_);
lean_dec_ref(v_____do__lift_92_);
v___x_97_ = lean_apply_2(v_h__2_94_, v_val_96_, lean_box(0));
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_98_, lean_object* v_00_u03b2_x27_99_, lean_object* v_n_100_, lean_object* v_f_101_, lean_object* v_out_102_, lean_object* v_motive_103_, lean_object* v_____do__lift_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_98_, v_00_u03b2_x27_99_, v_n_100_, v_f_101_, v_out_102_, v_motive_103_, v_____do__lift_104_, v_h__1_105_, v_h__2_106_);
lean_dec(v_out_102_);
lean_dec(v_f_101_);
return v_res_107_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
}
#ifdef __cplusplus
}
#endif
