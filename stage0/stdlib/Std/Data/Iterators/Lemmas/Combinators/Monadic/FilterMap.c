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
lean_object* v___x_20_; 
v___x_20_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter___redArg(v_x_16_, v_h__1_17_, v_h__2_18_, v_h__3_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_____do__lift_21_) == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_22_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__2_23_, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_23_);
v_val_26_ = lean_ctor_get(v_____do__lift_21_, 0);
lean_inc(v_val_26_);
lean_dec_ref(v_____do__lift_21_);
v___x_27_ = lean_apply_1(v_h__1_22_, v_val_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_28_, lean_object* v_motive_29_, lean_object* v_____do__lift_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_30_, v_h__1_31_, v_h__2_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_, lean_object* v_h__3_37_){
_start:
{
switch(lean_obj_tag(v_x_34_))
{
case 0:
{
lean_object* v_it_38_; lean_object* v_out_39_; lean_object* v___x_40_; 
lean_dec(v_h__3_37_);
lean_dec(v_h__2_36_);
v_it_38_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_it_38_);
v_out_39_ = lean_ctor_get(v_x_34_, 1);
lean_inc(v_out_39_);
lean_dec_ref(v_x_34_);
v___x_40_ = lean_apply_3(v_h__1_35_, v_it_38_, v_out_39_, lean_box(0));
return v___x_40_;
}
case 1:
{
lean_object* v_it_41_; lean_object* v___x_42_; 
lean_dec(v_h__3_37_);
lean_dec(v_h__1_35_);
v_it_41_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_it_41_);
lean_dec_ref(v_x_34_);
v___x_42_ = lean_apply_2(v_h__2_36_, v_it_41_, lean_box(0));
return v___x_42_;
}
default: 
{
lean_object* v___x_43_; 
lean_dec(v_h__2_36_);
lean_dec(v_h__1_35_);
v___x_43_ = lean_apply_1(v_h__3_37_, lean_box(0));
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_it_48_, lean_object* v_motive_49_, lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_, lean_object* v_h__3_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(v_x_50_, v_h__1_51_, v_h__2_52_, v_h__3_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_m_57_, lean_object* v_inst_58_, lean_object* v_it_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_55_, v_00_u03b2_56_, v_m_57_, v_inst_58_, v_it_59_, v_motive_60_, v_x_61_, v_h__1_62_, v_h__2_63_, v_h__3_64_);
lean_dec(v_it_59_);
lean_dec(v_inst_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
if (lean_obj_tag(v_____do__lift_66_) == 0)
{
lean_object* v___x_69_; 
lean_dec(v_h__2_68_);
v___x_69_ = lean_apply_1(v_h__1_67_, lean_box(0));
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_67_);
v_val_70_ = lean_ctor_get(v_____do__lift_66_, 0);
lean_inc(v_val_70_);
lean_dec_ref(v_____do__lift_66_);
v___x_71_ = lean_apply_2(v_h__2_68_, v_val_70_, lean_box(0));
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_72_, lean_object* v_00_u03b2_x27_73_, lean_object* v_n_74_, lean_object* v_f_75_, lean_object* v_out_76_, lean_object* v_motive_77_, lean_object* v_____do__lift_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_78_, v_h__1_79_, v_h__2_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_82_, lean_object* v_00_u03b2_x27_83_, lean_object* v_n_84_, lean_object* v_f_85_, lean_object* v_out_86_, lean_object* v_motive_87_, lean_object* v_____do__lift_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_82_, v_00_u03b2_x27_83_, v_n_84_, v_f_85_, v_out_86_, v_motive_87_, v_____do__lift_88_, v_h__1_89_, v_h__2_90_);
lean_dec(v_out_86_);
lean_dec(v_f_85_);
return v_res_91_;
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
