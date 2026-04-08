// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
// Imports: public import Init.Data.Iterators.Combinators.Monadic.FilterMap import all Init.Data.Iterators.Consumers.Monadic.Collect import Init.Data.Array.Monadic public import Init.Data.Iterators.Consumers.Monadic.Collect public import Init.Data.List.Control import Init.Data.Bool import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop import Init.Data.Iterators.Lemmas.Monadic.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___redArg(lean_object* v_____do__lift_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_____do__lift_1_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_4_;
}
else
{
lean_object* v_val_5_; lean_object* v___x_6_; 
lean_dec(v_h__1_2_);
v_val_5_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v_____do__lift_1_);
v___x_6_ = lean_apply_2(v_h__2_3_, v_val_5_, lean_box(0));
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(lean_object* v_00_u03b2_7_, lean_object* v_00_u03b3_8_, lean_object* v_n_9_, lean_object* v_f_10_, lean_object* v_out_11_, lean_object* v_motive_12_, lean_object* v_____do__lift_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_){
_start:
{
if (lean_obj_tag(v_____do__lift_13_) == 0)
{
lean_object* v___x_16_; 
lean_dec(v_h__2_15_);
v___x_16_ = lean_apply_1(v_h__1_14_, lean_box(0));
return v___x_16_;
}
else
{
lean_object* v_val_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_14_);
v_val_17_ = lean_ctor_get(v_____do__lift_13_, 0);
lean_inc(v_val_17_);
lean_dec_ref(v_____do__lift_13_);
v___x_18_ = lean_apply_2(v_h__2_15_, v_val_17_, lean_box(0));
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___boxed(lean_object* v_00_u03b2_19_, lean_object* v_00_u03b3_20_, lean_object* v_n_21_, lean_object* v_f_22_, lean_object* v_out_23_, lean_object* v_motive_24_, lean_object* v_____do__lift_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(v_00_u03b2_19_, v_00_u03b3_20_, v_n_21_, v_f_22_, v_out_23_, v_motive_24_, v_____do__lift_25_, v_h__1_26_, v_h__2_27_);
lean_dec(v_out_23_);
lean_dec(v_f_22_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
if (lean_obj_tag(v_____do__lift_29_) == 0)
{
lean_object* v___x_32_; 
lean_dec(v_h__2_31_);
v___x_32_ = lean_apply_1(v_h__1_30_, lean_box(0));
return v___x_32_;
}
else
{
lean_object* v_val_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_30_);
v_val_33_ = lean_ctor_get(v_____do__lift_29_, 0);
lean_inc(v_val_33_);
lean_dec_ref(v_____do__lift_29_);
v___x_34_ = lean_apply_2(v_h__2_31_, v_val_33_, lean_box(0));
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_35_, lean_object* v_00_u03b2_x27_36_, lean_object* v_n_37_, lean_object* v_f_38_, lean_object* v_out_39_, lean_object* v_motive_40_, lean_object* v_____do__lift_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
if (lean_obj_tag(v_____do__lift_41_) == 0)
{
lean_object* v___x_44_; 
lean_dec(v_h__2_43_);
v___x_44_ = lean_apply_1(v_h__1_42_, lean_box(0));
return v___x_44_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_42_);
v_val_45_ = lean_ctor_get(v_____do__lift_41_, 0);
lean_inc(v_val_45_);
lean_dec_ref(v_____do__lift_41_);
v___x_46_ = lean_apply_2(v_h__2_43_, v_val_45_, lean_box(0));
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_47_, lean_object* v_00_u03b2_x27_48_, lean_object* v_n_49_, lean_object* v_f_50_, lean_object* v_out_51_, lean_object* v_motive_52_, lean_object* v_____do__lift_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_47_, v_00_u03b2_x27_48_, v_n_49_, v_f_50_, v_out_51_, v_motive_52_, v_____do__lift_53_, v_h__1_54_, v_h__2_55_);
lean_dec(v_out_51_);
lean_dec(v_f_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
if (v_____do__lift_57_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_h__2_59_);
v___x_60_ = lean_apply_1(v_h__1_58_, lean_box(0));
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
lean_dec(v_h__1_58_);
v___x_61_ = lean_apply_1(v_h__2_59_, lean_box(0));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
uint8_t v_____do__lift_72__boxed_65_; lean_object* v_res_66_; 
v_____do__lift_72__boxed_65_ = lean_unbox(v_____do__lift_62_);
v_res_66_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_65_, v_h__1_63_, v_h__2_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_67_, lean_object* v_n_68_, lean_object* v_f_69_, lean_object* v_out_70_, lean_object* v_motive_71_, uint8_t v_____do__lift_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
if (v_____do__lift_72_ == 0)
{
lean_object* v___x_75_; 
lean_dec(v_h__2_74_);
v___x_75_ = lean_apply_1(v_h__1_73_, lean_box(0));
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
lean_dec(v_h__1_73_);
v___x_76_ = lean_apply_1(v_h__2_74_, lean_box(0));
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_77_, lean_object* v_n_78_, lean_object* v_f_79_, lean_object* v_out_80_, lean_object* v_motive_81_, lean_object* v_____do__lift_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
uint8_t v_____do__lift_79__boxed_85_; lean_object* v_res_86_; 
v_____do__lift_79__boxed_85_ = lean_unbox(v_____do__lift_82_);
v_res_86_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_77_, v_n_78_, v_f_79_, v_out_80_, v_motive_81_, v_____do__lift_79__boxed_85_, v_h__1_83_, v_h__2_84_);
lean_dec(v_out_80_);
lean_dec(v_f_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_){
_start:
{
if (v_____do__lift_87_ == 0)
{
lean_object* v___x_90_; 
lean_dec(v_h__2_89_);
v___x_90_ = lean_apply_1(v_h__1_88_, lean_box(0));
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_dec(v_h__1_88_);
v___x_91_ = lean_apply_1(v_h__2_89_, lean_box(0));
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
uint8_t v_____do__lift_74__boxed_95_; lean_object* v_res_96_; 
v_____do__lift_74__boxed_95_ = lean_unbox(v_____do__lift_92_);
v_res_96_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_95_, v_h__1_93_, v_h__2_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object* v_00_u03b2_97_, lean_object* v_n_98_, lean_object* v_f_99_, lean_object* v_inst_100_, lean_object* v_out_101_, lean_object* v_motive_102_, uint8_t v_____do__lift_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_){
_start:
{
if (v_____do__lift_103_ == 0)
{
lean_object* v___x_106_; 
lean_dec(v_h__2_105_);
v___x_106_ = lean_apply_1(v_h__1_104_, lean_box(0));
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
lean_dec(v_h__1_104_);
v___x_107_ = lean_apply_1(v_h__2_105_, lean_box(0));
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_108_, lean_object* v_n_109_, lean_object* v_f_110_, lean_object* v_inst_111_, lean_object* v_out_112_, lean_object* v_motive_113_, lean_object* v_____do__lift_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
uint8_t v_____do__lift_82__boxed_117_; lean_object* v_res_118_; 
v_____do__lift_82__boxed_117_ = lean_unbox(v_____do__lift_114_);
v_res_118_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_108_, v_n_109_, v_f_110_, v_inst_111_, v_out_112_, v_motive_113_, v_____do__lift_82__boxed_117_, v_h__1_115_, v_h__2_116_);
lean_dec(v_out_112_);
lean_dec(v_inst_111_);
lean_dec(v_f_110_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_, lean_object* v_h__3_122_){
_start:
{
switch(lean_obj_tag(v_x_119_))
{
case 0:
{
lean_object* v_it_123_; lean_object* v_out_124_; lean_object* v___x_125_; 
lean_dec(v_h__3_122_);
lean_dec(v_h__2_121_);
v_it_123_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_it_123_);
v_out_124_ = lean_ctor_get(v_x_119_, 1);
lean_inc(v_out_124_);
lean_dec_ref(v_x_119_);
v___x_125_ = lean_apply_3(v_h__1_120_, v_it_123_, v_out_124_, lean_box(0));
return v___x_125_;
}
case 1:
{
lean_object* v_it_126_; lean_object* v___x_127_; 
lean_dec(v_h__3_122_);
lean_dec(v_h__1_120_);
v_it_126_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_it_126_);
lean_dec_ref(v_x_119_);
v___x_127_ = lean_apply_2(v_h__2_121_, v_it_126_, lean_box(0));
return v___x_127_;
}
default: 
{
lean_object* v___x_128_; 
lean_dec(v_h__2_121_);
lean_dec(v_h__1_120_);
v___x_128_ = lean_apply_1(v_h__3_122_, lean_box(0));
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_m_131_, lean_object* v_inst_132_, lean_object* v_it_133_, lean_object* v_motive_134_, lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_, lean_object* v_h__3_138_){
_start:
{
switch(lean_obj_tag(v_x_135_))
{
case 0:
{
lean_object* v_it_139_; lean_object* v_out_140_; lean_object* v___x_141_; 
lean_dec(v_h__3_138_);
lean_dec(v_h__2_137_);
v_it_139_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_it_139_);
v_out_140_ = lean_ctor_get(v_x_135_, 1);
lean_inc(v_out_140_);
lean_dec_ref(v_x_135_);
v___x_141_ = lean_apply_3(v_h__1_136_, v_it_139_, v_out_140_, lean_box(0));
return v___x_141_;
}
case 1:
{
lean_object* v_it_142_; lean_object* v___x_143_; 
lean_dec(v_h__3_138_);
lean_dec(v_h__1_136_);
v_it_142_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_it_142_);
lean_dec_ref(v_x_135_);
v___x_143_ = lean_apply_2(v_h__2_137_, v_it_142_, lean_box(0));
return v___x_143_;
}
default: 
{
lean_object* v___x_144_; 
lean_dec(v_h__2_137_);
lean_dec(v_h__1_136_);
v___x_144_ = lean_apply_1(v_h__3_138_, lean_box(0));
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_m_147_, lean_object* v_inst_148_, lean_object* v_it_149_, lean_object* v_motive_150_, lean_object* v_x_151_, lean_object* v_h__1_152_, lean_object* v_h__2_153_, lean_object* v_h__3_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_145_, v_00_u03b2_146_, v_m_147_, v_inst_148_, v_it_149_, v_motive_150_, v_x_151_, v_h__1_152_, v_h__2_153_, v_h__3_154_);
lean_dec(v_it_149_);
lean_dec(v_inst_148_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object* v_x_156_, lean_object* v_h__1_157_, lean_object* v_h__2_158_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_h__2_158_);
v___x_159_ = lean_apply_1(v_h__1_157_, lean_box(0));
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_161_; 
lean_dec(v_h__1_157_);
v_val_160_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_val_160_);
lean_dec_ref(v_x_156_);
v___x_161_ = lean_apply_2(v_h__2_158_, v_val_160_, lean_box(0));
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object* v_00_u03b2_x27_162_, lean_object* v_motive_163_, lean_object* v_x_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v___x_167_; 
lean_dec(v_h__2_166_);
v___x_167_ = lean_apply_1(v_h__1_165_, lean_box(0));
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_169_; 
lean_dec(v_h__1_165_);
v_val_168_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_val_168_);
lean_dec_ref(v_x_164_);
v___x_169_ = lean_apply_2(v_h__2_166_, v_val_168_, lean_box(0));
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_, lean_object* v_h__3_173_){
_start:
{
switch(lean_obj_tag(v_x_170_))
{
case 0:
{
lean_object* v_it_174_; lean_object* v_out_175_; lean_object* v___x_176_; 
lean_dec(v_h__3_173_);
lean_dec(v_h__2_172_);
v_it_174_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_it_174_);
v_out_175_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_out_175_);
lean_dec_ref(v_x_170_);
v___x_176_ = lean_apply_2(v_h__1_171_, v_it_174_, v_out_175_);
return v___x_176_;
}
case 1:
{
lean_object* v_it_177_; lean_object* v___x_178_; 
lean_dec(v_h__3_173_);
lean_dec(v_h__1_171_);
v_it_177_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_it_177_);
lean_dec_ref(v_x_170_);
v___x_178_ = lean_apply_1(v_h__2_172_, v_it_177_);
return v___x_178_;
}
default: 
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__2_172_);
lean_dec(v_h__1_171_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_apply_1(v_h__3_173_, v___x_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_181_, lean_object* v_00_u03b2_182_, lean_object* v_m_183_, lean_object* v_motive_184_, lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_, lean_object* v_h__3_188_){
_start:
{
switch(lean_obj_tag(v_x_185_))
{
case 0:
{
lean_object* v_it_189_; lean_object* v_out_190_; lean_object* v___x_191_; 
lean_dec(v_h__3_188_);
lean_dec(v_h__2_187_);
v_it_189_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_it_189_);
v_out_190_ = lean_ctor_get(v_x_185_, 1);
lean_inc(v_out_190_);
lean_dec_ref(v_x_185_);
v___x_191_ = lean_apply_2(v_h__1_186_, v_it_189_, v_out_190_);
return v___x_191_;
}
case 1:
{
lean_object* v_it_192_; lean_object* v___x_193_; 
lean_dec(v_h__3_188_);
lean_dec(v_h__1_186_);
v_it_192_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_it_192_);
lean_dec_ref(v_x_185_);
v___x_193_ = lean_apply_1(v_h__2_187_, v_it_192_);
return v___x_193_;
}
default: 
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_h__2_187_);
lean_dec(v_h__1_186_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_apply_1(v_h__3_188_, v___x_194_);
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__2_198_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_1(v_h__1_197_, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_202_; 
lean_dec(v_h__1_197_);
v_val_201_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_val_201_);
lean_dec_ref(v_x_196_);
v___x_202_ = lean_apply_1(v_h__2_198_, v_val_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_203_, lean_object* v_motive_204_, lean_object* v_x_205_, lean_object* v_h__1_206_, lean_object* v_h__2_207_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_h__2_207_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_apply_1(v_h__1_206_, v___x_208_);
return v___x_209_;
}
else
{
lean_object* v_val_210_; lean_object* v___x_211_; 
lean_dec(v_h__1_206_);
v_val_210_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_val_210_);
lean_dec_ref(v_x_205_);
v___x_211_ = lean_apply_1(v_h__2_207_, v_val_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27___redArg(lean_object* v_t_212_, lean_object* v_mk_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_apply_2(v_mk_213_, v_t_212_, lean_box(0));
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27(lean_object* v_00_u03b1_215_, lean_object* v_p_216_, lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_mk_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_apply_2(v_mk_219_, v_t_218_, lean_box(0));
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(lean_object* v_t_221_, lean_object* v_n_222_, lean_object* v_s_223_){
_start:
{
if (lean_obj_tag(v_t_221_) == 0)
{
lean_object* v___x_224_; 
lean_dec(v_s_223_);
v___x_224_ = lean_apply_1(v_n_222_, lean_box(0));
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; 
lean_dec(v_n_222_);
v_val_225_ = lean_ctor_get(v_t_221_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v_t_221_);
v___x_226_ = lean_apply_2(v_s_223_, v_val_225_, lean_box(0));
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27(lean_object* v_00_u03b1_227_, lean_object* v_t_228_, lean_object* v_00_u03b2_229_, lean_object* v_n_230_, lean_object* v_s_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(v_t_228_, v_n_230_, v_s_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter___redArg(lean_object* v_t_233_, lean_object* v_n_234_, lean_object* v_s_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
if (lean_obj_tag(v_t_233_) == 0)
{
lean_object* v___x_238_; 
lean_dec(v_h__1_236_);
v___x_238_ = lean_apply_2(v_h__2_237_, v_n_234_, v_s_235_);
return v___x_238_;
}
else
{
lean_object* v_val_239_; lean_object* v___x_240_; 
lean_dec(v_h__2_237_);
v_val_239_ = lean_ctor_get(v_t_233_, 0);
lean_inc(v_val_239_);
lean_dec_ref(v_t_233_);
v___x_240_ = lean_apply_3(v_h__1_236_, v_val_239_, v_n_234_, v_s_235_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_motive_243_, lean_object* v_t_244_, lean_object* v_n_245_, lean_object* v_s_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_){
_start:
{
if (lean_obj_tag(v_t_244_) == 0)
{
lean_object* v___x_249_; 
lean_dec(v_h__1_247_);
v___x_249_ = lean_apply_2(v_h__2_248_, v_n_245_, v_s_246_);
return v___x_249_;
}
else
{
lean_object* v_val_250_; lean_object* v___x_251_; 
lean_dec(v_h__2_248_);
v_val_250_ = lean_ctor_get(v_t_244_, 0);
lean_inc(v_val_250_);
lean_dec_ref(v_t_244_);
v___x_251_ = lean_apply_3(v_h__1_247_, v_val_250_, v_n_245_, v_s_246_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
if (lean_obj_tag(v_____do__lift_252_) == 0)
{
lean_object* v___x_255_; 
lean_dec(v_h__2_254_);
v___x_255_ = lean_apply_1(v_h__1_253_, lean_box(0));
return v___x_255_;
}
else
{
lean_object* v_val_256_; lean_object* v___x_257_; 
lean_dec(v_h__1_253_);
v_val_256_ = lean_ctor_get(v_____do__lift_252_, 0);
lean_inc(v_val_256_);
lean_dec_ref(v_____do__lift_252_);
v___x_257_ = lean_apply_2(v_h__2_254_, v_val_256_, lean_box(0));
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_258_, lean_object* v_00_u03b2_x27_259_, lean_object* v_n_260_, lean_object* v_f_261_, lean_object* v_inst_262_, lean_object* v_out_263_, lean_object* v_motive_264_, lean_object* v_____do__lift_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
if (lean_obj_tag(v_____do__lift_265_) == 0)
{
lean_object* v___x_268_; 
lean_dec(v_h__2_267_);
v___x_268_ = lean_apply_1(v_h__1_266_, lean_box(0));
return v___x_268_;
}
else
{
lean_object* v_val_269_; lean_object* v___x_270_; 
lean_dec(v_h__1_266_);
v_val_269_ = lean_ctor_get(v_____do__lift_265_, 0);
lean_inc(v_val_269_);
lean_dec_ref(v_____do__lift_265_);
v___x_270_ = lean_apply_2(v_h__2_267_, v_val_269_, lean_box(0));
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_271_, lean_object* v_00_u03b2_x27_272_, lean_object* v_n_273_, lean_object* v_f_274_, lean_object* v_inst_275_, lean_object* v_out_276_, lean_object* v_motive_277_, lean_object* v_____do__lift_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_271_, v_00_u03b2_x27_272_, v_n_273_, v_f_274_, v_inst_275_, v_out_276_, v_motive_277_, v_____do__lift_278_, v_h__1_279_, v_h__2_280_);
lean_dec(v_out_276_);
lean_dec(v_inst_275_);
lean_dec(v_f_274_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter___redArg(lean_object* v_____do__lift_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
if (lean_obj_tag(v_____do__lift_282_) == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_h__2_284_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_apply_1(v_h__1_283_, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v_val_287_; lean_object* v___x_288_; 
lean_dec(v_h__1_283_);
v_val_287_ = lean_ctor_get(v_____do__lift_282_, 0);
lean_inc(v_val_287_);
lean_dec_ref(v_____do__lift_282_);
v___x_288_ = lean_apply_1(v_h__2_284_, v_val_287_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter(lean_object* v_00_u03b3_289_, lean_object* v_motive_290_, lean_object* v_____do__lift_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
if (lean_obj_tag(v_____do__lift_291_) == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_h__2_293_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_apply_1(v_h__1_292_, v___x_294_);
return v___x_295_;
}
else
{
lean_object* v_val_296_; lean_object* v___x_297_; 
lean_dec(v_h__1_292_);
v_val_296_ = lean_ctor_get(v_____do__lift_291_, 0);
lean_inc(v_val_296_);
lean_dec_ref(v_____do__lift_291_);
v___x_297_ = lean_apply_1(v_h__2_293_, v_val_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_){
_start:
{
if (lean_obj_tag(v_____do__lift_298_) == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_h__2_300_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_apply_1(v_h__1_299_, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v_val_303_; lean_object* v___x_304_; 
lean_dec(v_h__1_299_);
v_val_303_ = lean_ctor_get(v_____do__lift_298_, 0);
lean_inc(v_val_303_);
lean_dec_ref(v_____do__lift_298_);
v___x_304_ = lean_apply_1(v_h__2_300_, v_val_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_305_, lean_object* v_motive_306_, lean_object* v_____do__lift_307_, lean_object* v_h__1_308_, lean_object* v_h__2_309_){
_start:
{
if (lean_obj_tag(v_____do__lift_307_) == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_h__2_309_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_apply_1(v_h__1_308_, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_val_312_; lean_object* v___x_313_; 
lean_dec(v_h__1_308_);
v_val_312_ = lean_ctor_get(v_____do__lift_307_, 0);
lean_inc(v_val_312_);
lean_dec_ref(v_____do__lift_307_);
v___x_313_ = lean_apply_1(v_h__2_309_, v_val_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object* v_____do__lift_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_){
_start:
{
if (lean_obj_tag(v_____do__lift_314_) == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_h__2_316_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_apply_1(v_h__1_315_, v___x_317_);
return v___x_318_;
}
else
{
lean_object* v_val_319_; lean_object* v___x_320_; 
lean_dec(v_h__1_315_);
v_val_319_ = lean_ctor_get(v_____do__lift_314_, 0);
lean_inc(v_val_319_);
lean_dec_ref(v_____do__lift_314_);
v___x_320_ = lean_apply_1(v_h__2_316_, v_val_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter(lean_object* v_00_u03b2_321_, lean_object* v_motive_322_, lean_object* v_____do__lift_323_, lean_object* v_h__1_324_, lean_object* v_h__2_325_){
_start:
{
if (lean_obj_tag(v_____do__lift_323_) == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v_h__2_325_);
v___x_326_ = lean_box(0);
v___x_327_ = lean_apply_1(v_h__1_324_, v___x_326_);
return v___x_327_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_329_; 
lean_dec(v_h__1_324_);
v_val_328_ = lean_ctor_get(v_____do__lift_323_, 0);
lean_inc(v_val_328_);
lean_dec_ref(v_____do__lift_323_);
v___x_329_ = lean_apply_1(v_h__2_325_, v_val_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_330_, lean_object* v_h__1_331_, lean_object* v_h__2_332_){
_start:
{
if (lean_obj_tag(v_____do__lift_330_) == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_h__1_331_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_1(v_h__2_332_, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v_val_335_; lean_object* v___x_336_; 
lean_dec(v_h__2_332_);
v_val_335_ = lean_ctor_get(v_____do__lift_330_, 0);
lean_inc(v_val_335_);
lean_dec_ref(v_____do__lift_330_);
v___x_336_ = lean_apply_1(v_h__1_331_, v_val_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_337_, lean_object* v_motive_338_, lean_object* v_____do__lift_339_, lean_object* v_h__1_340_, lean_object* v_h__2_341_){
_start:
{
if (lean_obj_tag(v_____do__lift_339_) == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_h__1_340_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_apply_1(v_h__2_341_, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v_val_344_; lean_object* v___x_345_; 
lean_dec(v_h__2_341_);
v_val_344_ = lean_ctor_get(v_____do__lift_339_, 0);
lean_inc(v_val_344_);
lean_dec_ref(v_____do__lift_339_);
v___x_345_ = lean_apply_1(v_h__1_340_, v_val_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_346_, lean_object* v_h__1_347_, lean_object* v_h__2_348_, lean_object* v_h__3_349_){
_start:
{
switch(lean_obj_tag(v_x_346_))
{
case 0:
{
lean_object* v_it_350_; lean_object* v_out_351_; lean_object* v___x_352_; 
lean_dec(v_h__3_349_);
lean_dec(v_h__2_348_);
v_it_350_ = lean_ctor_get(v_x_346_, 0);
lean_inc(v_it_350_);
v_out_351_ = lean_ctor_get(v_x_346_, 1);
lean_inc(v_out_351_);
lean_dec_ref(v_x_346_);
v___x_352_ = lean_apply_3(v_h__1_347_, v_it_350_, v_out_351_, lean_box(0));
return v___x_352_;
}
case 1:
{
lean_object* v_it_353_; lean_object* v___x_354_; 
lean_dec(v_h__3_349_);
lean_dec(v_h__1_347_);
v_it_353_ = lean_ctor_get(v_x_346_, 0);
lean_inc(v_it_353_);
lean_dec_ref(v_x_346_);
v___x_354_ = lean_apply_2(v_h__2_348_, v_it_353_, lean_box(0));
return v___x_354_;
}
default: 
{
lean_object* v___x_355_; 
lean_dec(v_h__2_348_);
lean_dec(v_h__1_347_);
v___x_355_ = lean_apply_1(v_h__3_349_, lean_box(0));
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_m_358_, lean_object* v_inst_359_, lean_object* v_it_360_, lean_object* v_motive_361_, lean_object* v_x_362_, lean_object* v_h__1_363_, lean_object* v_h__2_364_, lean_object* v_h__3_365_){
_start:
{
switch(lean_obj_tag(v_x_362_))
{
case 0:
{
lean_object* v_it_366_; lean_object* v_out_367_; lean_object* v___x_368_; 
lean_dec(v_h__3_365_);
lean_dec(v_h__2_364_);
v_it_366_ = lean_ctor_get(v_x_362_, 0);
lean_inc(v_it_366_);
v_out_367_ = lean_ctor_get(v_x_362_, 1);
lean_inc(v_out_367_);
lean_dec_ref(v_x_362_);
v___x_368_ = lean_apply_3(v_h__1_363_, v_it_366_, v_out_367_, lean_box(0));
return v___x_368_;
}
case 1:
{
lean_object* v_it_369_; lean_object* v___x_370_; 
lean_dec(v_h__3_365_);
lean_dec(v_h__1_363_);
v_it_369_ = lean_ctor_get(v_x_362_, 0);
lean_inc(v_it_369_);
lean_dec_ref(v_x_362_);
v___x_370_ = lean_apply_2(v_h__2_364_, v_it_369_, lean_box(0));
return v___x_370_;
}
default: 
{
lean_object* v___x_371_; 
lean_dec(v_h__2_364_);
lean_dec(v_h__1_363_);
v___x_371_ = lean_apply_1(v_h__3_365_, lean_box(0));
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_m_374_, lean_object* v_inst_375_, lean_object* v_it_376_, lean_object* v_motive_377_, lean_object* v_x_378_, lean_object* v_h__1_379_, lean_object* v_h__2_380_, lean_object* v_h__3_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_372_, v_00_u03b2_373_, v_m_374_, v_inst_375_, v_it_376_, v_motive_377_, v_x_378_, v_h__1_379_, v_h__2_380_, v_h__3_381_);
lean_dec(v_it_376_);
lean_dec(v_inst_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_383_, lean_object* v_h__1_384_, lean_object* v_h__2_385_){
_start:
{
if (lean_obj_tag(v_____do__lift_383_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; 
lean_dec(v_h__1_384_);
v_a_386_ = lean_ctor_get(v_____do__lift_383_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v_____do__lift_383_);
v___x_387_ = lean_apply_1(v_h__2_385_, v_a_386_);
return v___x_387_;
}
else
{
lean_object* v_a_388_; lean_object* v___x_389_; 
lean_dec(v_h__2_385_);
v_a_388_ = lean_ctor_get(v_____do__lift_383_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v_____do__lift_383_);
v___x_389_ = lean_apply_1(v_h__1_384_, v_a_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_390_, lean_object* v_motive_391_, lean_object* v_____do__lift_392_, lean_object* v_h__1_393_, lean_object* v_h__2_394_){
_start:
{
if (lean_obj_tag(v_____do__lift_392_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_396_; 
lean_dec(v_h__1_393_);
v_a_395_ = lean_ctor_get(v_____do__lift_392_, 0);
lean_inc(v_a_395_);
lean_dec_ref(v_____do__lift_392_);
v___x_396_ = lean_apply_1(v_h__2_394_, v_a_395_);
return v___x_396_;
}
else
{
lean_object* v_a_397_; lean_object* v___x_398_; 
lean_dec(v_h__2_394_);
v_a_397_ = lean_ctor_get(v_____do__lift_392_, 0);
lean_inc(v_a_397_);
lean_dec_ref(v_____do__lift_392_);
v___x_398_ = lean_apply_1(v_h__1_393_, v_a_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_399_, lean_object* v_h__1_400_, lean_object* v_h__2_401_){
_start:
{
if (lean_obj_tag(v_____x_399_) == 1)
{
lean_object* v_val_402_; lean_object* v___x_403_; 
lean_dec(v_h__2_401_);
v_val_402_ = lean_ctor_get(v_____x_399_, 0);
lean_inc(v_val_402_);
lean_dec_ref(v_____x_399_);
v___x_403_ = lean_apply_1(v_h__1_400_, v_val_402_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; 
lean_dec(v_h__1_400_);
v___x_404_ = lean_apply_2(v_h__2_401_, v_____x_399_, lean_box(0));
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_405_, lean_object* v_motive_406_, lean_object* v_____x_407_, lean_object* v_h__1_408_, lean_object* v_h__2_409_){
_start:
{
if (lean_obj_tag(v_____x_407_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_411_; 
lean_dec(v_h__2_409_);
v_val_410_ = lean_ctor_get(v_____x_407_, 0);
lean_inc(v_val_410_);
lean_dec_ref(v_____x_407_);
v___x_411_ = lean_apply_1(v_h__1_408_, v_val_410_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; 
lean_dec(v_h__1_408_);
v___x_412_ = lean_apply_2(v_h__2_409_, v_____x_407_, lean_box(0));
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_413_, lean_object* v_h__1_414_, lean_object* v_h__2_415_, lean_object* v_h__3_416_){
_start:
{
switch(lean_obj_tag(v_x_413_))
{
case 0:
{
lean_object* v_it_417_; lean_object* v_out_418_; lean_object* v___x_419_; 
lean_dec(v_h__3_416_);
lean_dec(v_h__2_415_);
v_it_417_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_it_417_);
v_out_418_ = lean_ctor_get(v_x_413_, 1);
lean_inc(v_out_418_);
lean_dec_ref(v_x_413_);
v___x_419_ = lean_apply_2(v_h__1_414_, v_it_417_, v_out_418_);
return v___x_419_;
}
case 1:
{
lean_object* v_it_420_; lean_object* v___x_421_; 
lean_dec(v_h__3_416_);
lean_dec(v_h__1_414_);
v_it_420_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_it_420_);
lean_dec_ref(v_x_413_);
v___x_421_ = lean_apply_1(v_h__2_415_, v_it_420_);
return v___x_421_;
}
default: 
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_h__2_415_);
lean_dec(v_h__1_414_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_apply_1(v_h__3_416_, v___x_422_);
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_, lean_object* v_m_426_, lean_object* v_motive_427_, lean_object* v_x_428_, lean_object* v_h__1_429_, lean_object* v_h__2_430_, lean_object* v_h__3_431_){
_start:
{
switch(lean_obj_tag(v_x_428_))
{
case 0:
{
lean_object* v_it_432_; lean_object* v_out_433_; lean_object* v___x_434_; 
lean_dec(v_h__3_431_);
lean_dec(v_h__2_430_);
v_it_432_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_it_432_);
v_out_433_ = lean_ctor_get(v_x_428_, 1);
lean_inc(v_out_433_);
lean_dec_ref(v_x_428_);
v___x_434_ = lean_apply_2(v_h__1_429_, v_it_432_, v_out_433_);
return v___x_434_;
}
case 1:
{
lean_object* v_it_435_; lean_object* v___x_436_; 
lean_dec(v_h__3_431_);
lean_dec(v_h__1_429_);
v_it_435_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_it_435_);
lean_dec_ref(v_x_428_);
v___x_436_ = lean_apply_1(v_h__2_430_, v_it_435_);
return v___x_436_;
}
default: 
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_h__2_430_);
lean_dec(v_h__1_429_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_apply_1(v_h__3_431_, v___x_437_);
return v___x_438_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
}
#ifdef __cplusplus
}
#endif
