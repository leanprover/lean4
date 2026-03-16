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
lean_object* v___x_16_; 
v___x_16_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___redArg(v_____do__lift_13_, v_h__1_14_, v_h__2_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter___boxed(lean_object* v_00_u03b2_17_, lean_object* v_00_u03b3_18_, lean_object* v_n_19_, lean_object* v_f_20_, lean_object* v_out_21_, lean_object* v_motive_22_, lean_object* v_____do__lift_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instIterator_match__1_splitter(v_00_u03b2_17_, v_00_u03b3_18_, v_n_19_, v_f_20_, v_out_21_, v_motive_22_, v_____do__lift_23_, v_h__1_24_, v_h__2_25_);
lean_dec(v_out_21_);
lean_dec(v_f_20_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_____do__lift_27_) == 0)
{
lean_object* v___x_30_; 
lean_dec(v_h__2_29_);
v___x_30_ = lean_apply_1(v_h__1_28_, lean_box(0));
return v___x_30_;
}
else
{
lean_object* v_val_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_28_);
v_val_31_ = lean_ctor_get(v_____do__lift_27_, 0);
lean_inc(v_val_31_);
lean_dec_ref(v_____do__lift_27_);
v___x_32_ = lean_apply_2(v_h__2_29_, v_val_31_, lean_box(0));
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_33_, lean_object* v_00_u03b2_x27_34_, lean_object* v_n_35_, lean_object* v_f_36_, lean_object* v_out_37_, lean_object* v_motive_38_, lean_object* v_____do__lift_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_39_, v_h__1_40_, v_h__2_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_43_, lean_object* v_00_u03b2_x27_44_, lean_object* v_n_45_, lean_object* v_f_46_, lean_object* v_out_47_, lean_object* v_motive_48_, lean_object* v_____do__lift_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_43_, v_00_u03b2_x27_44_, v_n_45_, v_f_46_, v_out_47_, v_motive_48_, v_____do__lift_49_, v_h__1_50_, v_h__2_51_);
lean_dec(v_out_47_);
lean_dec(v_f_46_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
if (v_____do__lift_53_ == 0)
{
lean_object* v___x_56_; 
lean_dec(v_h__2_55_);
v___x_56_ = lean_apply_1(v_h__1_54_, lean_box(0));
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
lean_dec(v_h__1_54_);
v___x_57_ = lean_apply_1(v_h__2_55_, lean_box(0));
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
uint8_t v_____do__lift_70__boxed_61_; lean_object* v_res_62_; 
v_____do__lift_70__boxed_61_ = lean_unbox(v_____do__lift_58_);
v_res_62_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_70__boxed_61_, v_h__1_59_, v_h__2_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_63_, lean_object* v_n_64_, lean_object* v_f_65_, lean_object* v_out_66_, lean_object* v_motive_67_, uint8_t v_____do__lift_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_68_, v_h__1_69_, v_h__2_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_72_, lean_object* v_n_73_, lean_object* v_f_74_, lean_object* v_out_75_, lean_object* v_motive_76_, lean_object* v_____do__lift_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
uint8_t v_____do__lift_77__boxed_80_; lean_object* v_res_81_; 
v_____do__lift_77__boxed_80_ = lean_unbox(v_____do__lift_77_);
v_res_81_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_72_, v_n_73_, v_f_74_, v_out_75_, v_motive_76_, v_____do__lift_77__boxed_80_, v_h__1_78_, v_h__2_79_);
lean_dec(v_out_75_);
lean_dec(v_f_74_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
if (v_____do__lift_82_ == 0)
{
lean_object* v___x_85_; 
lean_dec(v_h__2_84_);
v___x_85_ = lean_apply_1(v_h__1_83_, lean_box(0));
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
lean_dec(v_h__1_83_);
v___x_86_ = lean_apply_1(v_h__2_84_, lean_box(0));
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_){
_start:
{
uint8_t v_____do__lift_72__boxed_90_; lean_object* v_res_91_; 
v_____do__lift_72__boxed_90_ = lean_unbox(v_____do__lift_87_);
v_res_91_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_72__boxed_90_, v_h__1_88_, v_h__2_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object* v_00_u03b2_92_, lean_object* v_n_93_, lean_object* v_f_94_, lean_object* v_inst_95_, lean_object* v_out_96_, lean_object* v_motive_97_, uint8_t v_____do__lift_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_98_, v_h__1_99_, v_h__2_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_102_, lean_object* v_n_103_, lean_object* v_f_104_, lean_object* v_inst_105_, lean_object* v_out_106_, lean_object* v_motive_107_, lean_object* v_____do__lift_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_){
_start:
{
uint8_t v_____do__lift_80__boxed_111_; lean_object* v_res_112_; 
v_____do__lift_80__boxed_111_ = lean_unbox(v_____do__lift_108_);
v_res_112_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_102_, v_n_103_, v_f_104_, v_inst_105_, v_out_106_, v_motive_107_, v_____do__lift_80__boxed_111_, v_h__1_109_, v_h__2_110_);
lean_dec(v_out_106_);
lean_dec(v_inst_105_);
lean_dec(v_f_104_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_, lean_object* v_h__3_116_){
_start:
{
switch(lean_obj_tag(v_x_113_))
{
case 0:
{
lean_object* v_it_117_; lean_object* v_out_118_; lean_object* v___x_119_; 
lean_dec(v_h__3_116_);
lean_dec(v_h__2_115_);
v_it_117_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_it_117_);
v_out_118_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_out_118_);
lean_dec_ref(v_x_113_);
v___x_119_ = lean_apply_3(v_h__1_114_, v_it_117_, v_out_118_, lean_box(0));
return v___x_119_;
}
case 1:
{
lean_object* v_it_120_; lean_object* v___x_121_; 
lean_dec(v_h__3_116_);
lean_dec(v_h__1_114_);
v_it_120_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_it_120_);
lean_dec_ref(v_x_113_);
v___x_121_ = lean_apply_2(v_h__2_115_, v_it_120_, lean_box(0));
return v___x_121_;
}
default: 
{
lean_object* v___x_122_; 
lean_dec(v_h__2_115_);
lean_dec(v_h__1_114_);
v___x_122_ = lean_apply_1(v_h__3_116_, lean_box(0));
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_it_127_, lean_object* v_motive_128_, lean_object* v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_, lean_object* v_h__3_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(v_x_129_, v_h__1_130_, v_h__2_131_, v_h__3_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_m_136_, lean_object* v_inst_137_, lean_object* v_it_138_, lean_object* v_motive_139_, lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_, lean_object* v_h__3_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_134_, v_00_u03b2_135_, v_m_136_, v_inst_137_, v_it_138_, v_motive_139_, v_x_140_, v_h__1_141_, v_h__2_142_, v_h__3_143_);
lean_dec(v_it_138_);
lean_dec(v_inst_137_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_148_; 
lean_dec(v_h__2_147_);
v___x_148_ = lean_apply_1(v_h__1_146_, lean_box(0));
return v___x_148_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_146_);
v_val_149_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_149_);
lean_dec_ref(v_x_145_);
v___x_150_ = lean_apply_2(v_h__2_147_, v_val_149_, lean_box(0));
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object* v_00_u03b2_x27_151_, lean_object* v_motive_152_, lean_object* v_x_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(v_x_153_, v_h__1_154_, v_h__2_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_, lean_object* v_h__3_160_){
_start:
{
switch(lean_obj_tag(v_x_157_))
{
case 0:
{
lean_object* v_it_161_; lean_object* v_out_162_; lean_object* v___x_163_; 
lean_dec(v_h__3_160_);
lean_dec(v_h__2_159_);
v_it_161_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_it_161_);
v_out_162_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_out_162_);
lean_dec_ref(v_x_157_);
v___x_163_ = lean_apply_2(v_h__1_158_, v_it_161_, v_out_162_);
return v___x_163_;
}
case 1:
{
lean_object* v_it_164_; lean_object* v___x_165_; 
lean_dec(v_h__3_160_);
lean_dec(v_h__1_158_);
v_it_164_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_it_164_);
lean_dec_ref(v_x_157_);
v___x_165_ = lean_apply_1(v_h__2_159_, v_it_164_);
return v___x_165_;
}
default: 
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_159_);
lean_dec(v_h__1_158_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__3_160_, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_m_170_, lean_object* v_motive_171_, lean_object* v_x_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_, lean_object* v_h__3_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(v_x_172_, v_h__1_173_, v_h__2_174_, v_h__3_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_h__2_179_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_apply_1(v_h__1_178_, v___x_180_);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_183_; 
lean_dec(v_h__1_178_);
v_val_182_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_val_182_);
lean_dec_ref(v_x_177_);
v___x_183_ = lean_apply_1(v_h__2_179_, v_val_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_184_, lean_object* v_motive_185_, lean_object* v_x_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter___redArg(v_x_186_, v_h__1_187_, v_h__2_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27___redArg(lean_object* v_t_190_, lean_object* v_mk_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_apply_2(v_mk_191_, v_t_190_, lean_box(0));
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27(lean_object* v_00_u03b1_193_, lean_object* v_p_194_, lean_object* v_motive_195_, lean_object* v_t_196_, lean_object* v_mk_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_apply_2(v_mk_197_, v_t_196_, lean_box(0));
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(lean_object* v_t_199_, lean_object* v_n_200_, lean_object* v_s_201_){
_start:
{
if (lean_obj_tag(v_t_199_) == 0)
{
lean_object* v___x_202_; 
lean_dec(v_s_201_);
v___x_202_ = lean_apply_1(v_n_200_, lean_box(0));
return v___x_202_;
}
else
{
lean_object* v_val_203_; lean_object* v___x_204_; 
lean_dec(v_n_200_);
v_val_203_ = lean_ctor_get(v_t_199_, 0);
lean_inc(v_val_203_);
lean_dec_ref(v_t_199_);
v___x_204_ = lean_apply_2(v_s_201_, v_val_203_, lean_box(0));
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27(lean_object* v_00_u03b1_205_, lean_object* v_t_206_, lean_object* v_00_u03b2_207_, lean_object* v_n_208_, lean_object* v_s_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(v_t_206_, v_n_208_, v_s_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter___redArg(lean_object* v_t_211_, lean_object* v_n_212_, lean_object* v_s_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_){
_start:
{
if (lean_obj_tag(v_t_211_) == 0)
{
lean_object* v___x_216_; 
lean_dec(v_h__1_214_);
v___x_216_ = lean_apply_2(v_h__2_215_, v_n_212_, v_s_213_);
return v___x_216_;
}
else
{
lean_object* v_val_217_; lean_object* v___x_218_; 
lean_dec(v_h__2_215_);
v_val_217_ = lean_ctor_get(v_t_211_, 0);
lean_inc(v_val_217_);
lean_dec_ref(v_t_211_);
v___x_218_ = lean_apply_3(v_h__1_214_, v_val_217_, v_n_212_, v_s_213_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_n_223_, lean_object* v_s_224_, lean_object* v_h__1_225_, lean_object* v_h__2_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter___redArg(v_t_222_, v_n_223_, v_s_224_, v_h__1_225_, v_h__2_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_){
_start:
{
if (lean_obj_tag(v_____do__lift_228_) == 0)
{
lean_object* v___x_231_; 
lean_dec(v_h__2_230_);
v___x_231_ = lean_apply_1(v_h__1_229_, lean_box(0));
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_233_; 
lean_dec(v_h__1_229_);
v_val_232_ = lean_ctor_get(v_____do__lift_228_, 0);
lean_inc(v_val_232_);
lean_dec_ref(v_____do__lift_228_);
v___x_233_ = lean_apply_2(v_h__2_230_, v_val_232_, lean_box(0));
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_234_, lean_object* v_00_u03b2_x27_235_, lean_object* v_n_236_, lean_object* v_f_237_, lean_object* v_inst_238_, lean_object* v_out_239_, lean_object* v_motive_240_, lean_object* v_____do__lift_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(v_____do__lift_241_, v_h__1_242_, v_h__2_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_245_, lean_object* v_00_u03b2_x27_246_, lean_object* v_n_247_, lean_object* v_f_248_, lean_object* v_inst_249_, lean_object* v_out_250_, lean_object* v_motive_251_, lean_object* v_____do__lift_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_245_, v_00_u03b2_x27_246_, v_n_247_, v_f_248_, v_inst_249_, v_out_250_, v_motive_251_, v_____do__lift_252_, v_h__1_253_, v_h__2_254_);
lean_dec(v_out_250_);
lean_dec(v_inst_249_);
lean_dec(v_f_248_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter___redArg(lean_object* v_____do__lift_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
if (lean_obj_tag(v_____do__lift_256_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_h__2_258_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_apply_1(v_h__1_257_, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v_val_261_; lean_object* v___x_262_; 
lean_dec(v_h__1_257_);
v_val_261_ = lean_ctor_get(v_____do__lift_256_, 0);
lean_inc(v_val_261_);
lean_dec_ref(v_____do__lift_256_);
v___x_262_ = lean_apply_1(v_h__2_258_, v_val_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter(lean_object* v_00_u03b3_263_, lean_object* v_motive_264_, lean_object* v_____do__lift_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter___redArg(v_____do__lift_265_, v_h__1_266_, v_h__2_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
if (lean_obj_tag(v_____do__lift_269_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_h__2_271_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_apply_1(v_h__1_270_, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v_val_274_; lean_object* v___x_275_; 
lean_dec(v_h__1_270_);
v_val_274_ = lean_ctor_get(v_____do__lift_269_, 0);
lean_inc(v_val_274_);
lean_dec_ref(v_____do__lift_269_);
v___x_275_ = lean_apply_1(v_h__2_271_, v_val_274_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_276_, lean_object* v_motive_277_, lean_object* v_____do__lift_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_278_, v_h__1_279_, v_h__2_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object* v_____do__lift_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter(lean_object* v_00_u03b2_289_, lean_object* v_motive_290_, lean_object* v_____do__lift_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter___redArg(v_____do__lift_291_, v_h__1_292_, v_h__2_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_){
_start:
{
if (lean_obj_tag(v_____do__lift_295_) == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_h__1_296_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_1(v_h__2_297_, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v_val_300_; lean_object* v___x_301_; 
lean_dec(v_h__2_297_);
v_val_300_ = lean_ctor_get(v_____do__lift_295_, 0);
lean_inc(v_val_300_);
lean_dec_ref(v_____do__lift_295_);
v___x_301_ = lean_apply_1(v_h__1_296_, v_val_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_302_, lean_object* v_motive_303_, lean_object* v_____do__lift_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_304_, v_h__1_305_, v_h__2_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_, lean_object* v_h__3_311_){
_start:
{
switch(lean_obj_tag(v_x_308_))
{
case 0:
{
lean_object* v_it_312_; lean_object* v_out_313_; lean_object* v___x_314_; 
lean_dec(v_h__3_311_);
lean_dec(v_h__2_310_);
v_it_312_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_it_312_);
v_out_313_ = lean_ctor_get(v_x_308_, 1);
lean_inc(v_out_313_);
lean_dec_ref(v_x_308_);
v___x_314_ = lean_apply_3(v_h__1_309_, v_it_312_, v_out_313_, lean_box(0));
return v___x_314_;
}
case 1:
{
lean_object* v_it_315_; lean_object* v___x_316_; 
lean_dec(v_h__3_311_);
lean_dec(v_h__1_309_);
v_it_315_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_it_315_);
lean_dec_ref(v_x_308_);
v___x_316_ = lean_apply_2(v_h__2_310_, v_it_315_, lean_box(0));
return v___x_316_;
}
default: 
{
lean_object* v___x_317_; 
lean_dec(v_h__2_310_);
lean_dec(v_h__1_309_);
v___x_317_ = lean_apply_1(v_h__3_311_, lean_box(0));
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_inst_321_, lean_object* v_it_322_, lean_object* v_motive_323_, lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_, lean_object* v_h__3_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(v_x_324_, v_h__1_325_, v_h__2_326_, v_h__3_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_m_331_, lean_object* v_inst_332_, lean_object* v_it_333_, lean_object* v_motive_334_, lean_object* v_x_335_, lean_object* v_h__1_336_, lean_object* v_h__2_337_, lean_object* v_h__3_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_329_, v_00_u03b2_330_, v_m_331_, v_inst_332_, v_it_333_, v_motive_334_, v_x_335_, v_h__1_336_, v_h__2_337_, v_h__3_338_);
lean_dec(v_it_333_);
lean_dec(v_inst_332_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_340_, lean_object* v_h__1_341_, lean_object* v_h__2_342_){
_start:
{
if (lean_obj_tag(v_____do__lift_340_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; 
lean_dec(v_h__1_341_);
v_a_343_ = lean_ctor_get(v_____do__lift_340_, 0);
lean_inc(v_a_343_);
lean_dec_ref(v_____do__lift_340_);
v___x_344_ = lean_apply_1(v_h__2_342_, v_a_343_);
return v___x_344_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_346_; 
lean_dec(v_h__2_342_);
v_a_345_ = lean_ctor_get(v_____do__lift_340_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v_____do__lift_340_);
v___x_346_ = lean_apply_1(v_h__1_341_, v_a_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_347_, lean_object* v_motive_348_, lean_object* v_____do__lift_349_, lean_object* v_h__1_350_, lean_object* v_h__2_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(v_____do__lift_349_, v_h__1_350_, v_h__2_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_353_, lean_object* v_h__1_354_, lean_object* v_h__2_355_){
_start:
{
if (lean_obj_tag(v_____x_353_) == 1)
{
lean_object* v_val_356_; lean_object* v___x_357_; 
lean_dec(v_h__2_355_);
v_val_356_ = lean_ctor_get(v_____x_353_, 0);
lean_inc(v_val_356_);
lean_dec_ref(v_____x_353_);
v___x_357_ = lean_apply_1(v_h__1_354_, v_val_356_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
lean_dec(v_h__1_354_);
v___x_358_ = lean_apply_2(v_h__2_355_, v_____x_353_, lean_box(0));
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_359_, lean_object* v_motive_360_, lean_object* v_____x_361_, lean_object* v_h__1_362_, lean_object* v_h__2_363_){
_start:
{
if (lean_obj_tag(v_____x_361_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_365_; 
lean_dec(v_h__2_363_);
v_val_364_ = lean_ctor_get(v_____x_361_, 0);
lean_inc(v_val_364_);
lean_dec_ref(v_____x_361_);
v___x_365_ = lean_apply_1(v_h__1_362_, v_val_364_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
lean_dec(v_h__1_362_);
v___x_366_ = lean_apply_2(v_h__2_363_, v_____x_361_, lean_box(0));
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_, lean_object* v_h__3_370_){
_start:
{
switch(lean_obj_tag(v_x_367_))
{
case 0:
{
lean_object* v_it_371_; lean_object* v_out_372_; lean_object* v___x_373_; 
lean_dec(v_h__3_370_);
lean_dec(v_h__2_369_);
v_it_371_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_371_);
v_out_372_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_out_372_);
lean_dec_ref(v_x_367_);
v___x_373_ = lean_apply_2(v_h__1_368_, v_it_371_, v_out_372_);
return v___x_373_;
}
case 1:
{
lean_object* v_it_374_; lean_object* v___x_375_; 
lean_dec(v_h__3_370_);
lean_dec(v_h__1_368_);
v_it_374_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_374_);
lean_dec_ref(v_x_367_);
v___x_375_ = lean_apply_1(v_h__2_369_, v_it_374_);
return v___x_375_;
}
default: 
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_h__2_369_);
lean_dec(v_h__1_368_);
v___x_376_ = lean_box(0);
v___x_377_ = lean_apply_1(v_h__3_370_, v___x_376_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_m_380_, lean_object* v_motive_381_, lean_object* v_x_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_, lean_object* v_h__3_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(v_x_382_, v_h__1_383_, v_h__2_384_, v_h__3_385_);
return v___x_386_;
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
