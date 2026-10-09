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
lean_dec_ref_known(v_____do__lift_1_, 1);
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
lean_dec_ref_known(v_____do__lift_13_, 1);
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
lean_dec_ref_known(v_____do__lift_29_, 1);
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
lean_dec_ref_known(v_____do__lift_41_, 1);
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
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
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
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_57_ = stack[0].m_num;
lean_object* v_h__1_58_ = stack[1].m_obj;
lean_object* v_h__2_59_ = stack[2].m_obj;
lean_object* v_res_62_;
v_res_62_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_57_, v_h__1_58_, v_h__2_59_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
uint8_t v_____do__lift_23__boxed_66_; lean_object* v_res_67_; 
v_____do__lift_23__boxed_66_ = lean_unbox(v_____do__lift_63_);
v_res_67_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_23__boxed_66_, v_h__1_64_, v_h__2_65_);
return v_res_67_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_68_, lean_object* v_n_69_, lean_object* v_f_70_, lean_object* v_out_71_, lean_object* v_motive_72_, uint8_t v_____do__lift_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_){
_start:
{
if (v_____do__lift_73_ == 0)
{
lean_object* v___x_76_; 
lean_dec(v_h__2_75_);
v___x_76_ = lean_apply_1(v_h__1_74_, lean_box(0));
return v___x_76_;
}
else
{
lean_object* v___x_77_; 
lean_dec(v_h__1_74_);
v___x_77_ = lean_apply_1(v_h__2_75_, lean_box(0));
return v___x_77_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_70_ = stack[2].m_obj;
lean_object* v_out_71_ = stack[3].m_obj;
uint8_t v_____do__lift_73_ = stack[5].m_num;
lean_object* v_h__1_74_ = stack[6].m_obj;
lean_object* v_h__2_75_ = stack[7].m_obj;
lean_object* v_res_78_;
v_res_78_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_box(0), lean_box(0), v_f_70_, v_out_71_, lean_box(0), v_____do__lift_73_, v_h__1_74_, v_h__2_75_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_79_, lean_object* v_n_80_, lean_object* v_f_81_, lean_object* v_out_82_, lean_object* v_motive_83_, lean_object* v_____do__lift_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
uint8_t v_____do__lift_34__boxed_87_; lean_object* v_res_88_; 
v_____do__lift_34__boxed_87_ = lean_unbox(v_____do__lift_84_);
v_res_88_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_79_, v_n_80_, v_f_81_, v_out_82_, v_motive_83_, v_____do__lift_34__boxed_87_, v_h__1_85_, v_h__2_86_);
lean_dec(v_out_82_);
lean_dec(v_f_81_);
return v_res_88_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (v_____do__lift_89_ == 0)
{
lean_object* v___x_92_; 
lean_dec(v_h__2_91_);
v___x_92_ = lean_apply_1(v_h__1_90_, lean_box(0));
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
lean_dec(v_h__1_90_);
v___x_93_ = lean_apply_1(v_h__2_91_, lean_box(0));
return v___x_93_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_89_ = stack[0].m_num;
lean_object* v_h__1_90_ = stack[1].m_obj;
lean_object* v_h__2_91_ = stack[2].m_obj;
lean_object* v_res_94_;
v_res_94_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_89_, v_h__1_90_, v_h__2_91_);
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
uint8_t v_____do__lift_25__boxed_98_; lean_object* v_res_99_; 
v_____do__lift_25__boxed_98_ = lean_unbox(v_____do__lift_95_);
v_res_99_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_25__boxed_98_, v_h__1_96_, v_h__2_97_);
return v_res_99_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object* v_00_u03b2_100_, lean_object* v_n_101_, lean_object* v_f_102_, lean_object* v_inst_103_, lean_object* v_out_104_, lean_object* v_motive_105_, uint8_t v_____do__lift_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
if (v_____do__lift_106_ == 0)
{
lean_object* v___x_109_; 
lean_dec(v_h__2_108_);
v___x_109_ = lean_apply_1(v_h__1_107_, lean_box(0));
return v___x_109_;
}
else
{
lean_object* v___x_110_; 
lean_dec(v_h__1_107_);
v___x_110_ = lean_apply_1(v_h__2_108_, lean_box(0));
return v___x_110_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_102_ = stack[2].m_obj;
lean_object* v_inst_103_ = stack[3].m_obj;
lean_object* v_out_104_ = stack[4].m_obj;
uint8_t v_____do__lift_106_ = stack[6].m_num;
lean_object* v_h__1_107_ = stack[7].m_obj;
lean_object* v_h__2_108_ = stack[8].m_obj;
lean_object* v_res_111_;
v_res_111_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_box(0), lean_box(0), v_f_102_, v_inst_103_, v_out_104_, lean_box(0), v_____do__lift_106_, v_h__1_107_, v_h__2_108_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_112_, lean_object* v_n_113_, lean_object* v_f_114_, lean_object* v_inst_115_, lean_object* v_out_116_, lean_object* v_motive_117_, lean_object* v_____do__lift_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
uint8_t v_____do__lift_37__boxed_121_; lean_object* v_res_122_; 
v_____do__lift_37__boxed_121_ = lean_unbox(v_____do__lift_118_);
v_res_122_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_112_, v_n_113_, v_f_114_, v_inst_115_, v_out_116_, v_motive_117_, v_____do__lift_37__boxed_121_, v_h__1_119_, v_h__2_120_);
lean_dec(v_out_116_);
lean_dec(v_inst_115_);
lean_dec(v_f_114_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_, lean_object* v_h__3_126_){
_start:
{
switch(lean_obj_tag(v_x_123_))
{
case 0:
{
lean_object* v_it_127_; lean_object* v_out_128_; lean_object* v___x_129_; 
lean_dec(v_h__3_126_);
lean_dec(v_h__2_125_);
v_it_127_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_it_127_);
v_out_128_ = lean_ctor_get(v_x_123_, 1);
lean_inc(v_out_128_);
lean_dec_ref_known(v_x_123_, 2);
v___x_129_ = lean_apply_3(v_h__1_124_, v_it_127_, v_out_128_, lean_box(0));
return v___x_129_;
}
case 1:
{
lean_object* v_it_130_; lean_object* v___x_131_; 
lean_dec(v_h__3_126_);
lean_dec(v_h__1_124_);
v_it_130_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_it_130_);
lean_dec_ref_known(v_x_123_, 1);
v___x_131_ = lean_apply_2(v_h__2_125_, v_it_130_, lean_box(0));
return v___x_131_;
}
default: 
{
lean_object* v___x_132_; 
lean_dec(v_h__2_125_);
lean_dec(v_h__1_124_);
v___x_132_ = lean_apply_1(v_h__3_126_, lean_box(0));
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_m_135_, lean_object* v_inst_136_, lean_object* v_it_137_, lean_object* v_motive_138_, lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_, lean_object* v_h__3_142_){
_start:
{
switch(lean_obj_tag(v_x_139_))
{
case 0:
{
lean_object* v_it_143_; lean_object* v_out_144_; lean_object* v___x_145_; 
lean_dec(v_h__3_142_);
lean_dec(v_h__2_141_);
v_it_143_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_it_143_);
v_out_144_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_out_144_);
lean_dec_ref_known(v_x_139_, 2);
v___x_145_ = lean_apply_3(v_h__1_140_, v_it_143_, v_out_144_, lean_box(0));
return v___x_145_;
}
case 1:
{
lean_object* v_it_146_; lean_object* v___x_147_; 
lean_dec(v_h__3_142_);
lean_dec(v_h__1_140_);
v_it_146_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_it_146_);
lean_dec_ref_known(v_x_139_, 1);
v___x_147_ = lean_apply_2(v_h__2_141_, v_it_146_, lean_box(0));
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; 
lean_dec(v_h__2_141_);
lean_dec(v_h__1_140_);
v___x_148_ = lean_apply_1(v_h__3_142_, lean_box(0));
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_m_151_, lean_object* v_inst_152_, lean_object* v_it_153_, lean_object* v_motive_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_, lean_object* v_h__3_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_149_, v_00_u03b2_150_, v_m_151_, v_inst_152_, v_it_153_, v_motive_154_, v_x_155_, v_h__1_156_, v_h__2_157_, v_h__3_158_);
lean_dec(v_it_153_);
lean_dec(v_inst_152_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_163_; 
lean_dec(v_h__2_162_);
v___x_163_ = lean_apply_1(v_h__1_161_, lean_box(0));
return v___x_163_;
}
else
{
lean_object* v_val_164_; lean_object* v___x_165_; 
lean_dec(v_h__1_161_);
v_val_164_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v_x_160_, 1);
v___x_165_ = lean_apply_2(v_h__2_162_, v_val_164_, lean_box(0));
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object* v_00_u03b2_x27_166_, lean_object* v_motive_167_, lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v___x_171_; 
lean_dec(v_h__2_170_);
v___x_171_ = lean_apply_1(v_h__1_169_, lean_box(0));
return v___x_171_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_173_; 
lean_dec(v_h__1_169_);
v_val_172_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v_x_168_, 1);
v___x_173_ = lean_apply_2(v_h__2_170_, v_val_172_, lean_box(0));
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_, lean_object* v_h__3_177_){
_start:
{
switch(lean_obj_tag(v_x_174_))
{
case 0:
{
lean_object* v_it_178_; lean_object* v_out_179_; lean_object* v___x_180_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__2_176_);
v_it_178_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_it_178_);
v_out_179_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_out_179_);
lean_dec_ref_known(v_x_174_, 2);
v___x_180_ = lean_apply_2(v_h__1_175_, v_it_178_, v_out_179_);
return v___x_180_;
}
case 1:
{
lean_object* v_it_181_; lean_object* v___x_182_; 
lean_dec(v_h__3_177_);
lean_dec(v_h__1_175_);
v_it_181_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_it_181_);
lean_dec_ref_known(v_x_174_, 1);
v___x_182_ = lean_apply_1(v_h__2_176_, v_it_181_);
return v___x_182_;
}
default: 
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_176_);
lean_dec(v_h__1_175_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__3_177_, v___x_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_185_, lean_object* v_00_u03b2_186_, lean_object* v_m_187_, lean_object* v_motive_188_, lean_object* v_x_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_, lean_object* v_h__3_192_){
_start:
{
switch(lean_obj_tag(v_x_189_))
{
case 0:
{
lean_object* v_it_193_; lean_object* v_out_194_; lean_object* v___x_195_; 
lean_dec(v_h__3_192_);
lean_dec(v_h__2_191_);
v_it_193_ = lean_ctor_get(v_x_189_, 0);
lean_inc(v_it_193_);
v_out_194_ = lean_ctor_get(v_x_189_, 1);
lean_inc(v_out_194_);
lean_dec_ref_known(v_x_189_, 2);
v___x_195_ = lean_apply_2(v_h__1_190_, v_it_193_, v_out_194_);
return v___x_195_;
}
case 1:
{
lean_object* v_it_196_; lean_object* v___x_197_; 
lean_dec(v_h__3_192_);
lean_dec(v_h__1_190_);
v_it_196_ = lean_ctor_get(v_x_189_, 0);
lean_inc(v_it_196_);
lean_dec_ref_known(v_x_189_, 1);
v___x_197_ = lean_apply_1(v_h__2_191_, v_it_196_);
return v___x_197_;
}
default: 
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_h__2_191_);
lean_dec(v_h__1_190_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_1(v_h__3_192_, v___x_198_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__2_202_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_h__1_201_, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; 
lean_dec(v_h__1_201_);
v_val_205_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v_x_200_, 1);
v___x_206_ = lean_apply_1(v_h__2_202_, v_val_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_207_, lean_object* v_motive_208_, lean_object* v_x_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_h__2_211_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_1(v_h__1_210_, v___x_212_);
return v___x_213_;
}
else
{
lean_object* v_val_214_; lean_object* v___x_215_; 
lean_dec(v_h__1_210_);
v_val_214_ = lean_ctor_get(v_x_209_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v_x_209_, 1);
v___x_215_ = lean_apply_1(v_h__2_211_, v_val_214_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27___redArg(lean_object* v_t_216_, lean_object* v_mk_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_apply_2(v_mk_217_, v_t_216_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_subtypeCasesOn_x27(lean_object* v_00_u03b1_219_, lean_object* v_p_220_, lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_mk_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_apply_2(v_mk_223_, v_t_222_, lean_box(0));
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(lean_object* v_t_225_, lean_object* v_n_226_, lean_object* v_s_227_){
_start:
{
if (lean_obj_tag(v_t_225_) == 0)
{
lean_object* v___x_228_; 
lean_dec(v_s_227_);
v___x_228_ = lean_apply_1(v_n_226_, lean_box(0));
return v___x_228_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_230_; 
lean_dec(v_n_226_);
v_val_229_ = lean_ctor_get(v_t_225_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v_t_225_, 1);
v___x_230_ = lean_apply_2(v_s_227_, v_val_229_, lean_box(0));
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27(lean_object* v_00_u03b1_231_, lean_object* v_t_232_, lean_object* v_00_u03b2_233_, lean_object* v_n_234_, lean_object* v_s_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27___redArg(v_t_232_, v_n_234_, v_s_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter___redArg(lean_object* v_t_237_, lean_object* v_n_238_, lean_object* v_s_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_){
_start:
{
if (lean_obj_tag(v_t_237_) == 0)
{
lean_object* v___x_242_; 
lean_dec(v_h__1_240_);
v___x_242_ = lean_apply_2(v_h__2_241_, v_n_238_, v_s_239_);
return v___x_242_;
}
else
{
lean_object* v_val_243_; lean_object* v___x_244_; 
lean_dec(v_h__2_241_);
v_val_243_ = lean_ctor_get(v_t_237_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v_t_237_, 1);
v___x_244_ = lean_apply_3(v_h__1_240_, v_val_243_, v_n_238_, v_s_239_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_Internal_optionPelim_x27_match__1_splitter(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_motive_247_, lean_object* v_t_248_, lean_object* v_n_249_, lean_object* v_s_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_){
_start:
{
if (lean_obj_tag(v_t_248_) == 0)
{
lean_object* v___x_253_; 
lean_dec(v_h__1_251_);
v___x_253_ = lean_apply_2(v_h__2_252_, v_n_249_, v_s_250_);
return v___x_253_;
}
else
{
lean_object* v_val_254_; lean_object* v___x_255_; 
lean_dec(v_h__2_252_);
v_val_254_ = lean_ctor_get(v_t_248_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v_t_248_, 1);
v___x_255_ = lean_apply_3(v_h__1_251_, v_val_254_, v_n_249_, v_s_250_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
if (lean_obj_tag(v_____do__lift_256_) == 0)
{
lean_object* v___x_259_; 
lean_dec(v_h__2_258_);
v___x_259_ = lean_apply_1(v_h__1_257_, lean_box(0));
return v___x_259_;
}
else
{
lean_object* v_val_260_; lean_object* v___x_261_; 
lean_dec(v_h__1_257_);
v_val_260_ = lean_ctor_get(v_____do__lift_256_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v_____do__lift_256_, 1);
v___x_261_ = lean_apply_2(v_h__2_258_, v_val_260_, lean_box(0));
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_262_, lean_object* v_00_u03b2_x27_263_, lean_object* v_n_264_, lean_object* v_f_265_, lean_object* v_inst_266_, lean_object* v_out_267_, lean_object* v_motive_268_, lean_object* v_____do__lift_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
if (lean_obj_tag(v_____do__lift_269_) == 0)
{
lean_object* v___x_272_; 
lean_dec(v_h__2_271_);
v___x_272_ = lean_apply_1(v_h__1_270_, lean_box(0));
return v___x_272_;
}
else
{
lean_object* v_val_273_; lean_object* v___x_274_; 
lean_dec(v_h__1_270_);
v_val_273_ = lean_ctor_get(v_____do__lift_269_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v_____do__lift_269_, 1);
v___x_274_ = lean_apply_2(v_h__2_271_, v_val_273_, lean_box(0));
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_275_, lean_object* v_00_u03b2_x27_276_, lean_object* v_n_277_, lean_object* v_f_278_, lean_object* v_inst_279_, lean_object* v_out_280_, lean_object* v_motive_281_, lean_object* v_____do__lift_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_275_, v_00_u03b2_x27_276_, v_n_277_, v_f_278_, v_inst_279_, v_out_280_, v_motive_281_, v_____do__lift_282_, v_h__1_283_, v_h__2_284_);
lean_dec(v_out_280_);
lean_dec(v_inst_279_);
lean_dec(v_f_278_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter___redArg(lean_object* v_____do__lift_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
if (lean_obj_tag(v_____do__lift_286_) == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_h__2_288_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_h__1_287_, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; 
lean_dec(v_h__1_287_);
v_val_291_ = lean_ctor_get(v_____do__lift_286_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v_____do__lift_286_, 1);
v___x_292_ = lean_apply_1(v_h__2_288_, v_val_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_x27_match__1_splitter(lean_object* v_00_u03b3_293_, lean_object* v_motive_294_, lean_object* v_____do__lift_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_){
_start:
{
if (lean_obj_tag(v_____do__lift_295_) == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_h__2_297_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_1(v_h__1_296_, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v_val_300_; lean_object* v___x_301_; 
lean_dec(v_h__1_296_);
v_val_300_ = lean_ctor_get(v_____do__lift_295_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v_____do__lift_295_, 1);
v___x_301_ = lean_apply_1(v_h__2_297_, v_val_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_302_, lean_object* v_h__1_303_, lean_object* v_h__2_304_){
_start:
{
if (lean_obj_tag(v_____do__lift_302_) == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_h__2_304_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_1(v_h__1_303_, v___x_305_);
return v___x_306_;
}
else
{
lean_object* v_val_307_; lean_object* v___x_308_; 
lean_dec(v_h__1_303_);
v_val_307_ = lean_ctor_get(v_____do__lift_302_, 0);
lean_inc(v_val_307_);
lean_dec_ref_known(v_____do__lift_302_, 1);
v___x_308_ = lean_apply_1(v_h__2_304_, v_val_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_toList__filterMapWithPostcondition__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_309_, lean_object* v_motive_310_, lean_object* v_____do__lift_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
if (lean_obj_tag(v_____do__lift_311_) == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_h__2_313_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_apply_1(v_h__1_312_, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v_val_316_; lean_object* v___x_317_; 
lean_dec(v_h__1_312_);
v_val_316_ = lean_ctor_get(v_____do__lift_311_, 0);
lean_inc(v_val_316_);
lean_dec_ref_known(v_____do__lift_311_, 1);
v___x_317_ = lean_apply_1(v_h__2_313_, v_val_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter___redArg(lean_object* v_____do__lift_318_, lean_object* v_h__1_319_, lean_object* v_h__2_320_){
_start:
{
if (lean_obj_tag(v_____do__lift_318_) == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_h__2_320_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_apply_1(v_h__1_319_, v___x_321_);
return v___x_322_;
}
else
{
lean_object* v_val_323_; lean_object* v___x_324_; 
lean_dec(v_h__1_319_);
v_val_323_ = lean_ctor_get(v_____do__lift_318_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v_____do__lift_318_, 1);
v___x_324_ = lean_apply_1(v_h__2_320_, v_val_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__List_filterMapM__cons_match__1_splitter(lean_object* v_00_u03b2_325_, lean_object* v_motive_326_, lean_object* v_____do__lift_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
if (lean_obj_tag(v_____do__lift_327_) == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_h__2_329_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_1(v_h__1_328_, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_333_; 
lean_dec(v_h__1_328_);
v_val_332_ = lean_ctor_get(v_____do__lift_327_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_____do__lift_327_, 1);
v___x_333_ = lean_apply_1(v_h__2_329_, v_val_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_){
_start:
{
if (lean_obj_tag(v_____do__lift_334_) == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_h__1_335_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_1(v_h__2_336_, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v_val_339_; lean_object* v___x_340_; 
lean_dec(v_h__2_336_);
v_val_339_ = lean_ctor_get(v_____do__lift_334_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v_____do__lift_334_, 1);
v___x_340_ = lean_apply_1(v_h__1_335_, v_val_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_341_, lean_object* v_motive_342_, lean_object* v_____do__lift_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_){
_start:
{
if (lean_obj_tag(v_____do__lift_343_) == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_h__1_344_);
v___x_346_ = lean_box(0);
v___x_347_ = lean_apply_1(v_h__2_345_, v___x_346_);
return v___x_347_;
}
else
{
lean_object* v_val_348_; lean_object* v___x_349_; 
lean_dec(v_h__2_345_);
v_val_348_ = lean_ctor_get(v_____do__lift_343_, 0);
lean_inc(v_val_348_);
lean_dec_ref_known(v_____do__lift_343_, 1);
v___x_349_ = lean_apply_1(v_h__1_344_, v_val_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_350_, lean_object* v_h__1_351_, lean_object* v_h__2_352_, lean_object* v_h__3_353_){
_start:
{
switch(lean_obj_tag(v_x_350_))
{
case 0:
{
lean_object* v_it_354_; lean_object* v_out_355_; lean_object* v___x_356_; 
lean_dec(v_h__3_353_);
lean_dec(v_h__2_352_);
v_it_354_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_it_354_);
v_out_355_ = lean_ctor_get(v_x_350_, 1);
lean_inc(v_out_355_);
lean_dec_ref_known(v_x_350_, 2);
v___x_356_ = lean_apply_3(v_h__1_351_, v_it_354_, v_out_355_, lean_box(0));
return v___x_356_;
}
case 1:
{
lean_object* v_it_357_; lean_object* v___x_358_; 
lean_dec(v_h__3_353_);
lean_dec(v_h__1_351_);
v_it_357_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_it_357_);
lean_dec_ref_known(v_x_350_, 1);
v___x_358_ = lean_apply_2(v_h__2_352_, v_it_357_, lean_box(0));
return v___x_358_;
}
default: 
{
lean_object* v___x_359_; 
lean_dec(v_h__2_352_);
lean_dec(v_h__1_351_);
v___x_359_ = lean_apply_1(v_h__3_353_, lean_box(0));
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_m_362_, lean_object* v_inst_363_, lean_object* v_it_364_, lean_object* v_motive_365_, lean_object* v_x_366_, lean_object* v_h__1_367_, lean_object* v_h__2_368_, lean_object* v_h__3_369_){
_start:
{
switch(lean_obj_tag(v_x_366_))
{
case 0:
{
lean_object* v_it_370_; lean_object* v_out_371_; lean_object* v___x_372_; 
lean_dec(v_h__3_369_);
lean_dec(v_h__2_368_);
v_it_370_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_it_370_);
v_out_371_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_out_371_);
lean_dec_ref_known(v_x_366_, 2);
v___x_372_ = lean_apply_3(v_h__1_367_, v_it_370_, v_out_371_, lean_box(0));
return v___x_372_;
}
case 1:
{
lean_object* v_it_373_; lean_object* v___x_374_; 
lean_dec(v_h__3_369_);
lean_dec(v_h__1_367_);
v_it_373_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_it_373_);
lean_dec_ref_known(v_x_366_, 1);
v___x_374_ = lean_apply_2(v_h__2_368_, v_it_373_, lean_box(0));
return v___x_374_;
}
default: 
{
lean_object* v___x_375_; 
lean_dec(v_h__2_368_);
lean_dec(v_h__1_367_);
v___x_375_ = lean_apply_1(v_h__3_369_, lean_box(0));
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_m_378_, lean_object* v_inst_379_, lean_object* v_it_380_, lean_object* v_motive_381_, lean_object* v_x_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_, lean_object* v_h__3_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_376_, v_00_u03b2_377_, v_m_378_, v_inst_379_, v_it_380_, v_motive_381_, v_x_382_, v_h__1_383_, v_h__2_384_, v_h__3_385_);
lean_dec(v_it_380_);
lean_dec(v_inst_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_387_, lean_object* v_h__1_388_, lean_object* v_h__2_389_){
_start:
{
if (lean_obj_tag(v_____do__lift_387_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_391_; 
lean_dec(v_h__1_388_);
v_a_390_ = lean_ctor_get(v_____do__lift_387_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v_____do__lift_387_, 1);
v___x_391_ = lean_apply_1(v_h__2_389_, v_a_390_);
return v___x_391_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_393_; 
lean_dec(v_h__2_389_);
v_a_392_ = lean_ctor_get(v_____do__lift_387_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v_____do__lift_387_, 1);
v___x_393_ = lean_apply_1(v_h__1_388_, v_a_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_394_, lean_object* v_motive_395_, lean_object* v_____do__lift_396_, lean_object* v_h__1_397_, lean_object* v_h__2_398_){
_start:
{
if (lean_obj_tag(v_____do__lift_396_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; 
lean_dec(v_h__1_397_);
v_a_399_ = lean_ctor_get(v_____do__lift_396_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v_____do__lift_396_, 1);
v___x_400_ = lean_apply_1(v_h__2_398_, v_a_399_);
return v___x_400_;
}
else
{
lean_object* v_a_401_; lean_object* v___x_402_; 
lean_dec(v_h__2_398_);
v_a_401_ = lean_ctor_get(v_____do__lift_396_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v_____do__lift_396_, 1);
v___x_402_ = lean_apply_1(v_h__1_397_, v_a_401_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_403_, lean_object* v_h__1_404_, lean_object* v_h__2_405_){
_start:
{
if (lean_obj_tag(v_____x_403_) == 1)
{
lean_object* v_val_406_; lean_object* v___x_407_; 
lean_dec(v_h__2_405_);
v_val_406_ = lean_ctor_get(v_____x_403_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_____x_403_, 1);
v___x_407_ = lean_apply_1(v_h__1_404_, v_val_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; 
lean_dec(v_h__1_404_);
v___x_408_ = lean_apply_2(v_h__2_405_, v_____x_403_, lean_box(0));
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_409_, lean_object* v_motive_410_, lean_object* v_____x_411_, lean_object* v_h__1_412_, lean_object* v_h__2_413_){
_start:
{
if (lean_obj_tag(v_____x_411_) == 1)
{
lean_object* v_val_414_; lean_object* v___x_415_; 
lean_dec(v_h__2_413_);
v_val_414_ = lean_ctor_get(v_____x_411_, 0);
lean_inc(v_val_414_);
lean_dec_ref_known(v_____x_411_, 1);
v___x_415_ = lean_apply_1(v_h__1_412_, v_val_414_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
lean_dec(v_h__1_412_);
v___x_416_ = lean_apply_2(v_h__2_413_, v_____x_411_, lean_box(0));
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_, lean_object* v_h__3_420_){
_start:
{
switch(lean_obj_tag(v_x_417_))
{
case 0:
{
lean_object* v_it_421_; lean_object* v_out_422_; lean_object* v___x_423_; 
lean_dec(v_h__3_420_);
lean_dec(v_h__2_419_);
v_it_421_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_it_421_);
v_out_422_ = lean_ctor_get(v_x_417_, 1);
lean_inc(v_out_422_);
lean_dec_ref_known(v_x_417_, 2);
v___x_423_ = lean_apply_2(v_h__1_418_, v_it_421_, v_out_422_);
return v___x_423_;
}
case 1:
{
lean_object* v_it_424_; lean_object* v___x_425_; 
lean_dec(v_h__3_420_);
lean_dec(v_h__1_418_);
v_it_424_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_it_424_);
lean_dec_ref_known(v_x_417_, 1);
v___x_425_ = lean_apply_1(v_h__2_419_, v_it_424_);
return v___x_425_;
}
default: 
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_h__2_419_);
lean_dec(v_h__1_418_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_apply_1(v_h__3_420_, v___x_426_);
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_m_430_, lean_object* v_motive_431_, lean_object* v_x_432_, lean_object* v_h__1_433_, lean_object* v_h__2_434_, lean_object* v_h__3_435_){
_start:
{
switch(lean_obj_tag(v_x_432_))
{
case 0:
{
lean_object* v_it_436_; lean_object* v_out_437_; lean_object* v___x_438_; 
lean_dec(v_h__3_435_);
lean_dec(v_h__2_434_);
v_it_436_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_it_436_);
v_out_437_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_out_437_);
lean_dec_ref_known(v_x_432_, 2);
v___x_438_ = lean_apply_2(v_h__1_433_, v_it_436_, v_out_437_);
return v___x_438_;
}
case 1:
{
lean_object* v_it_439_; lean_object* v___x_440_; 
lean_dec(v_h__3_435_);
lean_dec(v_h__1_433_);
v_it_439_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_it_439_);
lean_dec_ref_known(v_x_432_, 1);
v___x_440_ = lean_apply_1(v_h__2_434_, v_it_439_);
return v___x_440_;
}
default: 
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_h__2_434_);
lean_dec(v_h__1_433_);
v___x_441_ = lean_box(0);
v___x_442_ = lean_apply_1(v_h__3_435_, v___x_441_);
return v___x_442_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
