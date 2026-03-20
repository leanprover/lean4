// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.FilterMap
// Imports: public import Init.Data.Iterators.Combinators.FilterMap public import Init.Data.Iterators.Consumers.Collect public import Init.Data.Iterators.Consumers.Loop public import Init.Data.List.Control import Init.Data.Array.Lemmas import Init.Data.Bool import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.Iterators.Lemmas.Consumers.Loop import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
v___x_7_ = lean_apply_3(v_h__1_2_, v_it_5_, v_out_6_, lean_box(0));
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
v___x_9_ = lean_apply_2(v_h__2_3_, v_it_8_, lean_box(0));
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_apply_1(v_h__3_4_, lean_box(0));
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_m_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_, v_h__3_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_m_24_, lean_object* v_inst_25_, lean_object* v_it_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_22_, v_00_u03b2_23_, v_m_24_, v_inst_25_, v_it_26_, v_motive_27_, v_x_28_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
lean_dec(v_it_26_);
lean_dec(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_____do__lift_33_) == 0)
{
lean_object* v___x_36_; 
lean_dec(v_h__2_35_);
v___x_36_ = lean_apply_1(v_h__1_34_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v_val_37_; lean_object* v___x_38_; 
lean_dec(v_h__1_34_);
v_val_37_ = lean_ctor_get(v_____do__lift_33_, 0);
lean_inc(v_val_37_);
lean_dec_ref(v_____do__lift_33_);
v___x_38_ = lean_apply_2(v_h__2_35_, v_val_37_, lean_box(0));
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_39_, lean_object* v_00_u03b2_x27_40_, lean_object* v_n_41_, lean_object* v_f_42_, lean_object* v_out_43_, lean_object* v_motive_44_, lean_object* v_____do__lift_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_45_, v_h__1_46_, v_h__2_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_49_, lean_object* v_00_u03b2_x27_50_, lean_object* v_n_51_, lean_object* v_f_52_, lean_object* v_out_53_, lean_object* v_motive_54_, lean_object* v_____do__lift_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_49_, v_00_u03b2_x27_50_, v_n_51_, v_f_52_, v_out_53_, v_motive_54_, v_____do__lift_55_, v_h__1_56_, v_h__2_57_);
lean_dec(v_out_53_);
lean_dec(v_f_52_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_, lean_object* v_h__3_62_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_inst_71_, lean_object* v_it_72_, lean_object* v_motive_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_, lean_object* v_h__3_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(v_x_74_, v_h__1_75_, v_h__2_76_, v_h__3_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_inst_81_, lean_object* v_it_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_79_, v_00_u03b2_80_, v_inst_81_, v_it_82_, v_motive_83_, v_x_84_, v_h__1_85_, v_h__2_86_, v_h__3_87_);
lean_dec(v_it_82_);
lean_dec(v_inst_81_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_____do__lift_89_) == 0)
{
lean_object* v___x_92_; 
lean_dec(v_h__2_91_);
v___x_92_ = lean_apply_1(v_h__1_90_, lean_box(0));
return v___x_92_;
}
else
{
lean_object* v_val_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_90_);
v_val_93_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc(v_val_93_);
lean_dec_ref(v_____do__lift_89_);
v___x_94_ = lean_apply_2(v_h__2_91_, v_val_93_, lean_box(0));
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_95_, lean_object* v_00_u03b3_96_, lean_object* v_n_97_, lean_object* v_f_98_, lean_object* v_out_99_, lean_object* v_motive_100_, lean_object* v_____do__lift_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_101_, v_h__1_102_, v_h__2_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_105_, lean_object* v_00_u03b3_106_, lean_object* v_n_107_, lean_object* v_f_108_, lean_object* v_out_109_, lean_object* v_motive_110_, lean_object* v_____do__lift_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_105_, v_00_u03b3_106_, v_n_107_, v_f_108_, v_out_109_, v_motive_110_, v_____do__lift_111_, v_h__1_112_, v_h__2_113_);
lean_dec(v_out_109_);
lean_dec(v_f_108_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (v_____do__lift_115_ == 0)
{
lean_object* v___x_118_; 
lean_dec(v_h__2_117_);
v___x_118_ = lean_apply_1(v_h__1_116_, lean_box(0));
return v___x_118_;
}
else
{
lean_object* v___x_119_; 
lean_dec(v_h__1_116_);
v___x_119_ = lean_apply_1(v_h__2_117_, lean_box(0));
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
uint8_t v_____do__lift_70__boxed_123_; lean_object* v_res_124_; 
v_____do__lift_70__boxed_123_ = lean_unbox(v_____do__lift_120_);
v_res_124_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_70__boxed_123_, v_h__1_121_, v_h__2_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_125_, lean_object* v_n_126_, lean_object* v_f_127_, lean_object* v_out_128_, lean_object* v_motive_129_, uint8_t v_____do__lift_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_130_, v_h__1_131_, v_h__2_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_134_, lean_object* v_n_135_, lean_object* v_f_136_, lean_object* v_out_137_, lean_object* v_motive_138_, lean_object* v_____do__lift_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
uint8_t v_____do__lift_77__boxed_142_; lean_object* v_res_143_; 
v_____do__lift_77__boxed_142_ = lean_unbox(v_____do__lift_139_);
v_res_143_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_134_, v_n_135_, v_f_136_, v_out_137_, v_motive_138_, v_____do__lift_77__boxed_142_, v_h__1_140_, v_h__2_141_);
lean_dec(v_out_137_);
lean_dec(v_f_136_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
if (v_____do__lift_144_ == 0)
{
lean_object* v___x_147_; 
lean_dec(v_h__2_146_);
v___x_147_ = lean_apply_1(v_h__1_145_, lean_box(0));
return v___x_147_;
}
else
{
lean_object* v___x_148_; 
lean_dec(v_h__1_145_);
v___x_148_ = lean_apply_1(v_h__2_146_, lean_box(0));
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
uint8_t v_____do__lift_70__boxed_152_; lean_object* v_res_153_; 
v_____do__lift_70__boxed_152_ = lean_unbox(v_____do__lift_149_);
v_res_153_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_70__boxed_152_, v_h__1_150_, v_h__2_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_154_, lean_object* v_n_155_, lean_object* v_f_156_, lean_object* v_out_157_, lean_object* v_motive_158_, uint8_t v_____do__lift_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_159_, v_h__1_160_, v_h__2_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_163_, lean_object* v_n_164_, lean_object* v_f_165_, lean_object* v_out_166_, lean_object* v_motive_167_, lean_object* v_____do__lift_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
uint8_t v_____do__lift_77__boxed_171_; lean_object* v_res_172_; 
v_____do__lift_77__boxed_171_ = lean_unbox(v_____do__lift_168_);
v_res_172_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_163_, v_n_164_, v_f_165_, v_out_166_, v_motive_167_, v_____do__lift_77__boxed_171_, v_h__1_169_, v_h__2_170_);
lean_dec(v_out_166_);
lean_dec(v_f_165_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
if (lean_obj_tag(v_____do__lift_173_) == 0)
{
lean_object* v___x_176_; 
lean_dec(v_h__2_175_);
v___x_176_ = lean_apply_1(v_h__1_174_, lean_box(0));
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_178_; 
lean_dec(v_h__1_174_);
v_val_177_ = lean_ctor_get(v_____do__lift_173_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v_____do__lift_173_);
v___x_178_ = lean_apply_2(v_h__2_175_, v_val_177_, lean_box(0));
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_179_, lean_object* v_00_u03b2_x27_180_, lean_object* v_n_181_, lean_object* v_f_182_, lean_object* v_inst_183_, lean_object* v_out_184_, lean_object* v_motive_185_, lean_object* v_____do__lift_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(v_____do__lift_186_, v_h__1_187_, v_h__2_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_190_, lean_object* v_00_u03b2_x27_191_, lean_object* v_n_192_, lean_object* v_f_193_, lean_object* v_inst_194_, lean_object* v_out_195_, lean_object* v_motive_196_, lean_object* v_____do__lift_197_, lean_object* v_h__1_198_, lean_object* v_h__2_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_190_, v_00_u03b2_x27_191_, v_n_192_, v_f_193_, v_inst_194_, v_out_195_, v_motive_196_, v_____do__lift_197_, v_h__1_198_, v_h__2_199_);
lean_dec(v_out_195_);
lean_dec(v_inst_194_);
lean_dec(v_f_193_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_201_, lean_object* v_h__1_202_, lean_object* v_h__2_203_){
_start:
{
if (lean_obj_tag(v_____do__lift_201_) == 0)
{
lean_object* v___x_204_; 
lean_dec(v_h__2_203_);
v___x_204_ = lean_apply_1(v_h__1_202_, lean_box(0));
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; 
lean_dec(v_h__1_202_);
v_val_205_ = lean_ctor_get(v_____do__lift_201_, 0);
lean_inc(v_val_205_);
lean_dec_ref(v_____do__lift_201_);
v___x_206_ = lean_apply_2(v_h__2_203_, v_val_205_, lean_box(0));
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_207_, lean_object* v_n_208_, lean_object* v_00_u03b2_x27_209_, lean_object* v_f_210_, lean_object* v_inst_211_, lean_object* v_out_212_, lean_object* v_motive_213_, lean_object* v_____do__lift_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(v_____do__lift_214_, v_h__1_215_, v_h__2_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_218_, lean_object* v_n_219_, lean_object* v_00_u03b2_x27_220_, lean_object* v_f_221_, lean_object* v_inst_222_, lean_object* v_out_223_, lean_object* v_motive_224_, lean_object* v_____do__lift_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(v_00_u03b2_218_, v_n_219_, v_00_u03b2_x27_220_, v_f_221_, v_inst_222_, v_out_223_, v_motive_224_, v_____do__lift_225_, v_h__1_226_, v_h__2_227_);
lean_dec(v_out_223_);
lean_dec(v_inst_222_);
lean_dec(v_f_221_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
_start:
{
if (v_____do__lift_229_ == 0)
{
lean_object* v___x_232_; 
lean_dec(v_h__2_231_);
v___x_232_ = lean_apply_1(v_h__1_230_, lean_box(0));
return v___x_232_;
}
else
{
lean_object* v___x_233_; 
lean_dec(v_h__1_230_);
v___x_233_ = lean_apply_1(v_h__2_231_, lean_box(0));
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_234_, lean_object* v_h__1_235_, lean_object* v_h__2_236_){
_start:
{
uint8_t v_____do__lift_72__boxed_237_; lean_object* v_res_238_; 
v_____do__lift_72__boxed_237_ = lean_unbox(v_____do__lift_234_);
v_res_238_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_72__boxed_237_, v_h__1_235_, v_h__2_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object* v_00_u03b2_239_, lean_object* v_n_240_, lean_object* v_f_241_, lean_object* v_inst_242_, lean_object* v_out_243_, lean_object* v_motive_244_, uint8_t v_____do__lift_245_, lean_object* v_h__1_246_, lean_object* v_h__2_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_245_, v_h__1_246_, v_h__2_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_249_, lean_object* v_n_250_, lean_object* v_f_251_, lean_object* v_inst_252_, lean_object* v_out_253_, lean_object* v_motive_254_, lean_object* v_____do__lift_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_){
_start:
{
uint8_t v_____do__lift_80__boxed_258_; lean_object* v_res_259_; 
v_____do__lift_80__boxed_258_ = lean_unbox(v_____do__lift_255_);
v_res_259_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_249_, v_n_250_, v_f_251_, v_inst_252_, v_out_253_, v_motive_254_, v_____do__lift_80__boxed_258_, v_h__1_256_, v_h__2_257_);
lean_dec(v_out_253_);
lean_dec(v_inst_252_);
lean_dec(v_f_251_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_260_, lean_object* v_h__1_261_, lean_object* v_h__2_262_){
_start:
{
if (v_____do__lift_260_ == 0)
{
lean_object* v___x_263_; 
lean_dec(v_h__2_262_);
v___x_263_ = lean_apply_1(v_h__1_261_, lean_box(0));
return v___x_263_;
}
else
{
lean_object* v___x_264_; 
lean_dec(v_h__1_261_);
v___x_264_ = lean_apply_1(v_h__2_262_, lean_box(0));
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
uint8_t v_____do__lift_72__boxed_268_; lean_object* v_res_269_; 
v_____do__lift_72__boxed_268_ = lean_unbox(v_____do__lift_265_);
v_res_269_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_72__boxed_268_, v_h__1_266_, v_h__2_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(lean_object* v_00_u03b2_270_, lean_object* v_n_271_, lean_object* v_f_272_, lean_object* v_inst_273_, lean_object* v_out_274_, lean_object* v_motive_275_, uint8_t v_____do__lift_276_, lean_object* v_h__1_277_, lean_object* v_h__2_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_276_, v_h__1_277_, v_h__2_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_280_, lean_object* v_n_281_, lean_object* v_f_282_, lean_object* v_inst_283_, lean_object* v_out_284_, lean_object* v_motive_285_, lean_object* v_____do__lift_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
uint8_t v_____do__lift_80__boxed_289_; lean_object* v_res_290_; 
v_____do__lift_80__boxed_289_ = lean_unbox(v_____do__lift_286_);
v_res_290_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(v_00_u03b2_280_, v_n_281_, v_f_282_, v_inst_283_, v_out_284_, v_motive_285_, v_____do__lift_80__boxed_289_, v_h__1_287_, v_h__2_288_);
lean_dec(v_out_284_);
lean_dec(v_inst_283_);
lean_dec(v_f_282_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object* v_x_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v___x_294_; 
lean_dec(v_h__2_293_);
v___x_294_ = lean_apply_1(v_h__1_292_, lean_box(0));
return v___x_294_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_296_; 
lean_dec(v_h__1_292_);
v_val_295_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_val_295_);
lean_dec_ref(v_x_291_);
v___x_296_ = lean_apply_2(v_h__2_293_, v_val_295_, lean_box(0));
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object* v_00_u03b2_x27_297_, lean_object* v_motive_298_, lean_object* v_x_299_, lean_object* v_h__1_300_, lean_object* v_h__2_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(v_x_299_, v_h__1_300_, v_h__2_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(lean_object* v_x_303_, lean_object* v_h__1_304_, lean_object* v_h__2_305_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v___x_306_; 
lean_dec(v_h__2_305_);
v___x_306_ = lean_apply_1(v_h__1_304_, lean_box(0));
return v___x_306_;
}
else
{
lean_object* v_val_307_; lean_object* v___x_308_; 
lean_dec(v_h__1_304_);
v_val_307_ = lean_ctor_get(v_x_303_, 0);
lean_inc(v_val_307_);
lean_dec_ref(v_x_303_);
v___x_308_ = lean_apply_2(v_h__2_305_, v_val_307_, lean_box(0));
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter(lean_object* v_00_u03b3_309_, lean_object* v_motive_310_, lean_object* v_x_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(v_x_311_, v_h__1_312_, v_h__2_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(lean_object* v_x_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_, lean_object* v_h__3_318_){
_start:
{
switch(lean_obj_tag(v_x_315_))
{
case 0:
{
lean_object* v_it_319_; lean_object* v_out_320_; lean_object* v___x_321_; 
lean_dec(v_h__3_318_);
lean_dec(v_h__2_317_);
v_it_319_ = lean_ctor_get(v_x_315_, 0);
lean_inc(v_it_319_);
v_out_320_ = lean_ctor_get(v_x_315_, 1);
lean_inc(v_out_320_);
lean_dec_ref(v_x_315_);
v___x_321_ = lean_apply_2(v_h__1_316_, v_it_319_, v_out_320_);
return v___x_321_;
}
case 1:
{
lean_object* v_it_322_; lean_object* v___x_323_; 
lean_dec(v_h__3_318_);
lean_dec(v_h__1_316_);
v_it_322_ = lean_ctor_get(v_x_315_, 0);
lean_inc(v_it_322_);
lean_dec_ref(v_x_315_);
v___x_323_ = lean_apply_1(v_h__2_317_, v_it_322_);
return v___x_323_;
}
default: 
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_h__2_317_);
lean_dec(v_h__1_316_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_apply_1(v_h__3_318_, v___x_324_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter(lean_object* v_00_u03b1_326_, lean_object* v_00_u03b2_327_, lean_object* v_motive_328_, lean_object* v_x_329_, lean_object* v_h__1_330_, lean_object* v_h__2_331_, lean_object* v_h__3_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(v_x_329_, v_h__1_330_, v_h__2_331_, v_h__3_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(lean_object* v_x_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_h__2_336_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_1(v_h__1_335_, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v_val_339_; lean_object* v___x_340_; 
lean_dec(v_h__1_335_);
v_val_339_ = lean_ctor_get(v_x_334_, 0);
lean_inc(v_val_339_);
lean_dec_ref(v_x_334_);
v___x_340_ = lean_apply_1(v_h__2_336_, v_val_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter(lean_object* v_00_u03b3_341_, lean_object* v_motive_342_, lean_object* v_x_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(v_x_343_, v_h__1_344_, v_h__2_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_347_, lean_object* v_h__1_348_, lean_object* v_h__2_349_){
_start:
{
if (lean_obj_tag(v_____do__lift_347_) == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_348_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_apply_1(v_h__2_349_, v___x_350_);
return v___x_351_;
}
else
{
lean_object* v_val_352_; lean_object* v___x_353_; 
lean_dec(v_h__2_349_);
v_val_352_ = lean_ctor_get(v_____do__lift_347_, 0);
lean_inc(v_val_352_);
lean_dec_ref(v_____do__lift_347_);
v___x_353_ = lean_apply_1(v_h__1_348_, v_val_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_354_, lean_object* v_motive_355_, lean_object* v_____do__lift_356_, lean_object* v_h__1_357_, lean_object* v_h__2_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_356_, v_h__1_357_, v_h__2_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_360_, lean_object* v_h__1_361_, lean_object* v_h__2_362_){
_start:
{
if (lean_obj_tag(v_____do__lift_360_) == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_h__1_361_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_1(v_h__2_362_, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_val_365_; lean_object* v___x_366_; 
lean_dec(v_h__2_362_);
v_val_365_ = lean_ctor_get(v_____do__lift_360_, 0);
lean_inc(v_val_365_);
lean_dec_ref(v_____do__lift_360_);
v___x_366_ = lean_apply_1(v_h__1_361_, v_val_365_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_367_, lean_object* v_motive_368_, lean_object* v_____do__lift_369_, lean_object* v_h__1_370_, lean_object* v_h__2_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(v_____do__lift_369_, v_h__1_370_, v_h__2_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_373_, lean_object* v_h__1_374_, lean_object* v_h__2_375_){
_start:
{
if (lean_obj_tag(v_____x_373_) == 1)
{
lean_object* v_val_376_; lean_object* v___x_377_; 
lean_dec(v_h__2_375_);
v_val_376_ = lean_ctor_get(v_____x_373_, 0);
lean_inc(v_val_376_);
lean_dec_ref(v_____x_373_);
v___x_377_ = lean_apply_1(v_h__1_374_, v_val_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
lean_dec(v_h__1_374_);
v___x_378_ = lean_apply_2(v_h__2_375_, v_____x_373_, lean_box(0));
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_379_, lean_object* v_motive_380_, lean_object* v_____x_381_, lean_object* v_h__1_382_, lean_object* v_h__2_383_){
_start:
{
if (lean_obj_tag(v_____x_381_) == 1)
{
lean_object* v_val_384_; lean_object* v___x_385_; 
lean_dec(v_h__2_383_);
v_val_384_ = lean_ctor_get(v_____x_381_, 0);
lean_inc(v_val_384_);
lean_dec_ref(v_____x_381_);
v___x_385_ = lean_apply_1(v_h__1_382_, v_val_384_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; 
lean_dec(v_h__1_382_);
v___x_386_ = lean_apply_2(v_h__2_383_, v_____x_381_, lean_box(0));
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_387_, lean_object* v_h__1_388_, lean_object* v_h__2_389_){
_start:
{
if (lean_obj_tag(v_____x_387_) == 1)
{
lean_object* v_val_390_; lean_object* v___x_391_; 
lean_dec(v_h__2_389_);
v_val_390_ = lean_ctor_get(v_____x_387_, 0);
lean_inc(v_val_390_);
lean_dec_ref(v_____x_387_);
v___x_391_ = lean_apply_1(v_h__1_388_, v_val_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
lean_dec(v_h__1_388_);
v___x_392_ = lean_apply_2(v_h__2_389_, v_____x_387_, lean_box(0));
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_393_, lean_object* v_motive_394_, lean_object* v_____x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_){
_start:
{
if (lean_obj_tag(v_____x_395_) == 1)
{
lean_object* v_val_398_; lean_object* v___x_399_; 
lean_dec(v_h__2_397_);
v_val_398_ = lean_ctor_get(v_____x_395_, 0);
lean_inc(v_val_398_);
lean_dec_ref(v_____x_395_);
v___x_399_ = lean_apply_1(v_h__1_396_, v_val_398_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; 
lean_dec(v_h__1_396_);
v___x_400_ = lean_apply_2(v_h__2_397_, v_____x_395_, lean_box(0));
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_401_, lean_object* v_h__1_402_, lean_object* v_h__2_403_){
_start:
{
if (lean_obj_tag(v_____do__lift_401_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; 
lean_dec(v_h__1_402_);
v_a_404_ = lean_ctor_get(v_____do__lift_401_, 0);
lean_inc(v_a_404_);
lean_dec_ref(v_____do__lift_401_);
v___x_405_ = lean_apply_1(v_h__2_403_, v_a_404_);
return v___x_405_;
}
else
{
lean_object* v_a_406_; lean_object* v___x_407_; 
lean_dec(v_h__2_403_);
v_a_406_ = lean_ctor_get(v_____do__lift_401_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v_____do__lift_401_);
v___x_407_ = lean_apply_1(v_h__1_402_, v_a_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_408_, lean_object* v_motive_409_, lean_object* v_____do__lift_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(v_____do__lift_410_, v_h__1_411_, v_h__2_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_414_, lean_object* v_h__1_415_, lean_object* v_h__2_416_, lean_object* v_h__3_417_){
_start:
{
switch(lean_obj_tag(v_x_414_))
{
case 0:
{
lean_object* v_it_418_; lean_object* v_out_419_; lean_object* v___x_420_; 
lean_dec(v_h__3_417_);
lean_dec(v_h__2_416_);
v_it_418_ = lean_ctor_get(v_x_414_, 0);
lean_inc(v_it_418_);
v_out_419_ = lean_ctor_get(v_x_414_, 1);
lean_inc(v_out_419_);
lean_dec_ref(v_x_414_);
v___x_420_ = lean_apply_3(v_h__1_415_, v_it_418_, v_out_419_, lean_box(0));
return v___x_420_;
}
case 1:
{
lean_object* v_it_421_; lean_object* v___x_422_; 
lean_dec(v_h__3_417_);
lean_dec(v_h__1_415_);
v_it_421_ = lean_ctor_get(v_x_414_, 0);
lean_inc(v_it_421_);
lean_dec_ref(v_x_414_);
v___x_422_ = lean_apply_2(v_h__2_416_, v_it_421_, lean_box(0));
return v___x_422_;
}
default: 
{
lean_object* v___x_423_; 
lean_dec(v_h__2_416_);
lean_dec(v_h__1_415_);
v___x_423_ = lean_apply_1(v_h__3_417_, lean_box(0));
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_, lean_object* v_m_426_, lean_object* v_inst_427_, lean_object* v_it_428_, lean_object* v_motive_429_, lean_object* v_x_430_, lean_object* v_h__1_431_, lean_object* v_h__2_432_, lean_object* v_h__3_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(v_x_430_, v_h__1_431_, v_h__2_432_, v_h__3_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_435_, lean_object* v_00_u03b2_436_, lean_object* v_m_437_, lean_object* v_inst_438_, lean_object* v_it_439_, lean_object* v_motive_440_, lean_object* v_x_441_, lean_object* v_h__1_442_, lean_object* v_h__2_443_, lean_object* v_h__3_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_435_, v_00_u03b2_436_, v_m_437_, v_inst_438_, v_it_439_, v_motive_440_, v_x_441_, v_h__1_442_, v_h__2_443_, v_h__3_444_);
lean_dec(v_it_439_);
lean_dec(v_inst_438_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_446_, lean_object* v_h__1_447_, lean_object* v_h__2_448_){
_start:
{
if (lean_obj_tag(v_____do__lift_446_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; 
lean_dec(v_h__1_447_);
v_a_449_ = lean_ctor_get(v_____do__lift_446_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v_____do__lift_446_);
v___x_450_ = lean_apply_1(v_h__2_448_, v_a_449_);
return v___x_450_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_452_; 
lean_dec(v_h__2_448_);
v_a_451_ = lean_ctor_get(v_____do__lift_446_, 0);
lean_inc(v_a_451_);
lean_dec_ref(v_____do__lift_446_);
v___x_452_ = lean_apply_1(v_h__1_447_, v_a_451_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_453_, lean_object* v_motive_454_, lean_object* v_____do__lift_455_, lean_object* v_h__1_456_, lean_object* v_h__2_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(v_____do__lift_455_, v_h__1_456_, v_h__2_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_, lean_object* v_h__3_462_){
_start:
{
switch(lean_obj_tag(v_x_459_))
{
case 0:
{
lean_object* v_it_463_; lean_object* v_out_464_; lean_object* v___x_465_; 
lean_dec(v_h__3_462_);
lean_dec(v_h__2_461_);
v_it_463_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_it_463_);
v_out_464_ = lean_ctor_get(v_x_459_, 1);
lean_inc(v_out_464_);
lean_dec_ref(v_x_459_);
v___x_465_ = lean_apply_2(v_h__1_460_, v_it_463_, v_out_464_);
return v___x_465_;
}
case 1:
{
lean_object* v_it_466_; lean_object* v___x_467_; 
lean_dec(v_h__3_462_);
lean_dec(v_h__1_460_);
v_it_466_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_it_466_);
lean_dec_ref(v_x_459_);
v___x_467_ = lean_apply_1(v_h__2_461_, v_it_466_);
return v___x_467_;
}
default: 
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_h__2_461_);
lean_dec(v_h__1_460_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_apply_1(v_h__3_462_, v___x_468_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_motive_472_, lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_, lean_object* v_h__3_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(v_x_473_, v_h__1_474_, v_h__2_475_, v_h__3_476_);
return v___x_477_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
}
#ifdef __cplusplus
}
#endif
