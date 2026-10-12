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
lean_dec_ref_known(v_x_1_, 2);
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
lean_dec_ref_known(v_x_1_, 1);
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
switch(lean_obj_tag(v_x_17_))
{
case 0:
{
lean_object* v_it_21_; lean_object* v_out_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__2_19_);
v_it_21_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_21_);
v_out_22_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_out_22_);
lean_dec_ref_known(v_x_17_, 2);
v___x_23_ = lean_apply_3(v_h__1_18_, v_it_21_, v_out_22_, lean_box(0));
return v___x_23_;
}
case 1:
{
lean_object* v_it_24_; lean_object* v___x_25_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__1_18_);
v_it_24_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_24_);
lean_dec_ref_known(v_x_17_, 1);
v___x_25_ = lean_apply_2(v_h__2_19_, v_it_24_, lean_box(0));
return v___x_25_;
}
default: 
{
lean_object* v___x_26_; 
lean_dec(v_h__2_19_);
lean_dec(v_h__1_18_);
v___x_26_ = lean_apply_1(v_h__3_20_, lean_box(0));
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_m_29_, lean_object* v_inst_30_, lean_object* v_it_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_27_, v_00_u03b2_28_, v_m_29_, v_inst_30_, v_it_31_, v_motive_32_, v_x_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_);
lean_dec(v_it_31_);
lean_dec(v_inst_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
if (lean_obj_tag(v_____do__lift_38_) == 0)
{
lean_object* v___x_41_; 
lean_dec(v_h__2_40_);
v___x_41_ = lean_apply_1(v_h__1_39_, lean_box(0));
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_39_);
v_val_42_ = lean_ctor_get(v_____do__lift_38_, 0);
lean_inc(v_val_42_);
lean_dec_ref_known(v_____do__lift_38_, 1);
v___x_43_ = lean_apply_2(v_h__2_40_, v_val_42_, lean_box(0));
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_44_, lean_object* v_00_u03b2_x27_45_, lean_object* v_n_46_, lean_object* v_f_47_, lean_object* v_out_48_, lean_object* v_motive_49_, lean_object* v_____do__lift_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_____do__lift_50_) == 0)
{
lean_object* v___x_53_; 
lean_dec(v_h__2_52_);
v___x_53_ = lean_apply_1(v_h__1_51_, lean_box(0));
return v___x_53_;
}
else
{
lean_object* v_val_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_51_);
v_val_54_ = lean_ctor_get(v_____do__lift_50_, 0);
lean_inc(v_val_54_);
lean_dec_ref_known(v_____do__lift_50_, 1);
v___x_55_ = lean_apply_2(v_h__2_52_, v_val_54_, lean_box(0));
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_56_, lean_object* v_00_u03b2_x27_57_, lean_object* v_n_58_, lean_object* v_f_59_, lean_object* v_out_60_, lean_object* v_motive_61_, lean_object* v_____do__lift_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_56_, v_00_u03b2_x27_57_, v_n_58_, v_f_59_, v_out_60_, v_motive_61_, v_____do__lift_62_, v_h__1_63_, v_h__2_64_);
lean_dec(v_out_60_);
lean_dec(v_f_59_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_, lean_object* v_h__3_69_){
_start:
{
switch(lean_obj_tag(v_x_66_))
{
case 0:
{
lean_object* v_it_70_; lean_object* v_out_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_69_);
lean_dec(v_h__2_68_);
v_it_70_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_it_70_);
v_out_71_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_out_71_);
lean_dec_ref_known(v_x_66_, 2);
v___x_72_ = lean_apply_3(v_h__1_67_, v_it_70_, v_out_71_, lean_box(0));
return v___x_72_;
}
case 1:
{
lean_object* v_it_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_69_);
lean_dec(v_h__1_67_);
v_it_73_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_it_73_);
lean_dec_ref_known(v_x_66_, 1);
v___x_74_ = lean_apply_2(v_h__2_68_, v_it_73_, lean_box(0));
return v___x_74_;
}
default: 
{
lean_object* v___x_75_; 
lean_dec(v_h__2_68_);
lean_dec(v_h__1_67_);
v___x_75_ = lean_apply_1(v_h__3_69_, lean_box(0));
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_inst_78_, lean_object* v_it_79_, lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
_start:
{
switch(lean_obj_tag(v_x_81_))
{
case 0:
{
lean_object* v_it_85_; lean_object* v_out_86_; lean_object* v___x_87_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__2_83_);
v_it_85_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_it_85_);
v_out_86_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_out_86_);
lean_dec_ref_known(v_x_81_, 2);
v___x_87_ = lean_apply_3(v_h__1_82_, v_it_85_, v_out_86_, lean_box(0));
return v___x_87_;
}
case 1:
{
lean_object* v_it_88_; lean_object* v___x_89_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__1_82_);
v_it_88_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_it_88_);
lean_dec_ref_known(v_x_81_, 1);
v___x_89_ = lean_apply_2(v_h__2_83_, v_it_88_, lean_box(0));
return v___x_89_;
}
default: 
{
lean_object* v___x_90_; 
lean_dec(v_h__2_83_);
lean_dec(v_h__1_82_);
v___x_90_ = lean_apply_1(v_h__3_84_, lean_box(0));
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_inst_93_, lean_object* v_it_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_91_, v_00_u03b2_92_, v_inst_93_, v_it_94_, v_motive_95_, v_x_96_, v_h__1_97_, v_h__2_98_, v_h__3_99_);
lean_dec(v_it_94_);
lean_dec(v_inst_93_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
if (lean_obj_tag(v_____do__lift_101_) == 0)
{
lean_object* v___x_104_; 
lean_dec(v_h__2_103_);
v___x_104_ = lean_apply_1(v_h__1_102_, lean_box(0));
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_102_);
v_val_105_ = lean_ctor_get(v_____do__lift_101_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v_____do__lift_101_, 1);
v___x_106_ = lean_apply_2(v_h__2_103_, v_val_105_, lean_box(0));
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_107_, lean_object* v_00_u03b3_108_, lean_object* v_n_109_, lean_object* v_f_110_, lean_object* v_out_111_, lean_object* v_motive_112_, lean_object* v_____do__lift_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_){
_start:
{
if (lean_obj_tag(v_____do__lift_113_) == 0)
{
lean_object* v___x_116_; 
lean_dec(v_h__2_115_);
v___x_116_ = lean_apply_1(v_h__1_114_, lean_box(0));
return v___x_116_;
}
else
{
lean_object* v_val_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_114_);
v_val_117_ = lean_ctor_get(v_____do__lift_113_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v_____do__lift_113_, 1);
v___x_118_ = lean_apply_2(v_h__2_115_, v_val_117_, lean_box(0));
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_119_, lean_object* v_00_u03b3_120_, lean_object* v_n_121_, lean_object* v_f_122_, lean_object* v_out_123_, lean_object* v_motive_124_, lean_object* v_____do__lift_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_119_, v_00_u03b3_120_, v_n_121_, v_f_122_, v_out_123_, v_motive_124_, v_____do__lift_125_, v_h__1_126_, v_h__2_127_);
lean_dec(v_out_123_);
lean_dec(v_f_122_);
return v_res_128_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
if (v_____do__lift_129_ == 0)
{
lean_object* v___x_132_; 
lean_dec(v_h__2_131_);
v___x_132_ = lean_apply_1(v_h__1_130_, lean_box(0));
return v___x_132_;
}
else
{
lean_object* v___x_133_; 
lean_dec(v_h__1_130_);
v___x_133_ = lean_apply_1(v_h__2_131_, lean_box(0));
return v___x_133_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_129_ = stack[0].m_num;
lean_object* v_h__1_130_ = stack[1].m_obj;
lean_object* v_h__2_131_ = stack[2].m_obj;
lean_object* v_res_134_;
v_res_134_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_129_, v_h__1_130_, v_h__2_131_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
uint8_t v_____do__lift_23__boxed_138_; lean_object* v_res_139_; 
v_____do__lift_23__boxed_138_ = lean_unbox(v_____do__lift_135_);
v_res_139_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_23__boxed_138_, v_h__1_136_, v_h__2_137_);
return v_res_139_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_140_, lean_object* v_n_141_, lean_object* v_f_142_, lean_object* v_out_143_, lean_object* v_motive_144_, uint8_t v_____do__lift_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (v_____do__lift_145_ == 0)
{
lean_object* v___x_148_; 
lean_dec(v_h__2_147_);
v___x_148_ = lean_apply_1(v_h__1_146_, lean_box(0));
return v___x_148_;
}
else
{
lean_object* v___x_149_; 
lean_dec(v_h__1_146_);
v___x_149_ = lean_apply_1(v_h__2_147_, lean_box(0));
return v___x_149_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_142_ = stack[2].m_obj;
lean_object* v_out_143_ = stack[3].m_obj;
uint8_t v_____do__lift_145_ = stack[5].m_num;
lean_object* v_h__1_146_ = stack[6].m_obj;
lean_object* v_h__2_147_ = stack[7].m_obj;
lean_object* v_res_150_;
v_res_150_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_box(0), lean_box(0), v_f_142_, v_out_143_, lean_box(0), v_____do__lift_145_, v_h__1_146_, v_h__2_147_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_151_, lean_object* v_n_152_, lean_object* v_f_153_, lean_object* v_out_154_, lean_object* v_motive_155_, lean_object* v_____do__lift_156_, lean_object* v_h__1_157_, lean_object* v_h__2_158_){
_start:
{
uint8_t v_____do__lift_34__boxed_159_; lean_object* v_res_160_; 
v_____do__lift_34__boxed_159_ = lean_unbox(v_____do__lift_156_);
v_res_160_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_151_, v_n_152_, v_f_153_, v_out_154_, v_motive_155_, v_____do__lift_34__boxed_159_, v_h__1_157_, v_h__2_158_);
lean_dec(v_out_154_);
lean_dec(v_f_153_);
return v_res_160_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
if (v_____do__lift_161_ == 0)
{
lean_object* v___x_164_; 
lean_dec(v_h__2_163_);
v___x_164_ = lean_apply_1(v_h__1_162_, lean_box(0));
return v___x_164_;
}
else
{
lean_object* v___x_165_; 
lean_dec(v_h__1_162_);
v___x_165_ = lean_apply_1(v_h__2_163_, lean_box(0));
return v___x_165_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_161_ = stack[0].m_num;
lean_object* v_h__1_162_ = stack[1].m_obj;
lean_object* v_h__2_163_ = stack[2].m_obj;
lean_object* v_res_166_;
v_res_166_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_161_, v_h__1_162_, v_h__2_163_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_167_, lean_object* v_h__1_168_, lean_object* v_h__2_169_){
_start:
{
uint8_t v_____do__lift_23__boxed_170_; lean_object* v_res_171_; 
v_____do__lift_23__boxed_170_ = lean_unbox(v_____do__lift_167_);
v_res_171_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_23__boxed_170_, v_h__1_168_, v_h__2_169_);
return v_res_171_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_172_, lean_object* v_n_173_, lean_object* v_f_174_, lean_object* v_out_175_, lean_object* v_motive_176_, uint8_t v_____do__lift_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
if (v_____do__lift_177_ == 0)
{
lean_object* v___x_180_; 
lean_dec(v_h__2_179_);
v___x_180_ = lean_apply_1(v_h__1_178_, lean_box(0));
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
lean_dec(v_h__1_178_);
v___x_181_ = lean_apply_1(v_h__2_179_, lean_box(0));
return v___x_181_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_174_ = stack[2].m_obj;
lean_object* v_out_175_ = stack[3].m_obj;
uint8_t v_____do__lift_177_ = stack[5].m_num;
lean_object* v_h__1_178_ = stack[6].m_obj;
lean_object* v_h__2_179_ = stack[7].m_obj;
lean_object* v_res_182_;
v_res_182_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(lean_box(0), lean_box(0), v_f_174_, v_out_175_, lean_box(0), v_____do__lift_177_, v_h__1_178_, v_h__2_179_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_183_, lean_object* v_n_184_, lean_object* v_f_185_, lean_object* v_out_186_, lean_object* v_motive_187_, lean_object* v_____do__lift_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_){
_start:
{
uint8_t v_____do__lift_34__boxed_191_; lean_object* v_res_192_; 
v_____do__lift_34__boxed_191_ = lean_unbox(v_____do__lift_188_);
v_res_192_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_183_, v_n_184_, v_f_185_, v_out_186_, v_motive_187_, v_____do__lift_34__boxed_191_, v_h__1_189_, v_h__2_190_);
lean_dec(v_out_186_);
lean_dec(v_f_185_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_193_, lean_object* v_h__1_194_, lean_object* v_h__2_195_){
_start:
{
if (lean_obj_tag(v_____do__lift_193_) == 0)
{
lean_object* v___x_196_; 
lean_dec(v_h__2_195_);
v___x_196_ = lean_apply_1(v_h__1_194_, lean_box(0));
return v___x_196_;
}
else
{
lean_object* v_val_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_194_);
v_val_197_ = lean_ctor_get(v_____do__lift_193_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v_____do__lift_193_, 1);
v___x_198_ = lean_apply_2(v_h__2_195_, v_val_197_, lean_box(0));
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_199_, lean_object* v_00_u03b2_x27_200_, lean_object* v_n_201_, lean_object* v_f_202_, lean_object* v_inst_203_, lean_object* v_out_204_, lean_object* v_motive_205_, lean_object* v_____do__lift_206_, lean_object* v_h__1_207_, lean_object* v_h__2_208_){
_start:
{
if (lean_obj_tag(v_____do__lift_206_) == 0)
{
lean_object* v___x_209_; 
lean_dec(v_h__2_208_);
v___x_209_ = lean_apply_1(v_h__1_207_, lean_box(0));
return v___x_209_;
}
else
{
lean_object* v_val_210_; lean_object* v___x_211_; 
lean_dec(v_h__1_207_);
v_val_210_ = lean_ctor_get(v_____do__lift_206_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v_____do__lift_206_, 1);
v___x_211_ = lean_apply_2(v_h__2_208_, v_val_210_, lean_box(0));
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_212_, lean_object* v_00_u03b2_x27_213_, lean_object* v_n_214_, lean_object* v_f_215_, lean_object* v_inst_216_, lean_object* v_out_217_, lean_object* v_motive_218_, lean_object* v_____do__lift_219_, lean_object* v_h__1_220_, lean_object* v_h__2_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_212_, v_00_u03b2_x27_213_, v_n_214_, v_f_215_, v_inst_216_, v_out_217_, v_motive_218_, v_____do__lift_219_, v_h__1_220_, v_h__2_221_);
lean_dec(v_out_217_);
lean_dec(v_inst_216_);
lean_dec(v_f_215_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_){
_start:
{
if (lean_obj_tag(v_____do__lift_223_) == 0)
{
lean_object* v___x_226_; 
lean_dec(v_h__2_225_);
v___x_226_ = lean_apply_1(v_h__1_224_, lean_box(0));
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_228_; 
lean_dec(v_h__1_224_);
v_val_227_ = lean_ctor_get(v_____do__lift_223_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v_____do__lift_223_, 1);
v___x_228_ = lean_apply_2(v_h__2_225_, v_val_227_, lean_box(0));
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_229_, lean_object* v_n_230_, lean_object* v_00_u03b2_x27_231_, lean_object* v_f_232_, lean_object* v_inst_233_, lean_object* v_out_234_, lean_object* v_motive_235_, lean_object* v_____do__lift_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
_start:
{
if (lean_obj_tag(v_____do__lift_236_) == 0)
{
lean_object* v___x_239_; 
lean_dec(v_h__2_238_);
v___x_239_ = lean_apply_1(v_h__1_237_, lean_box(0));
return v___x_239_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_241_; 
lean_dec(v_h__1_237_);
v_val_240_ = lean_ctor_get(v_____do__lift_236_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v_____do__lift_236_, 1);
v___x_241_ = lean_apply_2(v_h__2_238_, v_val_240_, lean_box(0));
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_242_, lean_object* v_n_243_, lean_object* v_00_u03b2_x27_244_, lean_object* v_f_245_, lean_object* v_inst_246_, lean_object* v_out_247_, lean_object* v_motive_248_, lean_object* v_____do__lift_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(v_00_u03b2_242_, v_n_243_, v_00_u03b2_x27_244_, v_f_245_, v_inst_246_, v_out_247_, v_motive_248_, v_____do__lift_249_, v_h__1_250_, v_h__2_251_);
lean_dec(v_out_247_);
lean_dec(v_inst_246_);
lean_dec(v_f_245_);
return v_res_252_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_){
_start:
{
if (v_____do__lift_253_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_h__2_255_);
v___x_256_ = lean_apply_1(v_h__1_254_, lean_box(0));
return v___x_256_;
}
else
{
lean_object* v___x_257_; 
lean_dec(v_h__1_254_);
v___x_257_ = lean_apply_1(v_h__2_255_, lean_box(0));
return v___x_257_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_253_ = stack[0].m_num;
lean_object* v_h__1_254_ = stack[1].m_obj;
lean_object* v_h__2_255_ = stack[2].m_obj;
lean_object* v_res_258_;
v_res_258_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_253_, v_h__1_254_, v_h__2_255_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_259_, lean_object* v_h__1_260_, lean_object* v_h__2_261_){
_start:
{
uint8_t v_____do__lift_25__boxed_262_; lean_object* v_res_263_; 
v_____do__lift_25__boxed_262_ = lean_unbox(v_____do__lift_259_);
v_res_263_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_25__boxed_262_, v_h__1_260_, v_h__2_261_);
return v_res_263_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object* v_00_u03b2_264_, lean_object* v_n_265_, lean_object* v_f_266_, lean_object* v_inst_267_, lean_object* v_out_268_, lean_object* v_motive_269_, uint8_t v_____do__lift_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_){
_start:
{
if (v_____do__lift_270_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v_h__2_272_);
v___x_273_ = lean_apply_1(v_h__1_271_, lean_box(0));
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v_h__1_271_);
v___x_274_ = lean_apply_1(v_h__2_272_, lean_box(0));
return v___x_274_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_266_ = stack[2].m_obj;
lean_object* v_inst_267_ = stack[3].m_obj;
lean_object* v_out_268_ = stack[4].m_obj;
uint8_t v_____do__lift_270_ = stack[6].m_num;
lean_object* v_h__1_271_ = stack[7].m_obj;
lean_object* v_h__2_272_ = stack[8].m_obj;
lean_object* v_res_275_;
v_res_275_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_box(0), lean_box(0), v_f_266_, v_inst_267_, v_out_268_, lean_box(0), v_____do__lift_270_, v_h__1_271_, v_h__2_272_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_276_, lean_object* v_n_277_, lean_object* v_f_278_, lean_object* v_inst_279_, lean_object* v_out_280_, lean_object* v_motive_281_, lean_object* v_____do__lift_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
uint8_t v_____do__lift_37__boxed_285_; lean_object* v_res_286_; 
v_____do__lift_37__boxed_285_ = lean_unbox(v_____do__lift_282_);
v_res_286_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_276_, v_n_277_, v_f_278_, v_inst_279_, v_out_280_, v_motive_281_, v_____do__lift_37__boxed_285_, v_h__1_283_, v_h__2_284_);
lean_dec(v_out_280_);
lean_dec(v_inst_279_);
lean_dec(v_f_278_);
return v_res_286_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_){
_start:
{
if (v_____do__lift_287_ == 0)
{
lean_object* v___x_290_; 
lean_dec(v_h__2_289_);
v___x_290_ = lean_apply_1(v_h__1_288_, lean_box(0));
return v___x_290_;
}
else
{
lean_object* v___x_291_; 
lean_dec(v_h__1_288_);
v___x_291_ = lean_apply_1(v_h__2_289_, lean_box(0));
return v___x_291_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_287_ = stack[0].m_num;
lean_object* v_h__1_288_ = stack[1].m_obj;
lean_object* v_h__2_289_ = stack[2].m_obj;
lean_object* v_res_292_;
v_res_292_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_287_, v_h__1_288_, v_h__2_289_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_293_, lean_object* v_h__1_294_, lean_object* v_h__2_295_){
_start:
{
uint8_t v_____do__lift_25__boxed_296_; lean_object* v_res_297_; 
v_____do__lift_25__boxed_296_ = lean_unbox(v_____do__lift_293_);
v_res_297_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_25__boxed_296_, v_h__1_294_, v_h__2_295_);
return v_res_297_;
}
}
lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(lean_object* v_00_u03b2_298_, lean_object* v_n_299_, lean_object* v_f_300_, lean_object* v_inst_301_, lean_object* v_out_302_, lean_object* v_motive_303_, uint8_t v_____do__lift_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
if (v_____do__lift_304_ == 0)
{
lean_object* v___x_307_; 
lean_dec(v_h__2_306_);
v___x_307_ = lean_apply_1(v_h__1_305_, lean_box(0));
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v_h__1_305_);
v___x_308_ = lean_apply_1(v_h__2_306_, lean_box(0));
return v___x_308_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_300_ = stack[2].m_obj;
lean_object* v_inst_301_ = stack[3].m_obj;
lean_object* v_out_302_ = stack[4].m_obj;
uint8_t v_____do__lift_304_ = stack[6].m_num;
lean_object* v_h__1_305_ = stack[7].m_obj;
lean_object* v_h__2_306_ = stack[8].m_obj;
lean_object* v_res_309_;
v_res_309_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(lean_box(0), lean_box(0), v_f_300_, v_inst_301_, v_out_302_, lean_box(0), v_____do__lift_304_, v_h__1_305_, v_h__2_306_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_310_, lean_object* v_n_311_, lean_object* v_f_312_, lean_object* v_inst_313_, lean_object* v_out_314_, lean_object* v_motive_315_, lean_object* v_____do__lift_316_, lean_object* v_h__1_317_, lean_object* v_h__2_318_){
_start:
{
uint8_t v_____do__lift_37__boxed_319_; lean_object* v_res_320_; 
v_____do__lift_37__boxed_319_ = lean_unbox(v_____do__lift_316_);
v_res_320_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(v_00_u03b2_310_, v_n_311_, v_f_312_, v_inst_313_, v_out_314_, v_motive_315_, v_____do__lift_37__boxed_319_, v_h__1_317_, v_h__2_318_);
lean_dec(v_out_314_);
lean_dec(v_inst_313_);
lean_dec(v_f_312_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v___x_324_; 
lean_dec(v_h__2_323_);
v___x_324_ = lean_apply_1(v_h__1_322_, lean_box(0));
return v___x_324_;
}
else
{
lean_object* v_val_325_; lean_object* v___x_326_; 
lean_dec(v_h__1_322_);
v_val_325_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v_x_321_, 1);
v___x_326_ = lean_apply_2(v_h__2_323_, v_val_325_, lean_box(0));
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object* v_00_u03b2_x27_327_, lean_object* v_motive_328_, lean_object* v_x_329_, lean_object* v_h__1_330_, lean_object* v_h__2_331_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_object* v___x_332_; 
lean_dec(v_h__2_331_);
v___x_332_ = lean_apply_1(v_h__1_330_, lean_box(0));
return v___x_332_;
}
else
{
lean_object* v_val_333_; lean_object* v___x_334_; 
lean_dec(v_h__1_330_);
v_val_333_ = lean_ctor_get(v_x_329_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v_x_329_, 1);
v___x_334_ = lean_apply_2(v_h__2_331_, v_val_333_, lean_box(0));
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(lean_object* v_x_335_, lean_object* v_h__1_336_, lean_object* v_h__2_337_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v___x_338_; 
lean_dec(v_h__2_337_);
v___x_338_ = lean_apply_1(v_h__1_336_, lean_box(0));
return v___x_338_;
}
else
{
lean_object* v_val_339_; lean_object* v___x_340_; 
lean_dec(v_h__1_336_);
v_val_339_ = lean_ctor_get(v_x_335_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v_x_335_, 1);
v___x_340_ = lean_apply_2(v_h__2_337_, v_val_339_, lean_box(0));
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter(lean_object* v_00_u03b3_341_, lean_object* v_motive_342_, lean_object* v_x_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v___x_346_; 
lean_dec(v_h__2_345_);
v___x_346_ = lean_apply_1(v_h__1_344_, lean_box(0));
return v___x_346_;
}
else
{
lean_object* v_val_347_; lean_object* v___x_348_; 
lean_dec(v_h__1_344_);
v_val_347_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v_x_343_, 1);
v___x_348_ = lean_apply_2(v_h__2_345_, v_val_347_, lean_box(0));
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(lean_object* v_x_349_, lean_object* v_h__1_350_, lean_object* v_h__2_351_, lean_object* v_h__3_352_){
_start:
{
switch(lean_obj_tag(v_x_349_))
{
case 0:
{
lean_object* v_it_353_; lean_object* v_out_354_; lean_object* v___x_355_; 
lean_dec(v_h__3_352_);
lean_dec(v_h__2_351_);
v_it_353_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_it_353_);
v_out_354_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_out_354_);
lean_dec_ref_known(v_x_349_, 2);
v___x_355_ = lean_apply_2(v_h__1_350_, v_it_353_, v_out_354_);
return v___x_355_;
}
case 1:
{
lean_object* v_it_356_; lean_object* v___x_357_; 
lean_dec(v_h__3_352_);
lean_dec(v_h__1_350_);
v_it_356_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_it_356_);
lean_dec_ref_known(v_x_349_, 1);
v___x_357_ = lean_apply_1(v_h__2_351_, v_it_356_);
return v___x_357_;
}
default: 
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_h__2_351_);
lean_dec(v_h__1_350_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_apply_1(v_h__3_352_, v___x_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter(lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_motive_362_, lean_object* v_x_363_, lean_object* v_h__1_364_, lean_object* v_h__2_365_, lean_object* v_h__3_366_){
_start:
{
switch(lean_obj_tag(v_x_363_))
{
case 0:
{
lean_object* v_it_367_; lean_object* v_out_368_; lean_object* v___x_369_; 
lean_dec(v_h__3_366_);
lean_dec(v_h__2_365_);
v_it_367_ = lean_ctor_get(v_x_363_, 0);
lean_inc(v_it_367_);
v_out_368_ = lean_ctor_get(v_x_363_, 1);
lean_inc(v_out_368_);
lean_dec_ref_known(v_x_363_, 2);
v___x_369_ = lean_apply_2(v_h__1_364_, v_it_367_, v_out_368_);
return v___x_369_;
}
case 1:
{
lean_object* v_it_370_; lean_object* v___x_371_; 
lean_dec(v_h__3_366_);
lean_dec(v_h__1_364_);
v_it_370_ = lean_ctor_get(v_x_363_, 0);
lean_inc(v_it_370_);
lean_dec_ref_known(v_x_363_, 1);
v___x_371_ = lean_apply_1(v_h__2_365_, v_it_370_);
return v___x_371_;
}
default: 
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v_h__2_365_);
lean_dec(v_h__1_364_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_apply_1(v_h__3_366_, v___x_372_);
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(lean_object* v_x_374_, lean_object* v_h__1_375_, lean_object* v_h__2_376_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_h__2_376_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_apply_1(v_h__1_375_, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v_val_379_; lean_object* v___x_380_; 
lean_dec(v_h__1_375_);
v_val_379_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_val_379_);
lean_dec_ref_known(v_x_374_, 1);
v___x_380_ = lean_apply_1(v_h__2_376_, v_val_379_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter(lean_object* v_00_u03b3_381_, lean_object* v_motive_382_, lean_object* v_x_383_, lean_object* v_h__1_384_, lean_object* v_h__2_385_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_h__2_385_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_apply_1(v_h__1_384_, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v_val_388_; lean_object* v___x_389_; 
lean_dec(v_h__1_384_);
v_val_388_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_x_383_, 1);
v___x_389_ = lean_apply_1(v_h__2_385_, v_val_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_){
_start:
{
if (lean_obj_tag(v_____do__lift_390_) == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_h__1_391_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_apply_1(v_h__2_392_, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; 
lean_dec(v_h__2_392_);
v_val_395_ = lean_ctor_get(v_____do__lift_390_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_____do__lift_390_, 1);
v___x_396_ = lean_apply_1(v_h__1_391_, v_val_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_397_, lean_object* v_motive_398_, lean_object* v_____do__lift_399_, lean_object* v_h__1_400_, lean_object* v_h__2_401_){
_start:
{
if (lean_obj_tag(v_____do__lift_399_) == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_h__1_400_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_apply_1(v_h__2_401_, v___x_402_);
return v___x_403_;
}
else
{
lean_object* v_val_404_; lean_object* v___x_405_; 
lean_dec(v_h__2_401_);
v_val_404_ = lean_ctor_get(v_____do__lift_399_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v_____do__lift_399_, 1);
v___x_405_ = lean_apply_1(v_h__1_400_, v_val_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_406_, lean_object* v_h__1_407_, lean_object* v_h__2_408_){
_start:
{
if (lean_obj_tag(v_____do__lift_406_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_h__1_407_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_1(v_h__2_408_, v___x_409_);
return v___x_410_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_412_; 
lean_dec(v_h__2_408_);
v_val_411_ = lean_ctor_get(v_____do__lift_406_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v_____do__lift_406_, 1);
v___x_412_ = lean_apply_1(v_h__1_407_, v_val_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_413_, lean_object* v_motive_414_, lean_object* v_____do__lift_415_, lean_object* v_h__1_416_, lean_object* v_h__2_417_){
_start:
{
if (lean_obj_tag(v_____do__lift_415_) == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_h__1_416_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_apply_1(v_h__2_417_, v___x_418_);
return v___x_419_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_421_; 
lean_dec(v_h__2_417_);
v_val_420_ = lean_ctor_get(v_____do__lift_415_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_____do__lift_415_, 1);
v___x_421_ = lean_apply_1(v_h__1_416_, v_val_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_422_, lean_object* v_h__1_423_, lean_object* v_h__2_424_){
_start:
{
if (lean_obj_tag(v_____x_422_) == 1)
{
lean_object* v_val_425_; lean_object* v___x_426_; 
lean_dec(v_h__2_424_);
v_val_425_ = lean_ctor_get(v_____x_422_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_____x_422_, 1);
v___x_426_ = lean_apply_1(v_h__1_423_, v_val_425_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_dec(v_h__1_423_);
v___x_427_ = lean_apply_2(v_h__2_424_, v_____x_422_, lean_box(0));
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_428_, lean_object* v_motive_429_, lean_object* v_____x_430_, lean_object* v_h__1_431_, lean_object* v_h__2_432_){
_start:
{
if (lean_obj_tag(v_____x_430_) == 1)
{
lean_object* v_val_433_; lean_object* v___x_434_; 
lean_dec(v_h__2_432_);
v_val_433_ = lean_ctor_get(v_____x_430_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v_____x_430_, 1);
v___x_434_ = lean_apply_1(v_h__1_431_, v_val_433_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
lean_dec(v_h__1_431_);
v___x_435_ = lean_apply_2(v_h__2_432_, v_____x_430_, lean_box(0));
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_436_, lean_object* v_h__1_437_, lean_object* v_h__2_438_){
_start:
{
if (lean_obj_tag(v_____x_436_) == 1)
{
lean_object* v_val_439_; lean_object* v___x_440_; 
lean_dec(v_h__2_438_);
v_val_439_ = lean_ctor_get(v_____x_436_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v_____x_436_, 1);
v___x_440_ = lean_apply_1(v_h__1_437_, v_val_439_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
lean_dec(v_h__1_437_);
v___x_441_ = lean_apply_2(v_h__2_438_, v_____x_436_, lean_box(0));
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_442_, lean_object* v_motive_443_, lean_object* v_____x_444_, lean_object* v_h__1_445_, lean_object* v_h__2_446_){
_start:
{
if (lean_obj_tag(v_____x_444_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_448_; 
lean_dec(v_h__2_446_);
v_val_447_ = lean_ctor_get(v_____x_444_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_____x_444_, 1);
v___x_448_ = lean_apply_1(v_h__1_445_, v_val_447_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
lean_dec(v_h__1_445_);
v___x_449_ = lean_apply_2(v_h__2_446_, v_____x_444_, lean_box(0));
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_){
_start:
{
if (lean_obj_tag(v_____do__lift_450_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_454_; 
lean_dec(v_h__1_451_);
v_a_453_ = lean_ctor_get(v_____do__lift_450_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v_____do__lift_450_, 1);
v___x_454_ = lean_apply_1(v_h__2_452_, v_a_453_);
return v___x_454_;
}
else
{
lean_object* v_a_455_; lean_object* v___x_456_; 
lean_dec(v_h__2_452_);
v_a_455_ = lean_ctor_get(v_____do__lift_450_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v_____do__lift_450_, 1);
v___x_456_ = lean_apply_1(v_h__1_451_, v_a_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_457_, lean_object* v_motive_458_, lean_object* v_____do__lift_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
_start:
{
if (lean_obj_tag(v_____do__lift_459_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
lean_dec(v_h__1_460_);
v_a_462_ = lean_ctor_get(v_____do__lift_459_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v_____do__lift_459_, 1);
v___x_463_ = lean_apply_1(v_h__2_461_, v_a_462_);
return v___x_463_;
}
else
{
lean_object* v_a_464_; lean_object* v___x_465_; 
lean_dec(v_h__2_461_);
v_a_464_ = lean_ctor_get(v_____do__lift_459_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v_____do__lift_459_, 1);
v___x_465_ = lean_apply_1(v_h__1_460_, v_a_464_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_466_, lean_object* v_h__1_467_, lean_object* v_h__2_468_, lean_object* v_h__3_469_){
_start:
{
switch(lean_obj_tag(v_x_466_))
{
case 0:
{
lean_object* v_it_470_; lean_object* v_out_471_; lean_object* v___x_472_; 
lean_dec(v_h__3_469_);
lean_dec(v_h__2_468_);
v_it_470_ = lean_ctor_get(v_x_466_, 0);
lean_inc(v_it_470_);
v_out_471_ = lean_ctor_get(v_x_466_, 1);
lean_inc(v_out_471_);
lean_dec_ref_known(v_x_466_, 2);
v___x_472_ = lean_apply_3(v_h__1_467_, v_it_470_, v_out_471_, lean_box(0));
return v___x_472_;
}
case 1:
{
lean_object* v_it_473_; lean_object* v___x_474_; 
lean_dec(v_h__3_469_);
lean_dec(v_h__1_467_);
v_it_473_ = lean_ctor_get(v_x_466_, 0);
lean_inc(v_it_473_);
lean_dec_ref_known(v_x_466_, 1);
v___x_474_ = lean_apply_2(v_h__2_468_, v_it_473_, lean_box(0));
return v___x_474_;
}
default: 
{
lean_object* v___x_475_; 
lean_dec(v_h__2_468_);
lean_dec(v_h__1_467_);
v___x_475_ = lean_apply_1(v_h__3_469_, lean_box(0));
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_m_478_, lean_object* v_inst_479_, lean_object* v_it_480_, lean_object* v_motive_481_, lean_object* v_x_482_, lean_object* v_h__1_483_, lean_object* v_h__2_484_, lean_object* v_h__3_485_){
_start:
{
switch(lean_obj_tag(v_x_482_))
{
case 0:
{
lean_object* v_it_486_; lean_object* v_out_487_; lean_object* v___x_488_; 
lean_dec(v_h__3_485_);
lean_dec(v_h__2_484_);
v_it_486_ = lean_ctor_get(v_x_482_, 0);
lean_inc(v_it_486_);
v_out_487_ = lean_ctor_get(v_x_482_, 1);
lean_inc(v_out_487_);
lean_dec_ref_known(v_x_482_, 2);
v___x_488_ = lean_apply_3(v_h__1_483_, v_it_486_, v_out_487_, lean_box(0));
return v___x_488_;
}
case 1:
{
lean_object* v_it_489_; lean_object* v___x_490_; 
lean_dec(v_h__3_485_);
lean_dec(v_h__1_483_);
v_it_489_ = lean_ctor_get(v_x_482_, 0);
lean_inc(v_it_489_);
lean_dec_ref_known(v_x_482_, 1);
v___x_490_ = lean_apply_2(v_h__2_484_, v_it_489_, lean_box(0));
return v___x_490_;
}
default: 
{
lean_object* v___x_491_; 
lean_dec(v_h__2_484_);
lean_dec(v_h__1_483_);
v___x_491_ = lean_apply_1(v_h__3_485_, lean_box(0));
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_m_494_, lean_object* v_inst_495_, lean_object* v_it_496_, lean_object* v_motive_497_, lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_, lean_object* v_h__3_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_492_, v_00_u03b2_493_, v_m_494_, v_inst_495_, v_it_496_, v_motive_497_, v_x_498_, v_h__1_499_, v_h__2_500_, v_h__3_501_);
lean_dec(v_it_496_);
lean_dec(v_inst_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_){
_start:
{
if (lean_obj_tag(v_____do__lift_503_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
lean_dec(v_h__1_504_);
v_a_506_ = lean_ctor_get(v_____do__lift_503_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v_____do__lift_503_, 1);
v___x_507_ = lean_apply_1(v_h__2_505_, v_a_506_);
return v___x_507_;
}
else
{
lean_object* v_a_508_; lean_object* v___x_509_; 
lean_dec(v_h__2_505_);
v_a_508_ = lean_ctor_get(v_____do__lift_503_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v_____do__lift_503_, 1);
v___x_509_ = lean_apply_1(v_h__1_504_, v_a_508_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_510_, lean_object* v_motive_511_, lean_object* v_____do__lift_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_){
_start:
{
if (lean_obj_tag(v_____do__lift_512_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; 
lean_dec(v_h__1_513_);
v_a_515_ = lean_ctor_get(v_____do__lift_512_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v_____do__lift_512_, 1);
v___x_516_ = lean_apply_1(v_h__2_514_, v_a_515_);
return v___x_516_;
}
else
{
lean_object* v_a_517_; lean_object* v___x_518_; 
lean_dec(v_h__2_514_);
v_a_517_ = lean_ctor_get(v_____do__lift_512_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v_____do__lift_512_, 1);
v___x_518_ = lean_apply_1(v_h__1_513_, v_a_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_, lean_object* v_h__3_522_){
_start:
{
switch(lean_obj_tag(v_x_519_))
{
case 0:
{
lean_object* v_it_523_; lean_object* v_out_524_; lean_object* v___x_525_; 
lean_dec(v_h__3_522_);
lean_dec(v_h__2_521_);
v_it_523_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_it_523_);
v_out_524_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_out_524_);
lean_dec_ref_known(v_x_519_, 2);
v___x_525_ = lean_apply_2(v_h__1_520_, v_it_523_, v_out_524_);
return v___x_525_;
}
case 1:
{
lean_object* v_it_526_; lean_object* v___x_527_; 
lean_dec(v_h__3_522_);
lean_dec(v_h__1_520_);
v_it_526_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_it_526_);
lean_dec_ref_known(v_x_519_, 1);
v___x_527_ = lean_apply_1(v_h__2_521_, v_it_526_);
return v___x_527_;
}
default: 
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_h__2_521_);
lean_dec(v_h__1_520_);
v___x_528_ = lean_box(0);
v___x_529_ = lean_apply_1(v_h__3_522_, v___x_528_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_motive_532_, lean_object* v_x_533_, lean_object* v_h__1_534_, lean_object* v_h__2_535_, lean_object* v_h__3_536_){
_start:
{
switch(lean_obj_tag(v_x_533_))
{
case 0:
{
lean_object* v_it_537_; lean_object* v_out_538_; lean_object* v___x_539_; 
lean_dec(v_h__3_536_);
lean_dec(v_h__2_535_);
v_it_537_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_it_537_);
v_out_538_ = lean_ctor_get(v_x_533_, 1);
lean_inc(v_out_538_);
lean_dec_ref_known(v_x_533_, 2);
v___x_539_ = lean_apply_2(v_h__1_534_, v_it_537_, v_out_538_);
return v___x_539_;
}
case 1:
{
lean_object* v_it_540_; lean_object* v___x_541_; 
lean_dec(v_h__3_536_);
lean_dec(v_h__1_534_);
v_it_540_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_it_540_);
lean_dec_ref_known(v_x_533_, 1);
v___x_541_ = lean_apply_1(v_h__2_535_, v_it_540_);
return v___x_541_;
}
default: 
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v_h__2_535_);
lean_dec(v_h__1_534_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_apply_1(v_h__3_536_, v___x_542_);
return v___x_543_;
}
}
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
