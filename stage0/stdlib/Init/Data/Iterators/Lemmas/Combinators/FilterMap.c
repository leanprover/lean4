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
lean_dec_ref(v_x_17_);
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
lean_dec_ref(v_x_17_);
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
lean_dec_ref(v_____do__lift_38_);
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
lean_dec_ref(v_____do__lift_50_);
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
lean_dec_ref(v_x_66_);
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
lean_dec_ref(v_x_66_);
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
lean_dec_ref(v_x_81_);
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
lean_dec_ref(v_x_81_);
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
lean_dec_ref(v_____do__lift_101_);
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
lean_dec_ref(v_____do__lift_113_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_){
_start:
{
uint8_t v_____do__lift_72__boxed_137_; lean_object* v_res_138_; 
v_____do__lift_72__boxed_137_ = lean_unbox(v_____do__lift_134_);
v_res_138_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_137_, v_h__1_135_, v_h__2_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_139_, lean_object* v_n_140_, lean_object* v_f_141_, lean_object* v_out_142_, lean_object* v_motive_143_, uint8_t v_____do__lift_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_149_, lean_object* v_n_150_, lean_object* v_f_151_, lean_object* v_out_152_, lean_object* v_motive_153_, lean_object* v_____do__lift_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
uint8_t v_____do__lift_79__boxed_157_; lean_object* v_res_158_; 
v_____do__lift_79__boxed_157_ = lean_unbox(v_____do__lift_154_);
v_res_158_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_149_, v_n_150_, v_f_151_, v_out_152_, v_motive_153_, v_____do__lift_79__boxed_157_, v_h__1_155_, v_h__2_156_);
lean_dec(v_out_152_);
lean_dec(v_f_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(uint8_t v_____do__lift_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_){
_start:
{
if (v_____do__lift_159_ == 0)
{
lean_object* v___x_162_; 
lean_dec(v_h__2_161_);
v___x_162_ = lean_apply_1(v_h__1_160_, lean_box(0));
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
lean_dec(v_h__1_160_);
v___x_163_ = lean_apply_1(v_h__2_161_, lean_box(0));
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
uint8_t v_____do__lift_72__boxed_167_; lean_object* v_res_168_; 
v_____do__lift_72__boxed_167_ = lean_unbox(v_____do__lift_164_);
v_res_168_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_167_, v_h__1_165_, v_h__2_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_169_, lean_object* v_n_170_, lean_object* v_f_171_, lean_object* v_out_172_, lean_object* v_motive_173_, uint8_t v_____do__lift_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_){
_start:
{
if (v_____do__lift_174_ == 0)
{
lean_object* v___x_177_; 
lean_dec(v_h__2_176_);
v___x_177_ = lean_apply_1(v_h__1_175_, lean_box(0));
return v___x_177_;
}
else
{
lean_object* v___x_178_; 
lean_dec(v_h__1_175_);
v___x_178_ = lean_apply_1(v_h__2_176_, lean_box(0));
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter___boxed(lean_object* v_00_u03b2_179_, lean_object* v_n_180_, lean_object* v_f_181_, lean_object* v_out_182_, lean_object* v_motive_183_, lean_object* v_____do__lift_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_){
_start:
{
uint8_t v_____do__lift_79__boxed_187_; lean_object* v_res_188_; 
v_____do__lift_79__boxed_187_ = lean_unbox(v_____do__lift_184_);
v_res_188_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterWithPostcondition_match__1_splitter(v_00_u03b2_179_, v_n_180_, v_f_181_, v_out_182_, v_motive_183_, v_____do__lift_79__boxed_187_, v_h__1_185_, v_h__2_186_);
lean_dec(v_out_182_);
lean_dec(v_f_181_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_){
_start:
{
if (lean_obj_tag(v_____do__lift_189_) == 0)
{
lean_object* v___x_192_; 
lean_dec(v_h__2_191_);
v___x_192_ = lean_apply_1(v_h__1_190_, lean_box(0));
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; 
lean_dec(v_h__1_190_);
v_val_193_ = lean_ctor_get(v_____do__lift_189_, 0);
lean_inc(v_val_193_);
lean_dec_ref(v_____do__lift_189_);
v___x_194_ = lean_apply_2(v_h__2_191_, v_val_193_, lean_box(0));
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_195_, lean_object* v_00_u03b2_x27_196_, lean_object* v_n_197_, lean_object* v_f_198_, lean_object* v_inst_199_, lean_object* v_out_200_, lean_object* v_motive_201_, lean_object* v_____do__lift_202_, lean_object* v_h__1_203_, lean_object* v_h__2_204_){
_start:
{
if (lean_obj_tag(v_____do__lift_202_) == 0)
{
lean_object* v___x_205_; 
lean_dec(v_h__2_204_);
v___x_205_ = lean_apply_1(v_h__1_203_, lean_box(0));
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; 
lean_dec(v_h__1_203_);
v_val_206_ = lean_ctor_get(v_____do__lift_202_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v_____do__lift_202_);
v___x_207_ = lean_apply_2(v_h__2_204_, v_val_206_, lean_box(0));
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_208_, lean_object* v_00_u03b2_x27_209_, lean_object* v_n_210_, lean_object* v_f_211_, lean_object* v_inst_212_, lean_object* v_out_213_, lean_object* v_motive_214_, lean_object* v_____do__lift_215_, lean_object* v_h__1_216_, lean_object* v_h__2_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMapM_match__1_splitter(v_00_u03b2_208_, v_00_u03b2_x27_209_, v_n_210_, v_f_211_, v_inst_212_, v_out_213_, v_motive_214_, v_____do__lift_215_, v_h__1_216_, v_h__2_217_);
lean_dec(v_out_213_);
lean_dec(v_inst_212_);
lean_dec(v_f_211_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_219_, lean_object* v_h__1_220_, lean_object* v_h__2_221_){
_start:
{
if (lean_obj_tag(v_____do__lift_219_) == 0)
{
lean_object* v___x_222_; 
lean_dec(v_h__2_221_);
v___x_222_ = lean_apply_1(v_h__1_220_, lean_box(0));
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v___x_224_; 
lean_dec(v_h__1_220_);
v_val_223_ = lean_ctor_get(v_____do__lift_219_, 0);
lean_inc(v_val_223_);
lean_dec_ref(v_____do__lift_219_);
v___x_224_ = lean_apply_2(v_h__2_221_, v_val_223_, lean_box(0));
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(lean_object* v_00_u03b2_225_, lean_object* v_n_226_, lean_object* v_00_u03b2_x27_227_, lean_object* v_f_228_, lean_object* v_inst_229_, lean_object* v_out_230_, lean_object* v_motive_231_, lean_object* v_____do__lift_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_){
_start:
{
if (lean_obj_tag(v_____do__lift_232_) == 0)
{
lean_object* v___x_235_; 
lean_dec(v_h__2_234_);
v___x_235_ = lean_apply_1(v_h__1_233_, lean_box(0));
return v___x_235_;
}
else
{
lean_object* v_val_236_; lean_object* v___x_237_; 
lean_dec(v_h__1_233_);
v_val_236_ = lean_ctor_get(v_____do__lift_232_, 0);
lean_inc(v_val_236_);
lean_dec_ref(v_____do__lift_232_);
v___x_237_ = lean_apply_2(v_h__2_234_, v_val_236_, lean_box(0));
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter___boxed(lean_object* v_00_u03b2_238_, lean_object* v_n_239_, lean_object* v_00_u03b2_x27_240_, lean_object* v_f_241_, lean_object* v_inst_242_, lean_object* v_out_243_, lean_object* v_motive_244_, lean_object* v_____do__lift_245_, lean_object* v_h__1_246_, lean_object* v_h__2_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMapM_match__1_splitter(v_00_u03b2_238_, v_n_239_, v_00_u03b2_x27_240_, v_f_241_, v_inst_242_, v_out_243_, v_motive_244_, v_____do__lift_245_, v_h__1_246_, v_h__2_247_);
lean_dec(v_out_243_);
lean_dec(v_inst_242_);
lean_dec(v_f_241_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_){
_start:
{
if (v_____do__lift_249_ == 0)
{
lean_object* v___x_252_; 
lean_dec(v_h__2_251_);
v___x_252_ = lean_apply_1(v_h__1_250_, lean_box(0));
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
lean_dec(v_h__1_250_);
v___x_253_ = lean_apply_1(v_h__2_251_, lean_box(0));
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_254_, lean_object* v_h__1_255_, lean_object* v_h__2_256_){
_start:
{
uint8_t v_____do__lift_74__boxed_257_; lean_object* v_res_258_; 
v_____do__lift_74__boxed_257_ = lean_unbox(v_____do__lift_254_);
v_res_258_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_257_, v_h__1_255_, v_h__2_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(lean_object* v_00_u03b2_259_, lean_object* v_n_260_, lean_object* v_f_261_, lean_object* v_inst_262_, lean_object* v_out_263_, lean_object* v_motive_264_, uint8_t v_____do__lift_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
if (v_____do__lift_265_ == 0)
{
lean_object* v___x_268_; 
lean_dec(v_h__2_267_);
v___x_268_ = lean_apply_1(v_h__1_266_, lean_box(0));
return v___x_268_;
}
else
{
lean_object* v___x_269_; 
lean_dec(v_h__1_266_);
v___x_269_ = lean_apply_1(v_h__2_267_, lean_box(0));
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_270_, lean_object* v_n_271_, lean_object* v_f_272_, lean_object* v_inst_273_, lean_object* v_out_274_, lean_object* v_motive_275_, lean_object* v_____do__lift_276_, lean_object* v_h__1_277_, lean_object* v_h__2_278_){
_start:
{
uint8_t v_____do__lift_82__boxed_279_; lean_object* v_res_280_; 
v_____do__lift_82__boxed_279_ = lean_unbox(v_____do__lift_276_);
v_res_280_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterM_match__1_splitter(v_00_u03b2_270_, v_n_271_, v_f_272_, v_inst_273_, v_out_274_, v_motive_275_, v_____do__lift_82__boxed_279_, v_h__1_277_, v_h__2_278_);
lean_dec(v_out_274_);
lean_dec(v_inst_273_);
lean_dec(v_f_272_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(uint8_t v_____do__lift_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_){
_start:
{
if (v_____do__lift_281_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v_h__2_283_);
v___x_284_ = lean_apply_1(v_h__1_282_, lean_box(0));
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
lean_dec(v_h__1_282_);
v___x_285_ = lean_apply_1(v_h__2_283_, lean_box(0));
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
uint8_t v_____do__lift_74__boxed_289_; lean_object* v_res_290_; 
v_____do__lift_74__boxed_289_ = lean_unbox(v_____do__lift_286_);
v_res_290_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___redArg(v_____do__lift_74__boxed_289_, v_h__1_287_, v_h__2_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(lean_object* v_00_u03b2_291_, lean_object* v_n_292_, lean_object* v_f_293_, lean_object* v_inst_294_, lean_object* v_out_295_, lean_object* v_motive_296_, uint8_t v_____do__lift_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_){
_start:
{
if (v_____do__lift_297_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v_h__2_299_);
v___x_300_ = lean_apply_1(v_h__1_298_, lean_box(0));
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
lean_dec(v_h__1_298_);
v___x_301_ = lean_apply_1(v_h__2_299_, lean_box(0));
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter___boxed(lean_object* v_00_u03b2_302_, lean_object* v_n_303_, lean_object* v_f_304_, lean_object* v_inst_305_, lean_object* v_out_306_, lean_object* v_motive_307_, lean_object* v_____do__lift_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_){
_start:
{
uint8_t v_____do__lift_82__boxed_311_; lean_object* v_res_312_; 
v_____do__lift_82__boxed_311_ = lean_unbox(v_____do__lift_308_);
v_res_312_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterM_match__1_splitter(v_00_u03b2_302_, v_n_303_, v_f_304_, v_inst_305_, v_out_306_, v_motive_307_, v_____do__lift_82__boxed_311_, v_h__1_309_, v_h__2_310_);
lean_dec(v_out_306_);
lean_dec(v_inst_305_);
lean_dec(v_f_304_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter___redArg(lean_object* v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_316_; 
lean_dec(v_h__2_315_);
v___x_316_ = lean_apply_1(v_h__1_314_, lean_box(0));
return v___x_316_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; 
lean_dec(v_h__1_314_);
v_val_317_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v_x_313_);
v___x_318_ = lean_apply_2(v_h__2_315_, v_val_317_, lean_box(0));
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_step__filterMap_match__1_splitter(lean_object* v_00_u03b2_x27_319_, lean_object* v_motive_320_, lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_){
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
lean_dec_ref(v_x_321_);
v___x_326_ = lean_apply_2(v_h__2_323_, v_val_325_, lean_box(0));
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter___redArg(lean_object* v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v___x_330_; 
lean_dec(v_h__2_329_);
v___x_330_ = lean_apply_1(v_h__1_328_, lean_box(0));
return v___x_330_;
}
else
{
lean_object* v_val_331_; lean_object* v___x_332_; 
lean_dec(v_h__1_328_);
v_val_331_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_val_331_);
lean_dec_ref(v_x_327_);
v___x_332_ = lean_apply_2(v_h__2_329_, v_val_331_, lean_box(0));
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_step__filterMap_match__1_splitter(lean_object* v_00_u03b3_333_, lean_object* v_motive_334_, lean_object* v_x_335_, lean_object* v_h__1_336_, lean_object* v_h__2_337_){
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
lean_dec_ref(v_x_335_);
v___x_340_ = lean_apply_2(v_h__2_337_, v_val_339_, lean_box(0));
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter___redArg(lean_object* v_x_341_, lean_object* v_h__1_342_, lean_object* v_h__2_343_, lean_object* v_h__3_344_){
_start:
{
switch(lean_obj_tag(v_x_341_))
{
case 0:
{
lean_object* v_it_345_; lean_object* v_out_346_; lean_object* v___x_347_; 
lean_dec(v_h__3_344_);
lean_dec(v_h__2_343_);
v_it_345_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_it_345_);
v_out_346_ = lean_ctor_get(v_x_341_, 1);
lean_inc(v_out_346_);
lean_dec_ref(v_x_341_);
v___x_347_ = lean_apply_2(v_h__1_342_, v_it_345_, v_out_346_);
return v___x_347_;
}
case 1:
{
lean_object* v_it_348_; lean_object* v___x_349_; 
lean_dec(v_h__3_344_);
lean_dec(v_h__1_342_);
v_it_348_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_it_348_);
lean_dec_ref(v_x_341_);
v___x_349_ = lean_apply_1(v_h__2_343_, v_it_348_);
return v___x_349_;
}
default: 
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_h__2_343_);
lean_dec(v_h__1_342_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_apply_1(v_h__3_344_, v___x_350_);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__3_splitter(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_motive_354_, lean_object* v_x_355_, lean_object* v_h__1_356_, lean_object* v_h__2_357_, lean_object* v_h__3_358_){
_start:
{
switch(lean_obj_tag(v_x_355_))
{
case 0:
{
lean_object* v_it_359_; lean_object* v_out_360_; lean_object* v___x_361_; 
lean_dec(v_h__3_358_);
lean_dec(v_h__2_357_);
v_it_359_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_it_359_);
v_out_360_ = lean_ctor_get(v_x_355_, 1);
lean_inc(v_out_360_);
lean_dec_ref(v_x_355_);
v___x_361_ = lean_apply_2(v_h__1_356_, v_it_359_, v_out_360_);
return v___x_361_;
}
case 1:
{
lean_object* v_it_362_; lean_object* v___x_363_; 
lean_dec(v_h__3_358_);
lean_dec(v_h__1_356_);
v_it_362_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_it_362_);
lean_dec_ref(v_x_355_);
v___x_363_ = lean_apply_1(v_h__2_357_, v_it_362_);
return v___x_363_;
}
default: 
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_h__2_357_);
lean_dec(v_h__1_356_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_apply_1(v_h__3_358_, v___x_364_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter___redArg(lean_object* v_x_366_, lean_object* v_h__1_367_, lean_object* v_h__2_368_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec(v_h__2_368_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_apply_1(v_h__1_367_, v___x_369_);
return v___x_370_;
}
else
{
lean_object* v_val_371_; lean_object* v___x_372_; 
lean_dec(v_h__1_367_);
v_val_371_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v_x_366_);
v___x_372_ = lean_apply_1(v_h__2_368_, v_val_371_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_val__step__filterMap_match__1_splitter(lean_object* v_00_u03b3_373_, lean_object* v_motive_374_, lean_object* v_x_375_, lean_object* v_h__1_376_, lean_object* v_h__2_377_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_h__2_377_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_apply_1(v_h__1_376_, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v_val_380_; lean_object* v___x_381_; 
lean_dec(v_h__1_376_);
v_val_380_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_val_380_);
lean_dec_ref(v_x_375_);
v___x_381_ = lean_apply_1(v_h__2_377_, v_val_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_){
_start:
{
if (lean_obj_tag(v_____do__lift_382_) == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_h__1_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_apply_1(v_h__2_384_, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; 
lean_dec(v_h__2_384_);
v_val_387_ = lean_ctor_get(v_____do__lift_382_, 0);
lean_inc(v_val_387_);
lean_dec_ref(v_____do__lift_382_);
v___x_388_ = lean_apply_1(v_h__1_383_, v_val_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_389_, lean_object* v_motive_390_, lean_object* v_____do__lift_391_, lean_object* v_h__1_392_, lean_object* v_h__2_393_){
_start:
{
if (lean_obj_tag(v_____do__lift_391_) == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v_h__1_392_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_apply_1(v_h__2_393_, v___x_394_);
return v___x_395_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_397_; 
lean_dec(v_h__2_393_);
v_val_396_ = lean_ctor_get(v_____do__lift_391_, 0);
lean_inc(v_val_396_);
lean_dec_ref(v_____do__lift_391_);
v___x_397_ = lean_apply_1(v_h__1_392_, v_val_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____do__lift_398_, lean_object* v_h__1_399_, lean_object* v_h__2_400_){
_start:
{
if (lean_obj_tag(v_____do__lift_398_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_h__1_399_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_apply_1(v_h__2_400_, v___x_401_);
return v___x_402_;
}
else
{
lean_object* v_val_403_; lean_object* v___x_404_; 
lean_dec(v_h__2_400_);
v_val_403_ = lean_ctor_get(v_____do__lift_398_, 0);
lean_inc(v_val_403_);
lean_dec_ref(v_____do__lift_398_);
v___x_404_ = lean_apply_1(v_h__1_399_, v_val_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b2_u2082_405_, lean_object* v_motive_406_, lean_object* v_____do__lift_407_, lean_object* v_h__1_408_, lean_object* v_h__2_409_){
_start:
{
if (lean_obj_tag(v_____do__lift_407_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_h__1_408_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_apply_1(v_h__2_409_, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_413_; 
lean_dec(v_h__2_409_);
v_val_412_ = lean_ctor_get(v_____do__lift_407_, 0);
lean_inc(v_val_412_);
lean_dec_ref(v_____do__lift_407_);
v___x_413_ = lean_apply_1(v_h__1_408_, v_val_412_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_414_, lean_object* v_h__1_415_, lean_object* v_h__2_416_){
_start:
{
if (lean_obj_tag(v_____x_414_) == 1)
{
lean_object* v_val_417_; lean_object* v___x_418_; 
lean_dec(v_h__2_416_);
v_val_417_ = lean_ctor_get(v_____x_414_, 0);
lean_inc(v_val_417_);
lean_dec_ref(v_____x_414_);
v___x_418_ = lean_apply_1(v_h__1_415_, v_val_417_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; 
lean_dec(v_h__1_415_);
v___x_419_ = lean_apply_2(v_h__2_416_, v_____x_414_, lean_box(0));
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_420_, lean_object* v_motive_421_, lean_object* v_____x_422_, lean_object* v_h__1_423_, lean_object* v_h__2_424_){
_start:
{
if (lean_obj_tag(v_____x_422_) == 1)
{
lean_object* v_val_425_; lean_object* v___x_426_; 
lean_dec(v_h__2_424_);
v_val_425_ = lean_ctor_get(v_____x_422_, 0);
lean_inc(v_val_425_);
lean_dec_ref(v_____x_422_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter___redArg(lean_object* v_____x_428_, lean_object* v_h__1_429_, lean_object* v_h__2_430_){
_start:
{
if (lean_obj_tag(v_____x_428_) == 1)
{
lean_object* v_val_431_; lean_object* v___x_432_; 
lean_dec(v_h__2_430_);
v_val_431_ = lean_ctor_get(v_____x_428_, 0);
lean_inc(v_val_431_);
lean_dec_ref(v_____x_428_);
v___x_432_ = lean_apply_1(v_h__1_429_, v_val_431_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
lean_dec(v_h__1_429_);
v___x_433_ = lean_apply_2(v_h__2_430_, v_____x_428_, lean_box(0));
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_foldM__filterMapWithPostcondition_match__1_splitter(lean_object* v_00_u03b3_434_, lean_object* v_motive_435_, lean_object* v_____x_436_, lean_object* v_h__1_437_, lean_object* v_h__2_438_){
_start:
{
if (lean_obj_tag(v_____x_436_) == 1)
{
lean_object* v_val_439_; lean_object* v___x_440_; 
lean_dec(v_h__2_438_);
v_val_439_ = lean_ctor_get(v_____x_436_, 0);
lean_inc(v_val_439_);
lean_dec_ref(v_____x_436_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_){
_start:
{
if (lean_obj_tag(v_____do__lift_442_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
lean_dec(v_h__1_443_);
v_a_445_ = lean_ctor_get(v_____do__lift_442_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v_____do__lift_442_);
v___x_446_ = lean_apply_1(v_h__2_444_, v_a_445_);
return v___x_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; 
lean_dec(v_h__2_444_);
v_a_447_ = lean_ctor_get(v_____do__lift_442_, 0);
lean_inc(v_a_447_);
lean_dec_ref(v_____do__lift_442_);
v___x_448_ = lean_apply_1(v_h__1_443_, v_a_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_449_, lean_object* v_motive_450_, lean_object* v_____do__lift_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
if (lean_obj_tag(v_____do__lift_451_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; 
lean_dec(v_h__1_452_);
v_a_454_ = lean_ctor_get(v_____do__lift_451_, 0);
lean_inc(v_a_454_);
lean_dec_ref(v_____do__lift_451_);
v___x_455_ = lean_apply_1(v_h__2_453_, v_a_454_);
return v___x_455_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_457_; 
lean_dec(v_h__2_453_);
v_a_456_ = lean_ctor_get(v_____do__lift_451_, 0);
lean_inc(v_a_456_);
lean_dec_ref(v_____do__lift_451_);
v___x_457_ = lean_apply_1(v_h__1_452_, v_a_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_458_, lean_object* v_h__1_459_, lean_object* v_h__2_460_, lean_object* v_h__3_461_){
_start:
{
switch(lean_obj_tag(v_x_458_))
{
case 0:
{
lean_object* v_it_462_; lean_object* v_out_463_; lean_object* v___x_464_; 
lean_dec(v_h__3_461_);
lean_dec(v_h__2_460_);
v_it_462_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_it_462_);
v_out_463_ = lean_ctor_get(v_x_458_, 1);
lean_inc(v_out_463_);
lean_dec_ref(v_x_458_);
v___x_464_ = lean_apply_3(v_h__1_459_, v_it_462_, v_out_463_, lean_box(0));
return v___x_464_;
}
case 1:
{
lean_object* v_it_465_; lean_object* v___x_466_; 
lean_dec(v_h__3_461_);
lean_dec(v_h__1_459_);
v_it_465_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_it_465_);
lean_dec_ref(v_x_458_);
v___x_466_ = lean_apply_2(v_h__2_460_, v_it_465_, lean_box(0));
return v___x_466_;
}
default: 
{
lean_object* v___x_467_; 
lean_dec(v_h__2_460_);
lean_dec(v_h__1_459_);
v___x_467_ = lean_apply_1(v_h__3_461_, lean_box(0));
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_m_470_, lean_object* v_inst_471_, lean_object* v_it_472_, lean_object* v_motive_473_, lean_object* v_x_474_, lean_object* v_h__1_475_, lean_object* v_h__2_476_, lean_object* v_h__3_477_){
_start:
{
switch(lean_obj_tag(v_x_474_))
{
case 0:
{
lean_object* v_it_478_; lean_object* v_out_479_; lean_object* v___x_480_; 
lean_dec(v_h__3_477_);
lean_dec(v_h__2_476_);
v_it_478_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_it_478_);
v_out_479_ = lean_ctor_get(v_x_474_, 1);
lean_inc(v_out_479_);
lean_dec_ref(v_x_474_);
v___x_480_ = lean_apply_3(v_h__1_475_, v_it_478_, v_out_479_, lean_box(0));
return v___x_480_;
}
case 1:
{
lean_object* v_it_481_; lean_object* v___x_482_; 
lean_dec(v_h__3_477_);
lean_dec(v_h__1_475_);
v_it_481_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_it_481_);
lean_dec_ref(v_x_474_);
v___x_482_ = lean_apply_2(v_h__2_476_, v_it_481_, lean_box(0));
return v___x_482_;
}
default: 
{
lean_object* v___x_483_; 
lean_dec(v_h__2_476_);
lean_dec(v_h__1_475_);
v___x_483_ = lean_apply_1(v_h__3_477_, lean_box(0));
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_m_486_, lean_object* v_inst_487_, lean_object* v_it_488_, lean_object* v_motive_489_, lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_, lean_object* v_h__3_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_484_, v_00_u03b2_485_, v_m_486_, v_inst_487_, v_it_488_, v_motive_489_, v_x_490_, v_h__1_491_, v_h__2_492_, v_h__3_493_);
lean_dec(v_it_488_);
lean_dec(v_inst_487_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_495_, lean_object* v_h__1_496_, lean_object* v_h__2_497_){
_start:
{
if (lean_obj_tag(v_____do__lift_495_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; 
lean_dec(v_h__1_496_);
v_a_498_ = lean_ctor_get(v_____do__lift_495_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v_____do__lift_495_);
v___x_499_ = lean_apply_1(v_h__2_497_, v_a_498_);
return v___x_499_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_501_; 
lean_dec(v_h__2_497_);
v_a_500_ = lean_ctor_get(v_____do__lift_495_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v_____do__lift_495_);
v___x_501_ = lean_apply_1(v_h__1_496_, v_a_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b3_502_, lean_object* v_motive_503_, lean_object* v_____do__lift_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
if (lean_obj_tag(v_____do__lift_504_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
lean_dec(v_h__1_505_);
v_a_507_ = lean_ctor_get(v_____do__lift_504_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v_____do__lift_504_);
v___x_508_ = lean_apply_1(v_h__2_506_, v_a_507_);
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_510_; 
lean_dec(v_h__2_506_);
v_a_509_ = lean_ctor_get(v_____do__lift_504_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v_____do__lift_504_);
v___x_510_ = lean_apply_1(v_h__1_505_, v_a_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_, lean_object* v_h__3_514_){
_start:
{
switch(lean_obj_tag(v_x_511_))
{
case 0:
{
lean_object* v_it_515_; lean_object* v_out_516_; lean_object* v___x_517_; 
lean_dec(v_h__3_514_);
lean_dec(v_h__2_513_);
v_it_515_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_it_515_);
v_out_516_ = lean_ctor_get(v_x_511_, 1);
lean_inc(v_out_516_);
lean_dec_ref(v_x_511_);
v___x_517_ = lean_apply_2(v_h__1_512_, v_it_515_, v_out_516_);
return v___x_517_;
}
case 1:
{
lean_object* v_it_518_; lean_object* v___x_519_; 
lean_dec(v_h__3_514_);
lean_dec(v_h__1_512_);
v_it_518_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_it_518_);
lean_dec_ref(v_x_511_);
v___x_519_ = lean_apply_1(v_h__2_513_, v_it_518_);
return v___x_519_;
}
default: 
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_h__2_513_);
lean_dec(v_h__1_512_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_h__3_514_, v___x_520_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_FilterMap_0__Std_Iter_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_522_, lean_object* v_00_u03b2_523_, lean_object* v_motive_524_, lean_object* v_x_525_, lean_object* v_h__1_526_, lean_object* v_h__2_527_, lean_object* v_h__3_528_){
_start:
{
switch(lean_obj_tag(v_x_525_))
{
case 0:
{
lean_object* v_it_529_; lean_object* v_out_530_; lean_object* v___x_531_; 
lean_dec(v_h__3_528_);
lean_dec(v_h__2_527_);
v_it_529_ = lean_ctor_get(v_x_525_, 0);
lean_inc(v_it_529_);
v_out_530_ = lean_ctor_get(v_x_525_, 1);
lean_inc(v_out_530_);
lean_dec_ref(v_x_525_);
v___x_531_ = lean_apply_2(v_h__1_526_, v_it_529_, v_out_530_);
return v___x_531_;
}
case 1:
{
lean_object* v_it_532_; lean_object* v___x_533_; 
lean_dec(v_h__3_528_);
lean_dec(v_h__1_526_);
v_it_532_ = lean_ctor_get(v_x_525_, 0);
lean_inc(v_it_532_);
lean_dec_ref(v_x_525_);
v___x_533_ = lean_apply_1(v_h__2_527_, v_it_532_);
return v___x_533_;
}
default: 
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_h__2_527_);
lean_dec(v_h__1_526_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_apply_1(v_h__3_528_, v___x_534_);
return v___x_535_;
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
