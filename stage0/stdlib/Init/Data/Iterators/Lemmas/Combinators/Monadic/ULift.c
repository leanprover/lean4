// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift
// Imports: public import Init.Data.Iterators.Combinators.Monadic.ULift import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop import Init.Data.Iterators.Lemmas.Monadic.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter(lean_object* v_00_u03b1_11_, lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_, v_h__3_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_m_23_, lean_object* v_00_u03b2_24_, lean_object* v_inst_25_, lean_object* v_it_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter(v_00_u03b1_22_, v_m_23_, v_00_u03b2_24_, v_inst_25_, v_it_26_, v_motive_27_, v_x_28_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
lean_dec(v_it_26_);
lean_dec(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter___redArg(lean_object* v_step_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
switch(lean_obj_tag(v_step_33_))
{
case 0:
{
lean_object* v_it_37_; lean_object* v_out_38_; lean_object* v___x_39_; 
lean_dec(v_h__3_36_);
lean_dec(v_h__2_35_);
v_it_37_ = lean_ctor_get(v_step_33_, 0);
lean_inc(v_it_37_);
v_out_38_ = lean_ctor_get(v_step_33_, 1);
lean_inc(v_out_38_);
lean_dec_ref(v_step_33_);
v___x_39_ = lean_apply_2(v_h__1_34_, v_it_37_, v_out_38_);
return v___x_39_;
}
case 1:
{
lean_object* v_it_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_36_);
lean_dec(v_h__1_34_);
v_it_40_ = lean_ctor_get(v_step_33_, 0);
lean_inc(v_it_40_);
lean_dec_ref(v_step_33_);
v___x_41_ = lean_apply_1(v_h__2_35_, v_it_40_);
return v___x_41_;
}
default: 
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_35_);
lean_dec(v_h__1_34_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_apply_1(v_h__3_36_, v___x_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_m_45_, lean_object* v_00_u03b2_46_, lean_object* v_motive_47_, lean_object* v_step_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter___redArg(v_step_48_, v_h__1_49_, v_h__2_50_, v_h__3_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_){
_start:
{
switch(lean_obj_tag(v_x_53_))
{
case 0:
{
lean_object* v_it_57_; lean_object* v_out_58_; lean_object* v___x_59_; 
lean_dec(v_h__3_56_);
lean_dec(v_h__2_55_);
v_it_57_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_it_57_);
v_out_58_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_out_58_);
lean_dec_ref(v_x_53_);
v___x_59_ = lean_apply_2(v_h__1_54_, v_it_57_, v_out_58_);
return v___x_59_;
}
case 1:
{
lean_object* v_it_60_; lean_object* v___x_61_; 
lean_dec(v_h__3_56_);
lean_dec(v_h__1_54_);
v_it_60_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_it_60_);
lean_dec_ref(v_x_53_);
v___x_61_ = lean_apply_1(v_h__2_55_, v_it_60_);
return v___x_61_;
}
default: 
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_55_);
lean_dec(v_h__1_54_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__3_56_, v___x_62_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_m_66_, lean_object* v_motive_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(v_x_68_, v_h__1_69_, v_h__2_70_, v_h__3_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_){
_start:
{
switch(lean_obj_tag(v_x_73_))
{
case 0:
{
lean_object* v_it_77_; lean_object* v_out_78_; lean_object* v___x_79_; 
lean_dec(v_h__3_76_);
lean_dec(v_h__2_75_);
v_it_77_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_it_77_);
v_out_78_ = lean_ctor_get(v_x_73_, 1);
lean_inc(v_out_78_);
lean_dec_ref(v_x_73_);
v___x_79_ = lean_apply_2(v_h__1_74_, v_it_77_, v_out_78_);
return v___x_79_;
}
case 1:
{
lean_object* v_it_80_; lean_object* v___x_81_; 
lean_dec(v_h__3_76_);
lean_dec(v_h__1_74_);
v_it_80_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_it_80_);
lean_dec_ref(v_x_73_);
v___x_81_ = lean_apply_1(v_h__2_75_, v_it_80_);
return v___x_81_;
}
default: 
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_75_);
lean_dec(v_h__1_74_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__3_76_, v___x_82_);
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_m_86_, lean_object* v_motive_87_, lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_, lean_object* v_h__3_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(v_x_88_, v_h__1_89_, v_h__2_90_, v_h__3_91_);
return v___x_92_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_ULift(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
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
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
}
#ifdef __cplusplus
}
#endif
