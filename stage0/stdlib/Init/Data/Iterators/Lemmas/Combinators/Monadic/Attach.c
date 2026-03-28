// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Attach
// Imports: public import Init.Data.Iterators.Combinators.Monadic.Attach import all Init.Data.Iterators.Combinators.Monadic.Attach public import Init.Data.Iterators.Consumers.Monadic.Collect public import Init.Data.List.Attach import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop import Init.Data.Iterators.Lemmas.Monadic.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_m_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(lean_object* v_step_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_, lean_object* v_h__3_30_){
_start:
{
switch(lean_obj_tag(v_step_27_))
{
case 0:
{
lean_object* v_it_31_; lean_object* v_out_32_; lean_object* v___x_33_; 
lean_dec(v_h__3_30_);
lean_dec(v_h__2_29_);
v_it_31_ = lean_ctor_get(v_step_27_, 0);
lean_inc(v_it_31_);
v_out_32_ = lean_ctor_get(v_step_27_, 1);
lean_inc(v_out_32_);
lean_dec_ref(v_step_27_);
v___x_33_ = lean_apply_3(v_h__1_28_, v_it_31_, v_out_32_, lean_box(0));
return v___x_33_;
}
case 1:
{
lean_object* v_it_34_; lean_object* v___x_35_; 
lean_dec(v_h__3_30_);
lean_dec(v_h__1_28_);
v_it_34_ = lean_ctor_get(v_step_27_, 0);
lean_inc(v_it_34_);
lean_dec_ref(v_step_27_);
v___x_35_ = lean_apply_2(v_h__2_29_, v_it_34_, lean_box(0));
return v___x_35_;
}
default: 
{
lean_object* v___x_36_; 
lean_dec(v_h__2_29_);
lean_dec(v_h__1_28_);
v___x_36_ = lean_apply_1(v_h__3_30_, lean_box(0));
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(lean_object* v_00_u03b1_37_, lean_object* v_m_38_, lean_object* v_00_u03b2_39_, lean_object* v_inst_40_, lean_object* v_P_41_, lean_object* v_it_42_, lean_object* v_motive_43_, lean_object* v_step_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
_start:
{
switch(lean_obj_tag(v_step_44_))
{
case 0:
{
lean_object* v_it_48_; lean_object* v_out_49_; lean_object* v___x_50_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__2_46_);
v_it_48_ = lean_ctor_get(v_step_44_, 0);
lean_inc(v_it_48_);
v_out_49_ = lean_ctor_get(v_step_44_, 1);
lean_inc(v_out_49_);
lean_dec_ref(v_step_44_);
v___x_50_ = lean_apply_3(v_h__1_45_, v_it_48_, v_out_49_, lean_box(0));
return v___x_50_;
}
case 1:
{
lean_object* v_it_51_; lean_object* v___x_52_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__1_45_);
v_it_51_ = lean_ctor_get(v_step_44_, 0);
lean_inc(v_it_51_);
lean_dec_ref(v_step_44_);
v___x_52_ = lean_apply_2(v_h__2_46_, v_it_51_, lean_box(0));
return v___x_52_;
}
default: 
{
lean_object* v___x_53_; 
lean_dec(v_h__2_46_);
lean_dec(v_h__1_45_);
v___x_53_ = lean_apply_1(v_h__3_47_, lean_box(0));
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(lean_object* v_00_u03b1_54_, lean_object* v_m_55_, lean_object* v_00_u03b2_56_, lean_object* v_inst_57_, lean_object* v_P_58_, lean_object* v_it_59_, lean_object* v_motive_60_, lean_object* v_step_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(v_00_u03b1_54_, v_m_55_, v_00_u03b2_56_, v_inst_57_, v_P_58_, v_it_59_, v_motive_60_, v_step_61_, v_h__1_62_, v_h__2_63_, v_h__3_64_);
lean_dec(v_it_59_);
lean_dec(v_inst_57_);
return v_res_65_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin);
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
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
