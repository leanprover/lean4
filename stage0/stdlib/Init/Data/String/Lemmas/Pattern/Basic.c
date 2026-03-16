// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Basic
// Imports: public import Init.Data.String.Pattern.Basic public import Init.Data.String.Lemmas.Splits public import Init.Data.Iterators.Consumers.Collect import all Init.Data.String.Pattern.Basic import Init.Data.String.OrderInstances import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Lemmas.Basic import Init.Data.String.Lemmas.Order import Init.Data.String.Termination import Init.Data.Order.Lemmas import Init.ByCases import Init.Data.Option.Lemmas import Init.Data.Iterators.Lemmas.Consumers.Collect
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_apply_1(v_h__2_3_, lean_box(0));
return v___x_4_;
}
else
{
lean_object* v_val_5_; lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v_val_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v_x_1_);
v___x_6_ = lean_apply_2(v_h__1_2_, v_val_5_, lean_box(0));
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter(lean_object* v_00_u03c1_7_, lean_object* v_pat_8_, lean_object* v_s_9_, lean_object* v_it_10_, lean_object* v_motive_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter___redArg(v_x_12_, v_h__1_13_, v_h__2_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter___boxed(lean_object* v_00_u03c1_16_, lean_object* v_pat_17_, lean_object* v_s_18_, lean_object* v_it_19_, lean_object* v_motive_20_, lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter(v_00_u03c1_16_, v_pat_17_, v_s_18_, v_it_19_, v_motive_20_, v_x_21_, v_h__1_22_, v_h__2_23_);
lean_dec(v_it_19_);
lean_dec_ref(v_s_18_);
lean_dec(v_pat_17_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_, lean_object* v_h__3_28_){
_start:
{
switch(lean_obj_tag(v_x_25_))
{
case 0:
{
lean_object* v_it_29_; lean_object* v_out_30_; lean_object* v___x_31_; 
lean_dec(v_h__3_28_);
lean_dec(v_h__2_27_);
v_it_29_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_it_29_);
v_out_30_ = lean_ctor_get(v_x_25_, 1);
lean_inc(v_out_30_);
lean_dec_ref(v_x_25_);
v___x_31_ = lean_apply_2(v_h__1_26_, v_it_29_, v_out_30_);
return v___x_31_;
}
case 1:
{
lean_object* v_it_32_; lean_object* v___x_33_; 
lean_dec(v_h__3_28_);
lean_dec(v_h__1_26_);
v_it_32_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_it_32_);
lean_dec_ref(v_x_25_);
v___x_33_ = lean_apply_1(v_h__2_27_, v_it_32_);
return v___x_33_;
}
default: 
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_27_);
lean_dec(v_h__1_26_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__3_28_, v___x_34_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_motive_38_, lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_, lean_object* v_h__3_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Init_Data_String_Lemmas_Pattern_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(v_x_39_, v_h__1_40_, v_h__2_41_, v_h__3_42_);
return v___x_43_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
