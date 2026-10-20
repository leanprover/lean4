// Lean compiler output
// Module: Init.Data.List.TakeDrop
// Imports: import all Init.Data.List.Basic public import Init.BinderPredicates public import Init.Ext import Init.ByCases import Init.Data.Bool import Init.Data.List.Lemmas import Init.Data.Nat.Div.Basic import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(uint8_t v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_8_, lean_object* v_h__1_9_, lean_object* v_h__2_10_){
_start:
{
uint8_t v_x_24__boxed_11_; lean_object* v_res_12_; 
v_x_24__boxed_11_ = lean_unbox(v_x_8_);
v_res_12_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_11_, v_h__1_9_, v_h__2_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(lean_object* v_motive_13_, uint8_t v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (v_x_14_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__2_16_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_16_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__1_15_, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
uint8_t v_x_35__boxed_25_; lean_object* v_res_26_; 
v_x_35__boxed_25_ = lean_unbox(v_x_22_);
v_res_26_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(v_motive_21_, v_x_35__boxed_25_, v_h__1_23_, v_h__2_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_28_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_apply_1(v_h__2_29_, v___x_30_);
return v___x_31_;
}
else
{
lean_object* v_val_32_; lean_object* v___x_33_; 
lean_dec(v_h__2_29_);
v_val_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_val_32_);
lean_dec_ref_known(v_x_27_, 1);
v___x_33_ = lean_apply_1(v_h__1_28_, v_val_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__2_38_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_38_);
v_val_41_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v_x_36_, 1);
v___x_42_ = lean_apply_1(v_h__1_37_, v_val_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_45_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_apply_1(v_h__1_44_, v___x_46_);
return v___x_47_;
}
else
{
lean_object* v_val_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_44_);
v_val_48_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_val_48_);
lean_dec_ref_known(v_x_43_, 1);
v___x_49_ = lean_apply_1(v_h__2_45_, v_val_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_54_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__1_53_, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v_val_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_53_);
v_val_57_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v_x_52_, 1);
v___x_58_ = lean_apply_1(v_h__2_54_, v_val_57_);
return v___x_58_;
}
}
}
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_TakeDrop(builtin);
}
#ifdef __cplusplus
}
#endif
