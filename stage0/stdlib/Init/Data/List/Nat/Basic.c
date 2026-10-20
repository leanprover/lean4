// Lean compiler output
// Module: Init.Data.List.Nat.Basic
// Imports: public import Init.Data.List.MinMax import Init.Data.Bool import Init.Data.List.Count import Init.Data.Nat.Lemmas import Init.Data.Nat.Internal.Linear import Init.Data.Nat.MinMax import Init.Data.Option.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__1_11_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__2_12_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__2_19_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_18_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_tail_23_; 
lean_dec(v_h__1_18_);
v_tail_23_ = lean_ctor_get(v_x_17_, 1);
if (lean_obj_tag(v_tail_23_) == 0)
{
lean_object* v_head_24_; lean_object* v___x_25_; 
lean_dec(v_h__3_20_);
v_head_24_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_head_24_);
lean_dec_ref_known(v_x_17_, 2);
v___x_25_ = lean_apply_1(v_h__2_19_, v_head_24_);
return v___x_25_;
}
else
{
lean_object* v_head_26_; lean_object* v___x_27_; 
lean_inc(v_tail_23_);
lean_dec(v_h__2_19_);
v_head_26_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_head_26_);
lean_dec_ref_known(v_x_17_, 2);
v___x_27_ = lean_apply_3(v_h__3_20_, v_head_26_, v_tail_23_, lean_box(0));
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_, lean_object* v_h__3_33_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__3_33_);
lean_dec(v_h__2_32_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__1_31_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_tail_36_; 
lean_dec(v_h__1_31_);
v_tail_36_ = lean_ctor_get(v_x_30_, 1);
if (lean_obj_tag(v_tail_36_) == 0)
{
lean_object* v_head_37_; lean_object* v___x_38_; 
lean_dec(v_h__3_33_);
v_head_37_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_head_37_);
lean_dec_ref_known(v_x_30_, 2);
v___x_38_ = lean_apply_1(v_h__2_32_, v_head_37_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v___x_40_; 
lean_inc(v_tail_36_);
lean_dec(v_h__2_32_);
v_head_39_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_head_39_);
lean_dec_ref_known(v_x_30_, 2);
v___x_40_ = lean_apply_3(v_h__3_33_, v_head_39_, v_tail_36_, lean_box(0));
return v___x_40_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
