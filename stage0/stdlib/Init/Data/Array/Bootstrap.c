// Lean compiler output
// Module: Init.Data.Array.Bootstrap
// Imports: import all Init.Data.Array.Basic public import Init.Data.List.Control import Init.Data.List.Lemmas import Init.Data.List.TakeDrop
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(lean_object* v_i_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_i_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_2_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_i_1_, v_one_8_);
v___x_10_ = lean_apply_1(v_h__2_3_, v_n_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(lean_object* v_i_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_11_, v_h__1_12_, v_h__2_13_);
lean_dec(v_i_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(lean_object* v_motive_15_, lean_object* v_i_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(v_i_16_, v_h__1_17_, v_h__2_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_20_, lean_object* v_i_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(v_motive_20_, v_i_21_, v_h__1_22_, v_h__2_23_);
lean_dec(v_i_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_i_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_i_25_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_30_; 
lean_dec(v_h__2_27_);
v___x_30_ = lean_apply_1(v_h__1_26_, lean_box(0));
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_26_);
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_i_25_, v_one_31_);
v___x_33_ = lean_apply_2(v_h__2_27_, v_n_32_, lean_box(0));
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* v_i_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_34_, v_h__1_35_, v_h__2_36_);
lean_dec(v_i_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b1_38_, lean_object* v_as_39_, lean_object* v_motive_40_, lean_object* v_i_41_, lean_object* v_h_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_41_, v_h__1_43_, v_h__2_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_46_, lean_object* v_as_47_, lean_object* v_motive_48_, lean_object* v_i_49_, lean_object* v_h_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_46_, v_as_47_, v_motive_48_, v_i_49_, v_h_50_, v_h__1_51_, v_h__2_52_);
lean_dec(v_i_49_);
lean_dec_ref(v_as_47_);
return v_res_53_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Bootstrap(builtin);
}
#ifdef __cplusplus
}
#endif
