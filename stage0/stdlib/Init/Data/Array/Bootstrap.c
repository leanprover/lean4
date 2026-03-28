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
lean_object* v_zero_19_; uint8_t v_isZero_20_; 
v_zero_19_ = lean_unsigned_to_nat(0u);
v_isZero_20_ = lean_nat_dec_eq(v_i_16_, v_zero_19_);
if (v_isZero_20_ == 1)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_18_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_17_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_17_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_i_16_, v_one_23_);
v___x_25_ = lean_apply_1(v_h__2_18_, v_n_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___boxed(lean_object* v_motive_26_, lean_object* v_i_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(v_motive_26_, v_i_27_, v_h__1_28_, v_h__2_29_);
lean_dec(v_i_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_i_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_zero_34_; uint8_t v_isZero_35_; 
v_zero_34_ = lean_unsigned_to_nat(0u);
v_isZero_35_ = lean_nat_dec_eq(v_i_31_, v_zero_34_);
if (v_isZero_35_ == 1)
{
lean_object* v___x_36_; 
lean_dec(v_h__2_33_);
v___x_36_ = lean_apply_1(v_h__1_32_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v_one_37_; lean_object* v_n_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_32_);
v_one_37_ = lean_unsigned_to_nat(1u);
v_n_38_ = lean_nat_sub(v_i_31_, v_one_37_);
v___x_39_ = lean_apply_2(v_h__2_33_, v_n_38_, lean_box(0));
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* v_i_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_40_, v_h__1_41_, v_h__2_42_);
lean_dec(v_i_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b1_44_, lean_object* v_as_45_, lean_object* v_motive_46_, lean_object* v_i_47_, lean_object* v_h_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
lean_object* v_zero_51_; uint8_t v_isZero_52_; 
v_zero_51_ = lean_unsigned_to_nat(0u);
v_isZero_52_ = lean_nat_dec_eq(v_i_47_, v_zero_51_);
if (v_isZero_52_ == 1)
{
lean_object* v___x_53_; 
lean_dec(v_h__2_50_);
v___x_53_ = lean_apply_1(v_h__1_49_, lean_box(0));
return v___x_53_;
}
else
{
lean_object* v_one_54_; lean_object* v_n_55_; lean_object* v___x_56_; 
lean_dec(v_h__1_49_);
v_one_54_ = lean_unsigned_to_nat(1u);
v_n_55_ = lean_nat_sub(v_i_47_, v_one_54_);
v___x_56_ = lean_apply_2(v_h__2_50_, v_n_55_, lean_box(0));
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_57_, lean_object* v_as_58_, lean_object* v_motive_59_, lean_object* v_i_60_, lean_object* v_h_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_57_, v_as_58_, v_motive_59_, v_i_60_, v_h_61_, v_h__1_62_, v_h__2_63_);
lean_dec(v_i_60_);
lean_dec_ref(v_as_58_);
return v_res_64_;
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
