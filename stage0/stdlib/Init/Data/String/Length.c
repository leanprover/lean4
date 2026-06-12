// Lean compiler output
// Module: Init.Data.String.Length
// Imports: public import Init.Data.String.Basic import Init.Data.Char.Lemmas
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
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object* v_b_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_string_length(v_b_2_);
lean_dec_ref(v_b_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg(lean_object* v_x_4_, lean_object* v_x_5_, lean_object* v_h__1_6_, lean_object* v_h__2_7_){
_start:
{
lean_object* v_zero_8_; uint8_t v_isZero_9_; 
v_zero_8_ = lean_unsigned_to_nat(0u);
v_isZero_9_ = lean_nat_dec_eq(v_x_4_, v_zero_8_);
if (v_isZero_9_ == 1)
{
lean_object* v___x_10_; 
lean_dec(v_h__2_7_);
v___x_10_ = lean_apply_1(v_h__1_6_, v_x_5_);
return v___x_10_;
}
else
{
lean_object* v_one_11_; lean_object* v_n_12_; lean_object* v___x_13_; 
lean_dec(v_h__1_6_);
v_one_11_ = lean_unsigned_to_nat(1u);
v_n_12_ = lean_nat_sub(v_x_4_, v_one_11_);
v___x_13_ = lean_apply_2(v_h__2_7_, v_n_12_, v_x_5_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg(v_x_14_, v_x_15_, v_h__1_16_, v_h__2_17_);
lean_dec(v_x_14_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter(lean_object* v_00_u03b1_19_, lean_object* v_motive_20_, lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
lean_object* v_zero_25_; uint8_t v_isZero_26_; 
v_zero_25_ = lean_unsigned_to_nat(0u);
v_isZero_26_ = lean_nat_dec_eq(v_x_21_, v_zero_25_);
if (v_isZero_26_ == 1)
{
lean_object* v___x_27_; 
lean_dec(v_h__2_24_);
v___x_27_ = lean_apply_1(v_h__1_23_, v_x_22_);
return v___x_27_;
}
else
{
lean_object* v_one_28_; lean_object* v_n_29_; lean_object* v___x_30_; 
lean_dec(v_h__1_23_);
v_one_28_ = lean_unsigned_to_nat(1u);
v_n_29_ = lean_nat_sub(v_x_21_, v_one_28_);
v___x_30_ = lean_apply_2(v_h__2_24_, v_n_29_, v_x_22_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___boxed(lean_object* v_00_u03b1_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter(v_00_u03b1_31_, v_motive_32_, v_x_33_, v_x_34_, v_h__1_35_, v_h__2_36_);
lean_dec(v_x_33_);
return v_res_37_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Length(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Length(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Length(builtin);
}
#ifdef __cplusplus
}
#endif
