// Lean compiler output
// Module: Init.Data.ByteArray.Lemmas
// Imports: public import Init.Data.ByteArray.Basic import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Array.Extract import Init.Data.Array.Lemmas import Init.Omega
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
lean_object* lean_byte_array_data(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, uint8_t v_x_3_, lean_object* v_h__1_4_){
_start:
{
lean_object* v_data_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_data_5_ = lean_byte_array_data(v_x_1_);
v___x_6_ = lean_box(v_x_3_);
v___x_7_ = lean_apply_4(v_h__1_4_, v_data_5_, v_x_2_, v___x_6_, lean_box(0));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg___boxed(lean_object* v_x_8_, lean_object* v_x_9_, lean_object* v_x_10_, lean_object* v_h__1_11_){
_start:
{
uint8_t v_x_33__boxed_12_; lean_object* v_res_13_; 
v_x_33__boxed_12_ = lean_unbox(v_x_10_);
v_res_13_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(v_x_8_, v_x_9_, v_x_33__boxed_12_, v_h__1_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_x_16_, uint8_t v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_){
_start:
{
lean_object* v_data_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_data_20_ = lean_byte_array_data(v_x_15_);
v___x_21_ = lean_box(v_x_17_);
v___x_22_ = lean_apply_4(v_h__1_19_, v_data_20_, v_x_16_, v___x_21_, lean_box(0));
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_x_26_, lean_object* v_x_27_, lean_object* v_h__1_28_){
_start:
{
uint8_t v_x_48__boxed_29_; lean_object* v_res_30_; 
v_x_48__boxed_29_ = lean_unbox(v_x_26_);
v_res_30_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(v_motive_23_, v_x_24_, v_x_25_, v_x_48__boxed_29_, v_x_27_, v_h__1_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter___redArg(lean_object* v_x_31_, lean_object* v_h__1_32_){
_start:
{
lean_object* v_data_33_; lean_object* v___x_34_; 
v_data_33_ = lean_byte_array_data(v_x_31_);
v___x_34_ = lean_apply_1(v_h__1_32_, v_data_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter(lean_object* v_motive_35_, lean_object* v_x_36_, lean_object* v_h__1_37_){
_start:
{
lean_object* v_data_38_; lean_object* v___x_39_; 
v_data_38_ = lean_byte_array_data(v_x_36_);
v___x_39_ = lean_apply_1(v_h__1_37_, v_data_38_);
return v___x_39_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Extract(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Extract(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ByteArray_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
