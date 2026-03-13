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
uint8_t v_x_31__boxed_12_; lean_object* v_res_13_; 
v_x_31__boxed_12_ = lean_unbox(v_x_10_);
v_res_13_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(v_x_8_, v_x_9_, v_x_31__boxed_12_, v_h__1_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_x_16_, uint8_t v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(v_x_15_, v_x_16_, v_x_17_, v_h__1_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(lean_object* v_motive_21_, lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_h__1_26_){
_start:
{
uint8_t v_x_46__boxed_27_; lean_object* v_res_28_; 
v_x_46__boxed_27_ = lean_unbox(v_x_24_);
v_res_28_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(v_motive_21_, v_x_22_, v_x_23_, v_x_46__boxed_27_, v_x_25_, v_h__1_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter___redArg(lean_object* v_x_29_, lean_object* v_h__1_30_){
_start:
{
lean_object* v_data_31_; lean_object* v___x_32_; 
v_data_31_ = lean_byte_array_data(v_x_29_);
v___x_32_ = lean_apply_1(v_h__1_30_, v_data_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter(lean_object* v_motive_33_, lean_object* v_x_34_, lean_object* v_h__1_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter___redArg(v_x_34_, v_h__1_35_);
return v___x_36_;
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
