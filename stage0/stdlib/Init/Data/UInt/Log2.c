// Lean compiler output
// Module: Init.Data.UInt.Log2
// Imports: public import Init.Prelude import Init.Data.Fin.Log2 import Init.Data.UInt.BasicAux
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
uint8_t lean_uint8_log2(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_log2___boxed(lean_object*);
uint16_t lean_uint16_log2(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_log2___boxed(lean_object*);
uint32_t lean_uint32_log2(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_log2___boxed(lean_object*);
uint64_t lean_uint64_log2(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_log2___boxed(lean_object*);
size_t lean_usize_log2(size_t);
LEAN_EXPORT lean_object* l_USize_log2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_log2___boxed(lean_object* v_a_2_){
_start:
{
uint8_t v_a_boxed_3_; uint8_t v_res_4_; lean_object* v_r_5_; 
v_a_boxed_3_ = lean_unbox(v_a_2_);
v_res_4_ = lean_uint8_log2(v_a_boxed_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_UInt16_log2___boxed(lean_object* v_a_7_){
_start:
{
uint16_t v_a_boxed_8_; uint16_t v_res_9_; lean_object* v_r_10_; 
v_a_boxed_8_ = lean_unbox(v_a_7_);
v_res_9_ = lean_uint16_log2(v_a_boxed_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l_UInt32_log2___boxed(lean_object* v_a_12_){
_start:
{
uint32_t v_a_boxed_13_; uint32_t v_res_14_; lean_object* v_r_15_; 
v_a_boxed_13_ = lean_unbox_uint32(v_a_12_);
lean_dec(v_a_12_);
v_res_14_ = lean_uint32_log2(v_a_boxed_13_);
v_r_15_ = lean_box_uint32(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_UInt64_log2___boxed(lean_object* v_a_17_){
_start:
{
uint64_t v_a_boxed_18_; uint64_t v_res_19_; lean_object* v_r_20_; 
v_a_boxed_18_ = lean_unbox_uint64(v_a_17_);
lean_dec_ref(v_a_17_);
v_res_19_ = lean_uint64_log2(v_a_boxed_18_);
v_r_20_ = lean_box_uint64(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_USize_log2___boxed(lean_object* v_a_22_){
_start:
{
size_t v_a_boxed_23_; size_t v_res_24_; lean_object* v_r_25_; 
v_a_boxed_23_ = lean_unbox_usize(v_a_22_);
lean_dec(v_a_22_);
v_res_24_ = lean_usize_log2(v_a_boxed_23_);
v_r_25_ = lean_box_usize(v_res_24_);
return v_r_25_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_Log2(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_UInt_Log2(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Log2(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt_Log2(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_UInt_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_UInt_Log2(builtin);
}
#ifdef __cplusplus
}
#endif
