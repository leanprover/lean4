// Lean compiler output
// Module: Init.Data.Fin.Log2
// Imports: public import Init.Prelude import Init.Data.Nat.Log2
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
lean_object* lean_nat_log2(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___redArg(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_log2(v_n_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Fin_log2___redArg___boxed(lean_object* v_n_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Fin_log2___redArg(v_n_3_);
lean_dec(v_n_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Fin_log2(lean_object* v_m_5_, lean_object* v_n_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_nat_log2(v_n_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Fin_log2___boxed(lean_object* v_m_8_, lean_object* v_n_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Fin_log2(v_m_8_, v_n_9_);
lean_dec(v_n_9_);
lean_dec(v_m_8_);
return v_res_10_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Log2(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Fin_Log2(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Log2(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Fin_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Fin_Log2(builtin);
}
#ifdef __cplusplus
}
#endif
