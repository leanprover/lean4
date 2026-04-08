// Lean compiler output
// Module: Init.Classical
// Imports: public import Init.PropLemmas
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
LEAN_EXPORT uint8_t l_Classical_decidable__of__decidable__not___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Classical_decidable__of__decidable__not(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Classical_decidable__of__decidable__not___redArg(uint8_t v_h_1_){
_start:
{
if (v_h_1_ == 0)
{
uint8_t v___x_2_; 
v___x_2_ = 1;
return v___x_2_;
}
else
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___redArg___boxed(lean_object* v_h_4_){
_start:
{
uint8_t v_h_boxed_5_; uint8_t v_res_6_; lean_object* v_r_7_; 
v_h_boxed_5_ = lean_unbox(v_h_4_);
v_res_6_ = l_Classical_decidable__of__decidable__not___redArg(v_h_boxed_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_Classical_decidable__of__decidable__not(lean_object* v_p_8_, uint8_t v_h_9_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = l_Classical_decidable__of__decidable__not___redArg(v_h_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___boxed(lean_object* v_p_11_, lean_object* v_h_12_){
_start:
{
uint8_t v_h_boxed_13_; uint8_t v_res_14_; lean_object* v_r_15_; 
v_h_boxed_13_ = lean_unbox(v_h_12_);
v_res_14_ = l_Classical_decidable__of__decidable__not(v_p_11_, v_h_boxed_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Classical(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Classical(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Classical(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Classical(builtin);
}
#ifdef __cplusplus
}
#endif
