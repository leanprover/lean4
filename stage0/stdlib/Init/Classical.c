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
uint8_t l_Classical_decidable__of__decidable__not___redArg(uint8_t v_h_1_){
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
LEAN_EXPORT void l_Classical_decidable__of__decidable__not___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_h_1_ = stack[0].m_num;
uint8_t v_res_4_;
v_res_4_ = l_Classical_decidable__of__decidable__not___redArg(v_h_1_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___redArg___boxed(lean_object* v_h_5_){
_start:
{
uint8_t v_h_boxed_6_; uint8_t v_res_7_; lean_object* v_r_8_; 
v_h_boxed_6_ = lean_unbox(v_h_5_);
v_res_7_ = l_Classical_decidable__of__decidable__not___redArg(v_h_boxed_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint8_t l_Classical_decidable__of__decidable__not(lean_object* v_p_9_, uint8_t v_h_10_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = l_Classical_decidable__of__decidable__not___redArg(v_h_10_);
return v___x_11_;
}
}
LEAN_EXPORT void l_Classical_decidable__of__decidable__not_0interp(lean_interpreter_value* stack)
{
uint8_t v_h_10_ = stack[1].m_num;
uint8_t v_res_12_;
v_res_12_ = l_Classical_decidable__of__decidable__not(lean_box(0), v_h_10_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Classical_decidable__of__decidable__not___boxed(lean_object* v_p_13_, lean_object* v_h_14_){
_start:
{
uint8_t v_h_boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_h_boxed_15_ = lean_unbox(v_h_14_);
v_res_16_ = l_Classical_decidable__of__decidable__not(v_p_13_, v_h_boxed_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Classical(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
