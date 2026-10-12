// Lean compiler output
// Module: Init.Grind.Offset
// Imports: public import Init.Grind.Tactics import Init.Omega
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_isLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_isLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_isLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_isLE___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Grind_isLt(lean_object* v_x_1_, lean_object* v_y_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_x_1_, v_y_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Grind_isLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_y_2_ = stack[1].m_obj;
uint8_t v_res_4_;
v_res_4_ = l_Lean_Grind_isLt(v_x_1_, v_y_2_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_isLt___boxed(lean_object* v_x_5_, lean_object* v_y_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Lean_Grind_isLt(v_x_5_, v_y_6_);
lean_dec(v_y_6_);
lean_dec(v_x_5_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint8_t l_Lean_Grind_isLE(lean_object* v_x_9_, lean_object* v_y_10_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_le(v_x_9_, v_y_10_);
return v___x_11_;
}
}
LEAN_EXPORT void l_Lean_Grind_isLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_9_ = stack[0].m_obj;
lean_object* v_y_10_ = stack[1].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Lean_Grind_isLE(v_x_9_, v_y_10_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_isLE___boxed(lean_object* v_x_13_, lean_object* v_y_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Grind_isLE(v_x_13_, v_y_14_);
lean_dec(v_y_14_);
lean_dec(v_x_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Offset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Offset(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Offset(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Offset(builtin);
}
#ifdef __cplusplus
}
#endif
