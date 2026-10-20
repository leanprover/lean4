// Lean compiler output
// Module: Init.LetFun
// Imports: import Init.Notation
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
LEAN_EXPORT lean_object* l_letFun___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_letFun(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_letFun___redArg(lean_object* v_v_1_, lean_object* v_f_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_f_2_, v_v_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_letFun(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_v_6_, lean_object* v_f_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_f_7_, v_v_6_);
return v___x_8_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_LetFun(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_LetFun(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_LetFun(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LetFun(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_LetFun(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_LetFun(builtin);
}
#ifdef __cplusplus
}
#endif
