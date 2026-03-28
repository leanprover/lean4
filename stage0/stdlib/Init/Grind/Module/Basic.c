// Lean compiler output
// Module: Init.Grind.Module.Basic
// Imports: public import Init.Grind.ToInt import all Init.Grind.ToInt
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
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule___redArg(lean_object* v_I_1_){
_start:
{
lean_object* v_toAddCommGroup_2_; lean_object* v_nsmul_3_; lean_object* v_toAddCommMonoid_4_; lean_object* v___x_5_; 
v_toAddCommGroup_2_ = lean_ctor_get(v_I_1_, 0);
v_nsmul_3_ = lean_ctor_get(v_I_1_, 1);
v_toAddCommMonoid_4_ = lean_ctor_get(v_toAddCommGroup_2_, 0);
lean_inc(v_nsmul_3_);
lean_inc_ref(v_toAddCommMonoid_4_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_toAddCommMonoid_4_);
lean_ctor_set(v___x_5_, 1, v_nsmul_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule___redArg___boxed(lean_object* v_I_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_I_6_);
lean_dec_ref(v_I_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule(lean_object* v_M_8_, lean_object* v_I_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_I_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_toNatModule___boxed(lean_object* v_M_11_, lean_object* v_I_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Grind_IntModule_toNatModule(v_M_11_, v_I_12_);
lean_dec_ref(v_I_12_);
return v_res_13_;
}
}
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Module_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Module_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Module_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Module_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Module_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
