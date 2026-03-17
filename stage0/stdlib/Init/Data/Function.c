// Lean compiler output
// Module: Init.Data.Function
// Imports: public import Init.Grind.Tactics
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
LEAN_EXPORT lean_object* l_Function_curry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_curry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_uncurry___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_curry___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_a_2_);
lean_ctor_set(v___x_4_, 1, v_b_3_);
v___x_5_ = lean_apply_1(v_f_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Function_curry(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_00_u03c6_8_, lean_object* v_f_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v_a_10_);
lean_ctor_set(v___x_12_, 1, v_b_11_);
v___x_13_ = lean_apply_1(v_f_9_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Function_uncurry___redArg(lean_object* v_f_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___x_18_; 
v_fst_16_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_fst_16_);
v_snd_17_ = lean_ctor_get(v_a_15_, 1);
lean_inc(v_snd_17_);
lean_dec_ref(v_a_15_);
v___x_18_ = lean_apply_2(v_f_14_, v_fst_16_, v_snd_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Function_uncurry(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_00_u03c6_21_, lean_object* v_f_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_26_; 
v_fst_24_ = lean_ctor_get(v_a_23_, 0);
lean_inc(v_fst_24_);
v_snd_25_ = lean_ctor_get(v_a_23_, 1);
lean_inc(v_snd_25_);
lean_dec_ref(v_a_23_);
v___x_26_ = lean_apply_2(v_f_22_, v_fst_24_, v_snd_25_);
return v___x_26_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Function(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Function(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Function(builtin);
}
#ifdef __cplusplus
}
#endif
