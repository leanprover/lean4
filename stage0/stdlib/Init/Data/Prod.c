// Lean compiler output
// Module: Init.Data.Prod
// Imports: public import Init.NotationExtra
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
LEAN_EXPORT lean_object* l_Prod_swap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Prod_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_swap___redArg(lean_object* v_p_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_10_; 
v_fst_2_ = lean_ctor_get(v_p_1_, 0);
v_snd_3_ = lean_ctor_get(v_p_1_, 1);
v_isSharedCheck_10_ = !lean_is_exclusive(v_p_1_);
if (v_isSharedCheck_10_ == 0)
{
v___x_5_ = v_p_1_;
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_snd_3_);
lean_inc(v_fst_2_);
lean_dec(v_p_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v_fst_2_);
lean_ctor_set(v___x_5_, 0, v_snd_3_);
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_9_; 
v_reuseFailAlloc_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_9_, 0, v_snd_3_);
lean_ctor_set(v_reuseFailAlloc_9_, 1, v_fst_2_);
v___x_8_ = v_reuseFailAlloc_9_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_swap(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_p_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Prod_swap___redArg(v_p_13_);
return v___x_14_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Prod(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Prod(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Prod(builtin);
}
#ifdef __cplusplus
}
#endif
