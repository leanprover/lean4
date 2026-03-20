// Lean compiler output
// Module: Init.Grind.ToIntLemmas
// Imports: public import Init.Grind.ToInt import all Init.Grind.ToInt public import Init.Data.Option.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(lean_object* v_i_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_, lean_object* v_h__4_5_){
_start:
{
switch(lean_obj_tag(v_i_1_))
{
case 0:
{
lean_object* v_lo_6_; lean_object* v_hi_7_; lean_object* v___x_8_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_lo_6_ = lean_ctor_get(v_i_1_, 0);
lean_inc(v_lo_6_);
v_hi_7_ = lean_ctor_get(v_i_1_, 1);
lean_inc(v_hi_7_);
lean_dec_ref(v_i_1_);
v___x_8_ = lean_apply_2(v_h__1_2_, v_lo_6_, v_hi_7_);
return v___x_8_;
}
case 1:
{
lean_object* v_lo_9_; lean_object* v___x_10_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_lo_9_ = lean_ctor_get(v_i_1_, 0);
lean_inc(v_lo_9_);
lean_dec_ref(v_i_1_);
v___x_10_ = lean_apply_1(v_h__2_3_, v_lo_9_);
return v___x_10_;
}
case 2:
{
lean_object* v_hi_11_; lean_object* v___x_12_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v_hi_11_ = lean_ctor_get(v_i_1_, 0);
lean_inc(v_hi_11_);
lean_dec_ref(v_i_1_);
v___x_12_ = lean_apply_1(v_h__3_4_, v_hi_11_);
return v___x_12_;
}
default: 
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__4_5_, v___x_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(lean_object* v_motive_15_, lean_object* v_i_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_, lean_object* v_h__4_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(v_i_16_, v_h__1_17_, v_h__2_18_, v_h__3_19_, v_h__4_20_);
return v___x_21_;
}
}
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_ToIntLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_ToIntLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_ToIntLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToIntLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_ToIntLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_ToIntLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
