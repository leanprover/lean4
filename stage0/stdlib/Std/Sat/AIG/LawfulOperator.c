// Lean compiler output
// Module: Std.Sat.AIG.LawfulOperator
// Imports: public import Std.Sat.AIG.Basic import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_5_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v___x_5_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_5_;
}
case 1:
{
lean_object* v_idx_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_idx_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_idx_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_2(v_h__2_3_, v_idx_6_, lean_box(0));
return v___x_7_;
}
default: 
{
lean_object* v_l_8_; lean_object* v_r_9_; lean_object* v___x_10_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v_l_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_l_8_);
v_r_9_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_r_9_);
lean_dec_ref(v_x_1_);
v___x_10_ = lean_apply_3(v_h__3_4_, v_l_8_, v_r_9_, lean_box(0));
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* v_00_u03b1_11_, lean_object* v_motive_12_, lean_object* v_x_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_, lean_object* v_h__3_16_){
_start:
{
switch(lean_obj_tag(v_x_13_))
{
case 0:
{
lean_object* v___x_17_; 
lean_dec(v_h__3_16_);
lean_dec(v_h__2_15_);
v___x_17_ = lean_apply_1(v_h__1_14_, lean_box(0));
return v___x_17_;
}
case 1:
{
lean_object* v_idx_18_; lean_object* v___x_19_; 
lean_dec(v_h__3_16_);
lean_dec(v_h__1_14_);
v_idx_18_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_idx_18_);
lean_dec_ref(v_x_13_);
v___x_19_ = lean_apply_2(v_h__2_15_, v_idx_18_, lean_box(0));
return v___x_19_;
}
default: 
{
lean_object* v_l_20_; lean_object* v_r_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_15_);
lean_dec(v_h__1_14_);
v_l_20_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_l_20_);
v_r_21_ = lean_ctor_get(v_x_13_, 1);
lean_inc(v_r_21_);
lean_dec_ref(v_x_13_);
v___x_22_ = lean_apply_3(v_h__3_16_, v_l_20_, v_r_21_, lean_box(0));
return v___x_22_;
}
}
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_LawfulOperator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_LawfulOperator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_LawfulOperator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_LawfulOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_LawfulOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_LawfulOperator(builtin);
}
#ifdef __cplusplus
}
#endif
