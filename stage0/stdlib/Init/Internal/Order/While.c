// Lean compiler output
// Module: Init.Internal.Order.While
// Imports: public import Init.While import all Init.While public import Init.Internal.Order.MonadTail
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
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__repeatM_body_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__repeatM_body_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__repeatM_body_match__1_splitter___redArg(lean_object* v_____do__lift_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_____do__lift_1_) == 0)
{
lean_object* v_val_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_val_4_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v_____do__lift_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_val_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_____do__lift_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__repeatM_body_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b2_9_, lean_object* v_motive_10_, lean_object* v_____do__lift_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_____do__lift_11_) == 0)
{
lean_object* v_val_14_; lean_object* v___x_15_; 
lean_dec(v_h__2_13_);
v_val_14_ = lean_ctor_get(v_____do__lift_11_, 0);
lean_inc(v_val_14_);
lean_dec_ref_known(v_____do__lift_11_, 1);
v___x_15_ = lean_apply_1(v_h__1_12_, v_val_14_);
return v___x_15_;
}
else
{
lean_object* v_val_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_12_);
v_val_16_ = lean_ctor_get(v_____do__lift_11_, 0);
lean_inc(v_val_16_);
lean_dec_ref_known(v_____do__lift_11_, 1);
v___x_17_ = lean_apply_1(v_h__2_13_, v_val_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object* v_____do__lift_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_____do__lift_18_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_20_);
v_a_21_ = lean_ctor_get(v_____do__lift_18_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v_____do__lift_18_, 1);
v___x_22_ = lean_apply_1(v_h__1_19_, v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_h__1_19_);
v_a_23_ = lean_ctor_get(v_____do__lift_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref_known(v_____do__lift_18_, 1);
v___x_24_ = lean_apply_1(v_h__2_20_, v_a_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter(lean_object* v_00_u03b2_25_, lean_object* v_motive_26_, lean_object* v_____do__lift_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_____do__lift_27_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; 
lean_dec(v_h__2_29_);
v_a_30_ = lean_ctor_get(v_____do__lift_27_, 0);
lean_inc(v_a_30_);
lean_dec_ref_known(v_____do__lift_27_, 1);
v___x_31_ = lean_apply_1(v_h__1_28_, v_a_30_);
return v___x_31_;
}
else
{
lean_object* v_a_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_28_);
v_a_32_ = lean_ctor_get(v_____do__lift_27_, 0);
lean_inc(v_a_32_);
lean_dec_ref_known(v_____do__lift_27_, 1);
v___x_33_ = lean_apply_1(v_h__2_29_, v_a_32_);
return v___x_33_;
}
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_MonadTail(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Internal_Order_While(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_MonadTail(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Internal_Order_While(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Internal_Order_MonadTail(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Internal_Order_While(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_MonadTail(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Internal_Order_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Internal_Order_While(builtin);
}
#ifdef __cplusplus
}
#endif
