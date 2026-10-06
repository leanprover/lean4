// Lean compiler output
// Module: Std.Internal.Order.FrameClosure
// Imports: public import Std.Internal.Order.OfProp public import Std.Internal.Order.PreservesSup public import Std.Internal.Order.PredTrans
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
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_pointwise___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_pointwise(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_prod___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_prod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_pointwise___redArg(lean_object* v_opE_1_, lean_object* v_r_2_, lean_object* v_g_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v_g_3_, v_a_4_);
v___x_6_ = lean_apply_2(v_opE_1_, v_r_2_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_pointwise(lean_object* v_A_7_, lean_object* v_R_8_, lean_object* v_00_u03b5_9_, lean_object* v_opE_10_, lean_object* v_r_11_, lean_object* v_g_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Order_FrameOp_pointwise___redArg(v_opE_10_, v_r_11_, v_g_12_, v_a_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_prod___redArg(lean_object* v_opA_15_, lean_object* v_opB_16_, lean_object* v_r_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc(v_r_17_);
v___x_19_ = lean_apply_1(v_opA_15_, v_r_17_);
v___x_20_ = lean_apply_1(v_opB_16_, v_r_17_);
v___x_21_ = l_Prod_map___redArg(v___x_19_, v___x_20_, v_a_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_prod(lean_object* v_A_22_, lean_object* v_B_23_, lean_object* v_R_24_, lean_object* v_opA_25_, lean_object* v_opB_26_, lean_object* v_r_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Order_FrameOp_prod___redArg(v_opA_25_, v_opB_26_, v_r_27_, v_a_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore___redArg(lean_object* v_a_30_){
_start:
{
lean_inc(v_a_30_);
return v_a_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore___redArg___boxed(lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Order_FrameOp_ignore___redArg(v_a_31_);
lean_dec(v_a_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore(lean_object* v_A_33_, lean_object* v_R_34_, lean_object* v_x_35_, lean_object* v_a_36_){
_start:
{
lean_inc(v_a_36_);
return v_a_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Order_FrameOp_ignore___boxed(lean_object* v_A_37_, lean_object* v_R_38_, lean_object* v_x_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Order_FrameOp_ignore(v_A_37_, v_R_38_, v_x_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec(v_x_39_);
return v_res_41_;
}
}
lean_object* runtime_initialize_Std_Internal_Order_OfProp(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_PreservesSup(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_PredTrans(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Order_FrameClosure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Order_OfProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_PreservesSup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Order_FrameClosure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Order_OfProp(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_PreservesSup(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_PredTrans(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Order_FrameClosure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Order_OfProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_PreservesSup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_FrameClosure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Order_FrameClosure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Order_FrameClosure(builtin);
}
#ifdef __cplusplus
}
#endif
