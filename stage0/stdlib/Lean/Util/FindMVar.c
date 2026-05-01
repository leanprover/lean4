// Lean compiler output
// Module: Lean.Util.FindMVar
// Imports: public import Lean.Expr
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
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_main___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findMVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_main(lean_object* v_p_1_, lean_object* v_x_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_d_5_; lean_object* v_b_6_; lean_object* v___y_7_; 
switch(lean_obj_tag(v_x_2_))
{
case 11:
{
lean_object* v_struct_10_; lean_object* v___x_11_; 
v_struct_10_ = lean_ctor_get(v_x_2_, 2);
lean_inc_ref(v_struct_10_);
lean_dec_ref(v_x_2_);
v___x_11_ = l_Lean_FindMVar_visit(v_p_1_, v_struct_10_, v_a_3_);
return v___x_11_;
}
case 7:
{
lean_object* v_binderType_12_; lean_object* v_body_13_; 
v_binderType_12_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_binderType_12_);
v_body_13_ = lean_ctor_get(v_x_2_, 2);
lean_inc_ref(v_body_13_);
lean_dec_ref(v_x_2_);
v_d_5_ = v_binderType_12_;
v_b_6_ = v_body_13_;
v___y_7_ = v_a_3_;
goto v___jp_4_;
}
case 6:
{
lean_object* v_binderType_14_; lean_object* v_body_15_; 
v_binderType_14_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_binderType_14_);
v_body_15_ = lean_ctor_get(v_x_2_, 2);
lean_inc_ref(v_body_15_);
lean_dec_ref(v_x_2_);
v_d_5_ = v_binderType_14_;
v_b_6_ = v_body_15_;
v___y_7_ = v_a_3_;
goto v___jp_4_;
}
case 8:
{
lean_object* v_type_16_; lean_object* v_value_17_; lean_object* v_body_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_type_16_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_type_16_);
v_value_17_ = lean_ctor_get(v_x_2_, 2);
lean_inc_ref(v_value_17_);
v_body_18_ = lean_ctor_get(v_x_2_, 3);
lean_inc_ref(v_body_18_);
lean_dec_ref(v_x_2_);
lean_inc_ref_n(v_p_1_, 2);
v___x_19_ = l_Lean_FindMVar_visit(v_p_1_, v_type_16_, v_a_3_);
v___x_20_ = l_Lean_FindMVar_visit(v_p_1_, v_value_17_, v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = l_Lean_FindMVar_visit(v_p_1_, v_body_18_, v___x_20_);
lean_dec(v___x_20_);
return v___x_21_;
}
case 5:
{
lean_object* v_fn_22_; lean_object* v_arg_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_fn_22_ = lean_ctor_get(v_x_2_, 0);
lean_inc_ref(v_fn_22_);
v_arg_23_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_arg_23_);
lean_dec_ref(v_x_2_);
lean_inc_ref(v_p_1_);
v___x_24_ = l_Lean_FindMVar_visit(v_p_1_, v_fn_22_, v_a_3_);
v___x_25_ = l_Lean_FindMVar_visit(v_p_1_, v_arg_23_, v___x_24_);
lean_dec(v___x_24_);
return v___x_25_;
}
case 10:
{
lean_object* v_expr_26_; lean_object* v___x_27_; 
v_expr_26_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_expr_26_);
lean_dec_ref(v_x_2_);
v___x_27_ = l_Lean_FindMVar_visit(v_p_1_, v_expr_26_, v_a_3_);
return v___x_27_;
}
case 2:
{
if (lean_obj_tag(v_a_3_) == 0)
{
lean_object* v_mvarId_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v_mvarId_28_ = lean_ctor_get(v_x_2_, 0);
lean_inc_n(v_mvarId_28_, 2);
lean_dec_ref(v_x_2_);
v___x_29_ = lean_apply_1(v_p_1_, v_mvarId_28_);
v___x_30_ = lean_unbox(v___x_29_);
if (v___x_30_ == 0)
{
lean_dec(v_mvarId_28_);
return v_a_3_;
}
else
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v_mvarId_28_);
return v___x_31_;
}
}
else
{
lean_dec_ref(v_x_2_);
lean_dec_ref(v_p_1_);
lean_inc_ref(v_a_3_);
return v_a_3_;
}
}
default: 
{
lean_dec_ref(v_x_2_);
lean_dec_ref(v_p_1_);
lean_inc(v_a_3_);
return v_a_3_;
}
}
v___jp_4_:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc_ref(v_p_1_);
v___x_8_ = l_Lean_FindMVar_visit(v_p_1_, v_d_5_, v___y_7_);
v___x_9_ = l_Lean_FindMVar_visit(v_p_1_, v_b_6_, v___x_8_);
lean_dec(v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit(lean_object* v_p_32_, lean_object* v_e_33_, lean_object* v_s_34_){
_start:
{
if (lean_obj_tag(v_s_34_) == 0)
{
uint8_t v___x_35_; 
v___x_35_ = l_Lean_Expr_hasExprMVar(v_e_33_);
if (v___x_35_ == 0)
{
lean_dec_ref(v_e_33_);
lean_dec_ref(v_p_32_);
return v_s_34_;
}
else
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_FindMVar_main(v_p_32_, v_e_33_, v_s_34_);
return v___x_36_;
}
}
else
{
lean_dec_ref(v_e_33_);
lean_dec_ref(v_p_32_);
lean_inc_ref(v_s_34_);
return v_s_34_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit___boxed(lean_object* v_p_37_, lean_object* v_e_38_, lean_object* v_s_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_FindMVar_visit(v_p_37_, v_e_38_, v_s_39_);
lean_dec(v_s_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_FindMVar_main___boxed(lean_object* v_p_41_, lean_object* v_x_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_FindMVar_main(v_p_41_, v_x_42_, v_a_43_);
lean_dec(v_a_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findMVar_x3f(lean_object* v_e_45_, lean_object* v_p_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_box(0);
v___x_48_ = l_Lean_FindMVar_main(v_p_46_, v_e_45_, v___x_47_);
return v___x_48_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_FindMVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_FindMVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FindMVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FindMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_FindMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_FindMVar(builtin);
}
#ifdef __cplusplus
}
#endif
