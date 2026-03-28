// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Pred
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__7_splitter___redArg(lean_object* v_pred_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_pred_1_) == 0)
{
lean_object* v_w_4_; lean_object* v_lhs_5_; uint8_t v_op_6_; lean_object* v_rhs_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_3_);
v_w_4_ = lean_ctor_get(v_pred_1_, 0);
lean_inc(v_w_4_);
v_lhs_5_ = lean_ctor_get(v_pred_1_, 1);
lean_inc_ref(v_lhs_5_);
v_op_6_ = lean_ctor_get_uint8(v_pred_1_, sizeof(void*)*3);
v_rhs_7_ = lean_ctor_get(v_pred_1_, 2);
lean_inc_ref(v_rhs_7_);
lean_dec_ref(v_pred_1_);
v___x_8_ = lean_box(v_op_6_);
v___x_9_ = lean_apply_4(v_h__1_2_, v_w_4_, v_lhs_5_, v___x_8_, v_rhs_7_);
return v___x_9_;
}
else
{
lean_object* v_w_10_; lean_object* v_expr_11_; lean_object* v_idx_12_; lean_object* v___x_13_; 
lean_dec(v_h__1_2_);
v_w_10_ = lean_ctor_get(v_pred_1_, 0);
lean_inc(v_w_10_);
v_expr_11_ = lean_ctor_get(v_pred_1_, 1);
lean_inc_ref(v_expr_11_);
v_idx_12_ = lean_ctor_get(v_pred_1_, 2);
lean_inc(v_idx_12_);
lean_dec_ref(v_pred_1_);
v___x_13_ = lean_apply_3(v_h__2_3_, v_w_10_, v_expr_11_, v_idx_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__7_splitter(lean_object* v_motive_14_, lean_object* v_pred_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (lean_obj_tag(v_pred_15_) == 0)
{
lean_object* v_w_18_; lean_object* v_lhs_19_; uint8_t v_op_20_; lean_object* v_rhs_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_17_);
v_w_18_ = lean_ctor_get(v_pred_15_, 0);
lean_inc(v_w_18_);
v_lhs_19_ = lean_ctor_get(v_pred_15_, 1);
lean_inc_ref(v_lhs_19_);
v_op_20_ = lean_ctor_get_uint8(v_pred_15_, sizeof(void*)*3);
v_rhs_21_ = lean_ctor_get(v_pred_15_, 2);
lean_inc_ref(v_rhs_21_);
lean_dec_ref(v_pred_15_);
v___x_22_ = lean_box(v_op_20_);
v___x_23_ = lean_apply_4(v_h__1_16_, v_w_18_, v_lhs_19_, v___x_22_, v_rhs_21_);
return v___x_23_;
}
else
{
lean_object* v_w_24_; lean_object* v_expr_25_; lean_object* v_idx_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_16_);
v_w_24_ = lean_ctor_get(v_pred_15_, 0);
lean_inc(v_w_24_);
v_expr_25_ = lean_ctor_get(v_pred_15_, 1);
lean_inc_ref(v_expr_25_);
v_idx_26_ = lean_ctor_get(v_pred_15_, 2);
lean_inc(v_idx_26_);
lean_dec_ref(v_pred_15_);
v___x_27_ = lean_apply_3(v_h__2_17_, v_w_24_, v_expr_25_, v_idx_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter___redArg(lean_object* v_input_28_, lean_object* v_h__1_29_){
_start:
{
lean_object* v_val_30_; lean_object* v_cache_31_; lean_object* v___x_32_; 
v_val_30_ = lean_ctor_get(v_input_28_, 0);
lean_inc(v_val_30_);
v_cache_31_ = lean_ctor_get(v_input_28_, 1);
lean_inc_ref(v_cache_31_);
lean_dec_ref(v_input_28_);
v___x_32_ = lean_apply_2(v_h__1_29_, v_val_30_, v_cache_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter(lean_object* v_aig_33_, lean_object* v_motive_34_, lean_object* v_input_35_, lean_object* v_h__1_36_){
_start:
{
lean_object* v_val_37_; lean_object* v_cache_38_; lean_object* v___x_39_; 
v_val_37_ = lean_ctor_get(v_input_35_, 0);
lean_inc(v_val_37_);
v_cache_38_ = lean_ctor_get(v_input_35_, 1);
lean_inc_ref(v_cache_38_);
lean_dec_ref(v_input_35_);
v___x_39_ = lean_apply_2(v_h__1_36_, v_val_37_, v_cache_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter___boxed(lean_object* v_aig_40_, lean_object* v_motive_41_, lean_object* v_input_42_, lean_object* v_h__1_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter(v_aig_40_, v_motive_41_, v_input_42_, v_h__1_43_);
lean_dec_ref(v_aig_40_);
return v_res_44_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
}
#ifdef __cplusplus
}
#endif
