// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.LawfulVecOperator import Init.Data.Nat.Order import Init.Data.Order.Lemmas
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(lean_object* v_aig_1_, lean_object* v_target_2_){
_start:
{
lean_object* v_lhs_3_; lean_object* v_rhs_4_; lean_object* v_combined_5_; lean_object* v___x_6_; 
v_lhs_3_ = lean_ctor_get(v_target_2_, 2);
lean_inc_ref(v_lhs_3_);
v_rhs_4_ = lean_ctor_get(v_target_2_, 3);
lean_inc_ref(v_rhs_4_);
lean_dec_ref(v_target_2_);
v_combined_5_ = l_Array_append___redArg(v_rhs_4_, v_lhs_3_);
lean_dec_ref(v_lhs_3_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_aig_1_);
lean_ctor_set(v___x_6_, 1, v_combined_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_newWidth_10_, lean_object* v_aig_11_, lean_object* v_target_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(v_aig_11_, v_target_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___boxed(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_newWidth_17_, lean_object* v_aig_18_, lean_object* v_target_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend(v_00_u03b1_14_, v_inst_15_, v_inst_16_, v_newWidth_17_, v_aig_18_, v_target_19_);
lean_dec(v_newWidth_17_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_inst_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter___redArg(lean_object* v_target_21_, lean_object* v_h__1_22_){
_start:
{
lean_object* v_lw_23_; lean_object* v_rw_24_; lean_object* v_lhs_25_; lean_object* v_rhs_26_; lean_object* v___x_27_; 
v_lw_23_ = lean_ctor_get(v_target_21_, 0);
lean_inc(v_lw_23_);
v_rw_24_ = lean_ctor_get(v_target_21_, 1);
lean_inc(v_rw_24_);
v_lhs_25_ = lean_ctor_get(v_target_21_, 2);
lean_inc_ref(v_lhs_25_);
v_rhs_26_ = lean_ctor_get(v_target_21_, 3);
lean_inc_ref(v_rhs_26_);
lean_dec_ref(v_target_21_);
v___x_27_ = lean_apply_5(v_h__1_22_, v_lw_23_, v_rw_24_, v_lhs_25_, v_rhs_26_, lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_newWidth_31_, lean_object* v_aig_32_, lean_object* v_motive_33_, lean_object* v_target_34_, lean_object* v_h__1_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter___redArg(v_target_34_, v_h__1_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_newWidth_40_, lean_object* v_aig_41_, lean_object* v_motive_42_, lean_object* v_target_43_, lean_object* v_h__1_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter(v_00_u03b1_37_, v_inst_38_, v_inst_39_, v_newWidth_40_, v_aig_41_, v_motive_42_, v_target_43_, v_h__1_44_);
lean_dec_ref(v_aig_41_);
lean_dec(v_newWidth_40_);
lean_dec_ref(v_inst_39_);
lean_dec_ref(v_inst_38_);
return v_res_45_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
}
#ifdef __cplusplus
}
#endif
