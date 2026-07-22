// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastSub_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastSub_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastSub_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_input_5_){
_start:
{
lean_object* v_lhs_6_; lean_object* v_rhs_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_18_; 
v_lhs_6_ = lean_ctor_get(v_input_5_, 0);
v_rhs_7_ = lean_ctor_get(v_input_5_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_input_5_);
if (v_isSharedCheck_18_ == 0)
{
v___x_9_ = v_input_5_;
v_isShared_10_ = v_isSharedCheck_18_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_rhs_7_);
lean_inc(v_lhs_6_);
lean_dec(v_input_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_18_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v_res_11_; lean_object* v_aig_12_; lean_object* v_vec_13_; lean_object* v___x_15_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_11_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_4_, v_rhs_7_);
v_aig_12_ = lean_ctor_get(v_res_11_, 0);
lean_inc_ref(v_aig_12_);
v_vec_13_ = lean_ctor_get(v_res_11_, 1);
lean_inc_ref(v_vec_13_);
lean_dec_ref(v_res_11_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 1, v_vec_13_);
v___x_15_ = v___x_9_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_lhs_6_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v_vec_13_);
v___x_15_ = v_reuseFailAlloc_17_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; 
v___x_16_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(v_inst_1_, v_inst_2_, v_w_3_, v_aig_12_, v___x_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg___boxed(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_w_21_, lean_object* v_aig_22_, lean_object* v_input_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(v_inst_19_, v_inst_20_, v_w_21_, v_aig_22_, v_input_23_);
lean_dec(v_w_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_w_28_, lean_object* v_aig_29_, lean_object* v_input_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(v_inst_26_, v_inst_27_, v_w_28_, v_aig_29_, v_input_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___boxed(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_w_35_, lean_object* v_aig_36_, lean_object* v_input_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub(v_00_u03b1_32_, v_inst_33_, v_inst_34_, v_w_35_, v_aig_36_, v_input_37_);
lean_dec(v_w_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastSub_match__1_splitter___redArg(lean_object* v_input_39_, lean_object* v_h__1_40_){
_start:
{
lean_object* v_lhs_41_; lean_object* v_rhs_42_; lean_object* v___x_43_; 
v_lhs_41_ = lean_ctor_get(v_input_39_, 0);
lean_inc_ref(v_lhs_41_);
v_rhs_42_ = lean_ctor_get(v_input_39_, 1);
lean_inc_ref(v_rhs_42_);
lean_dec_ref(v_input_39_);
v___x_43_ = lean_apply_2(v_h__1_40_, v_lhs_41_, v_rhs_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastSub_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_w_47_, lean_object* v_aig_48_, lean_object* v_motive_49_, lean_object* v_input_50_, lean_object* v_h__1_51_){
_start:
{
lean_object* v_lhs_52_; lean_object* v_rhs_53_; lean_object* v___x_54_; 
v_lhs_52_ = lean_ctor_get(v_input_50_, 0);
lean_inc_ref(v_lhs_52_);
v_rhs_53_ = lean_ctor_get(v_input_50_, 1);
lean_inc_ref(v_rhs_53_);
lean_dec_ref(v_input_50_);
v___x_54_ = lean_apply_2(v_h__1_51_, v_lhs_52_, v_rhs_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastSub_match__1_splitter___boxed(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_w_58_, lean_object* v_aig_59_, lean_object* v_motive_60_, lean_object* v_input_61_, lean_object* v_h__1_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastSub_match__1_splitter(v_00_u03b1_55_, v_inst_56_, v_inst_57_, v_w_58_, v_aig_59_, v_motive_60_, v_input_61_, v_h__1_62_);
lean_dec_ref(v_aig_59_);
lean_dec(v_w_58_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
return v_res_63_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
}
#ifdef __cplusplus
}
#endif
