// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
// Imports: public import Std.Sat.AIG.RefVecOperator
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
lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_zip___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkAndCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_pair_5_){
_start:
{
lean_object* v___x_6_; lean_object* v_res_7_; lean_object* v_aig_8_; lean_object* v_vec_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v___x_6_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkBEqCached), 5, 3);
lean_closure_set(v___x_6_, 0, lean_box(0));
lean_closure_set(v___x_6_, 1, v_inst_1_);
lean_closure_set(v___x_6_, 2, v_inst_2_);
v_res_7_ = l_Std_Sat_AIG_RefVec_zip___redArg(v_w_3_, v_aig_4_, v_pair_5_, v___x_6_);
v_aig_8_ = lean_ctor_get(v_res_7_, 0);
lean_inc_ref(v_aig_8_);
v_vec_9_ = lean_ctor_get(v_res_7_, 1);
lean_inc_ref(v_vec_9_);
lean_dec_ref(v_res_7_);
v___x_10_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAndCached), 5, 3);
lean_closure_set(v___x_10_, 0, lean_box(0));
lean_closure_set(v___x_10_, 1, v_inst_1_);
lean_closure_set(v___x_10_, 2, v_inst_2_);
v___x_11_ = l_Std_Sat_AIG_RefVec_fold___redArg(v_w_3_, v_aig_8_, v_vec_9_, v___x_10_);
lean_dec_ref(v_vec_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg___boxed(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_w_14_, lean_object* v_aig_15_, lean_object* v_pair_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(v_inst_12_, v_inst_13_, v_w_14_, v_aig_15_, v_pair_16_);
lean_dec_ref(v_pair_16_);
lean_dec(v_w_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_w_21_, lean_object* v_aig_22_, lean_object* v_pair_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(v_inst_19_, v_inst_20_, v_w_21_, v_aig_22_, v_pair_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_w_28_, lean_object* v_aig_29_, lean_object* v_pair_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Tactic_BVDecide_BVPred_mkEq(v_00_u03b1_25_, v_inst_26_, v_inst_27_, v_w_28_, v_aig_29_, v_pair_30_);
lean_dec_ref(v_pair_30_);
lean_dec(v_w_28_);
return v_res_31_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_RefVecOperator(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_RefVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_RefVecOperator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_RefVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
}
#ifdef __cplusplus
}
#endif
