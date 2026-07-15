// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.RefVecOperator
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
lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_w_3_, lean_object* v_aig_4_, lean_object* v_s_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkNotCached___boxed), 5, 3);
lean_closure_set(v___x_6_, 0, lean_box(0));
lean_closure_set(v___x_6_, 1, v_inst_1_);
lean_closure_set(v___x_6_, 2, v_inst_2_);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_s_5_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
v___x_8_ = l_Std_Sat_AIG_RefVec_map___redArg(v_w_3_, v_aig_4_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg___boxed(lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_w_11_, lean_object* v_aig_12_, lean_object* v_s_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(v_inst_9_, v_inst_10_, v_w_11_, v_aig_12_, v_s_13_);
lean_dec(v_w_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_w_18_, lean_object* v_aig_19_, lean_object* v_s_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(v_inst_16_, v_inst_17_, v_w_18_, v_aig_19_, v_s_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_w_25_, lean_object* v_aig_26_, lean_object* v_s_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot(v_00_u03b1_22_, v_inst_23_, v_inst_24_, v_w_25_, v_aig_26_, v_s_27_);
lean_dec(v_w_25_);
return v_res_28_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_RefVecOperator(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_RefVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_RefVecOperator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_RefVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
}
#ifdef __cplusplus
}
#endif
