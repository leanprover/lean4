// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
// Imports: public import Std.Sat.AIG.Basic public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
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
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment(lean_object* v_assign_1_, lean_object* v_bit_2_){
_start:
{
lean_object* v_var_3_; lean_object* v_idx_4_; lean_object* v___x_5_; lean_object* v_bv_6_; uint8_t v___x_7_; 
v_var_3_ = lean_ctor_get(v_bit_2_, 0);
v_idx_4_ = lean_ctor_get(v_bit_2_, 2);
v___x_5_ = l_Lean_RArray_getImpl___redArg(v_assign_1_, v_var_3_);
v_bv_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_bv_6_);
lean_dec(v___x_5_);
v___x_7_ = l_Nat_testBit(v_bv_6_, v_idx_4_);
lean_dec(v_bv_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment___boxed(lean_object* v_assign_8_, lean_object* v_bit_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment(v_assign_8_, v_bit_9_);
lean_dec_ref(v_bit_9_);
lean_dec_ref(v_assign_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
