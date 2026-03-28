// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Checker
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Convert public import Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound public import Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker import Std.Tactic.BVDecide.LRAT.Internal.CompactLRATCheckerSound
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
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object*);
lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object* v_lratProof_1_, lean_object* v_cnf_2_){
_start:
{
lean_object* v_internalFormula_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v_checkerResult_7_; uint8_t v___x_8_; uint8_t v___x_9_; 
lean_inc_ref(v_cnf_2_);
v_internalFormula_3_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(v_cnf_2_);
v___x_4_ = l_Std_Sat_CNF_numLiterals(v_cnf_2_);
lean_dec_ref(v_cnf_2_);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_add(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v_checkerResult_7_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(v___x_6_, v_internalFormula_3_, v_lratProof_1_);
v___x_8_ = 0;
v___x_9_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(v_checkerResult_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object* v_lratProof_10_, lean_object* v_cnf_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_Tactic_BVDecide_LRAT_check(v_lratProof_10_, v_cnf_11_);
lean_dec_ref(v_lratProof_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
}
#ifdef __cplusplus
}
#endif
