// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Checker
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Checker
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
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_check(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object* v_lratProof_1_, lean_object* v_cnf_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = l_Std_Tactic_BVDecide_LRAT_Internal_check(v_lratProof_1_, v_cnf_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_check_0interp(lean_interpreter_value* stack)
{
lean_object* v_lratProof_1_ = stack[0].m_obj;
lean_object* v_cnf_2_ = stack[1].m_obj;
uint8_t v_res_4_;
v_res_4_ = l_Std_Tactic_BVDecide_LRAT_check(v_lratProof_1_, v_cnf_2_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object* v_lratProof_5_, lean_object* v_cnf_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Std_Tactic_BVDecide_LRAT_check(v_lratProof_5_, v_cnf_6_);
lean_dec_ref(v_lratProof_5_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(builtin);
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
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(builtin);
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
