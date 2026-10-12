// Lean compiler output
// Module: Std.Tactic.BVDecide.Syntax
// Imports: public import Init.Simproc public import Init.Grind.Tactics public import Init.MetaTypes import Init.Data.Nat.Bitwise.Basic
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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(lean_object* v_proof_24_){
_start:
{
lean_inc(v_proof_24_);
return v_proof_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg___boxed(lean_object* v_proof_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(v_proof_25_);
lean_dec(v_proof_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_proof_30_){
_start:
{
lean_inc(v_proof_30_);
return v_proof_30_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_proof_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(lean_box(0), v_t_28_, lean_box(0), v_proof_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_proof_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_proof_35_);
lean_dec(v_proof_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(lean_object* v_counterexample_38_){
_start:
{
lean_inc(v_counterexample_38_);
return v_counterexample_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg___boxed(lean_object* v_counterexample_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(v_counterexample_39_);
lean_dec(v_counterexample_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_counterexample_44_){
_start:
{
lean_inc(v_counterexample_44_);
return v_counterexample_44_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_counterexample_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(lean_box(0), v_t_42_, lean_box(0), v_counterexample_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_counterexample_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_counterexample_49_);
lean_dec(v_counterexample_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(lean_object* v_default_52_){
_start:
{
lean_inc(v_default_52_);
return v_default_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg___boxed(lean_object* v_default_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(v_default_53_);
lean_dec(v_default_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_default_58_){
_start:
{
lean_inc(v_default_58_);
return v_default_58_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_default_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(lean_box(0), v_t_56_, lean_box(0), v_default_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_default_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_default_63_);
lean_dec(v_default_63_);
return v_res_65_;
}
}
uint8_t l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental(lean_object* v_cfg_66_){
_start:
{
uint8_t v_uf_67_; 
v_uf_67_ = lean_ctor_get_uint8(v_cfg_66_, sizeof(void*)*3 + 11);
return v_uf_67_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_66_ = stack[0].m_obj;
uint8_t v_res_68_;
v_res_68_ = l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental(v_cfg_66_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental___boxed(lean_object* v_cfg_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental(v_cfg_69_);
lean_dec_ref(v_cfg_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
