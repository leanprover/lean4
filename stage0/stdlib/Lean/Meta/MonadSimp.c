// Lean compiler output
// Module: Lean.Meta.MonadSimp
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
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_instInhabitedResult_default;
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_instInhabitedResult;
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_MonadSimp_Result_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_e_8_; lean_object* v_h_9_; lean_object* v___x_10_; 
v_e_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_e_8_);
v_h_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_h_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_e_8_, v_h_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_MonadSimp_Result_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim___redArg(lean_object* v_t_23_, lean_object* v_rfl_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_23_, v_rfl_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_rfl_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_27_, v_rfl_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim___redArg(lean_object* v_t_31_, lean_object* v_step_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_31_, v_step_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_step_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_35_, v_step_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Meta_MonadSimp_instInhabitedResult_default(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Meta_MonadSimp_instInhabitedResult(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_MonadSimp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_MonadSimp_instInhabitedResult_default = _init_l_Lean_Meta_MonadSimp_instInhabitedResult_default();
lean_mark_persistent(l_Lean_Meta_MonadSimp_instInhabitedResult_default);
l_Lean_Meta_MonadSimp_instInhabitedResult = _init_l_Lean_Meta_MonadSimp_instInhabitedResult();
lean_mark_persistent(l_Lean_Meta_MonadSimp_instInhabitedResult);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_MonadSimp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_MonadSimp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MonadSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_MonadSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_MonadSimp(builtin);
}
#ifdef __cplusplus
}
#endif
