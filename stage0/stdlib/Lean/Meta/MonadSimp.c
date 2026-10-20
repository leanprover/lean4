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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_instInhabitedResult_default;
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_instInhabitedResult;
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_MonadSimp_Result_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_e_7_; lean_object* v_h_8_; lean_object* v___x_9_; 
v_e_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_e_7_);
v_h_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_h_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_e_7_, v_h_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_MonadSimp_Result_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim___redArg(lean_object* v_t_22_, lean_object* v_rfl_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_22_, v_rfl_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_rfl_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_rfl_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_26_, v_rfl_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim___redArg(lean_object* v_t_30_, lean_object* v_step_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_30_, v_step_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MonadSimp_Result_step_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_step_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_34_, v_step_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_MonadSimp_instInhabitedResult_default(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Meta_MonadSimp_instInhabitedResult(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_MonadSimp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
