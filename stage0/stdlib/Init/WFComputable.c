// Lean compiler output
// Module: Init.WFComputable
// Imports: public import Init.WF import Init.NotationExtra import Init.WFTactics
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
LEAN_EXPORT lean_object* l_Acc_wfRel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_recC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_recC___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_recC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_wfRel(lean_object* v_00_u03b1_1_, lean_object* v_r_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg(lean_object* v_intro_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___f_6_; lean_object* v___x_7_; 
lean_inc(v_intro_4_);
v___f_6_ = lean_alloc_closure((void*)(l_Acc_recC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6_, 0, v_intro_4_);
v___x_7_ = lean_apply_3(v_intro_4_, v_a_5_, lean_box(0), v___f_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg___lam__0(lean_object* v_intro_8_, lean_object* v_x_9_, lean_object* v_hr_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Acc_recC___redArg(v_intro_8_, v_x_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC(lean_object* v_00_u03b1_12_, lean_object* v_r_13_, lean_object* v_motive_14_, lean_object* v_intro_15_, lean_object* v_a_16_, lean_object* v_t_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Acc_recC___redArg(v_intro_15_, v_a_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object* v_m_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Acc_recC___redArg(v_m_19_, v_a_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object* v_00_u03b1_22_, lean_object* v_r_23_, lean_object* v_C_24_, lean_object* v_m_25_, lean_object* v_a_26_, lean_object* v_n_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Acc_recC___redArg(v_m_25_, v_a_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object* v_a_29_, lean_object* v_m_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Acc_recC___redArg(v_m_30_, v_a_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object* v_00_u03b1_32_, lean_object* v_r_33_, lean_object* v_C_34_, lean_object* v_a_35_, lean_object* v_n_36_, lean_object* v_m_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Acc_recC___redArg(v_m_37_, v_a_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object* v_F_39_, lean_object* v_x_u2081_40_, lean_object* v_h_41_, lean_object* v_ih_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_apply_2(v_F_39_, v_x_u2081_40_, v_ih_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object* v_F_44_, lean_object* v_x_45_){
_start:
{
lean_object* v___f_46_; lean_object* v___x_47_; 
v___f_46_ = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(v___f_46_, 0, v_F_44_);
v___x_47_ = l_Acc_recC___redArg(v___f_46_, v_x_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC(lean_object* v_00_u03b1_48_, lean_object* v_r_49_, lean_object* v_C_50_, lean_object* v_F_51_, lean_object* v_x_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___f_54_; lean_object* v___x_55_; 
v___f_54_ = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(v___f_54_, 0, v_F_51_);
v___x_55_ = l_Acc_recC___redArg(v___f_54_, v_x_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg(lean_object* v_F_56_, lean_object* v_x_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; 
lean_inc(v_F_56_);
v___f_58_ = lean_alloc_closure((void*)(l_WellFounded_fixC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_58_, 0, v_F_56_);
v___x_59_ = lean_apply_2(v_F_56_, v_x_57_, v___f_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg___lam__0(lean_object* v_F_60_, lean_object* v_y_61_, lean_object* v_x_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_WellFounded_fixC___redArg(v_F_60_, v_y_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC(lean_object* v_00_u03b1_64_, lean_object* v_C_65_, lean_object* v_r_66_, lean_object* v_hwf_67_, lean_object* v_F_68_, lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_WellFounded_fixC___redArg(v_F_68_, v_x_69_);
return v___x_70_;
}
}
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_WFComputable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_WFComputable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_WFComputable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFComputable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_WFComputable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_WFComputable(builtin);
}
#ifdef __cplusplus
}
#endif
