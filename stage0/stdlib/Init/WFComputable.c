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
LEAN_EXPORT lean_object* l_Acc_wfRel___redArg();
LEAN_EXPORT lean_object* l_Acc_wfRel___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Acc_wfRel___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Acc_wfRel___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Acc_wfRel___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Acc_wfRel(lean_object* v_00_u03b1_5_, lean_object* v_r_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg(lean_object* v_intro_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; 
lean_inc(v_intro_8_);
v___f_10_ = lean_alloc_closure((void*)(l_Acc_recC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_10_, 0, v_intro_8_);
v___x_11_ = lean_apply_3(v_intro_8_, v_a_9_, lean_box(0), v___f_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg___lam__0(lean_object* v_intro_12_, lean_object* v_x_13_, lean_object* v_hr_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Acc_recC___redArg(v_intro_12_, v_x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC(lean_object* v_00_u03b1_16_, lean_object* v_r_17_, lean_object* v_motive_18_, lean_object* v_intro_19_, lean_object* v_a_20_, lean_object* v_t_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Acc_recC___redArg(v_intro_19_, v_a_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object* v_m_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Acc_recC___redArg(v_m_23_, v_a_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object* v_00_u03b1_26_, lean_object* v_r_27_, lean_object* v_C_28_, lean_object* v_m_29_, lean_object* v_a_30_, lean_object* v_n_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Acc_recC___redArg(v_m_29_, v_a_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object* v_a_33_, lean_object* v_m_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Acc_recC___redArg(v_m_34_, v_a_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object* v_00_u03b1_36_, lean_object* v_r_37_, lean_object* v_C_38_, lean_object* v_a_39_, lean_object* v_n_40_, lean_object* v_m_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Acc_recC___redArg(v_m_41_, v_a_39_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object* v_F_43_, lean_object* v_x_u2081_44_, lean_object* v_h_45_, lean_object* v_ih_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_2(v_F_43_, v_x_u2081_44_, v_ih_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object* v_F_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___f_50_; lean_object* v___x_51_; 
v___f_50_ = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(v___f_50_, 0, v_F_48_);
v___x_51_ = l_Acc_recC___redArg(v___f_50_, v_x_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC(lean_object* v_00_u03b1_52_, lean_object* v_r_53_, lean_object* v_C_54_, lean_object* v_F_55_, lean_object* v_x_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; 
v___f_58_ = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(v___f_58_, 0, v_F_55_);
v___x_59_ = l_Acc_recC___redArg(v___f_58_, v_x_56_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg(lean_object* v_F_60_, lean_object* v_x_61_){
_start:
{
lean_object* v___f_62_; lean_object* v___x_63_; 
lean_inc(v_F_60_);
v___f_62_ = lean_alloc_closure((void*)(l_WellFounded_fixC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_62_, 0, v_F_60_);
v___x_63_ = lean_apply_2(v_F_60_, v_x_61_, v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg___lam__0(lean_object* v_F_64_, lean_object* v_y_65_, lean_object* v_x_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_WellFounded_fixC___redArg(v_F_64_, v_y_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC(lean_object* v_00_u03b1_68_, lean_object* v_C_69_, lean_object* v_r_70_, lean_object* v_hwf_71_, lean_object* v_F_72_, lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_WellFounded_fixC___redArg(v_F_72_, v_x_73_);
return v___x_74_;
}
}
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_WFComputable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
