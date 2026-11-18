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
LEAN_EXPORT lean_object* l_Acc_recOnC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_recOnC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Acc_recOnC___redArg(lean_object* v_a_23_, lean_object* v_intro_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Acc_recC___redArg(v_intro_24_, v_a_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Acc_recOnC(lean_object* v_00_u03b1_26_, lean_object* v_r_27_, lean_object* v_motive_28_, lean_object* v_a_29_, lean_object* v_t_30_, lean_object* v_intro_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Acc_recC___redArg(v_intro_31_, v_a_29_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object* v_m_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Acc_recC___redArg(v_m_33_, v_a_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object* v_00_u03b1_36_, lean_object* v_r_37_, lean_object* v_C_38_, lean_object* v_m_39_, lean_object* v_a_40_, lean_object* v_n_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Acc_recC___redArg(v_m_39_, v_a_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object* v_a_43_, lean_object* v_m_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Acc_recC___redArg(v_m_44_, v_a_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object* v_00_u03b1_46_, lean_object* v_r_47_, lean_object* v_C_48_, lean_object* v_a_49_, lean_object* v_n_50_, lean_object* v_m_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Acc_recC___redArg(v_m_51_, v_a_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object* v_F_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; 
lean_inc(v_F_53_);
v___f_55_ = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_55_, 0, v_F_53_);
v___x_56_ = lean_apply_2(v_F_53_, v_x_54_, v___f_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object* v_F_57_, lean_object* v_y_58_, lean_object* v_h_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_WellFounded_fixFC___redArg(v_F_57_, v_y_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC(lean_object* v_00_u03b1_61_, lean_object* v_r_62_, lean_object* v_C_63_, lean_object* v_F_64_, lean_object* v_x_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_WellFounded_fixFC___redArg(v_F_64_, v_x_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg(lean_object* v_F_68_, lean_object* v_x_69_){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; 
lean_inc(v_F_68_);
v___f_70_ = lean_alloc_closure((void*)(l_WellFounded_fixC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_70_, 0, v_F_68_);
v___x_71_ = lean_apply_2(v_F_68_, v_x_69_, v___f_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg___lam__0(lean_object* v_F_72_, lean_object* v_y_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_WellFounded_fixC___redArg(v_F_72_, v_y_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC(lean_object* v_00_u03b1_76_, lean_object* v_C_77_, lean_object* v_r_78_, lean_object* v_hwf_79_, lean_object* v_F_80_, lean_object* v_x_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_WellFounded_fixC___redArg(v_F_80_, v_x_81_);
return v___x_82_;
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
