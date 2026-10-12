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
lean_object* l_Acc_wfRel___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Acc_wfRel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Acc_wfRel___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Acc_wfRel___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Acc_wfRel___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Acc_wfRel(lean_object* v_00_u03b1_6_, lean_object* v_r_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg(lean_object* v_intro_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; 
lean_inc(v_intro_9_);
v___f_11_ = lean_alloc_closure((void*)(l_Acc_recC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_11_, 0, v_intro_9_);
v___x_12_ = lean_apply_3(v_intro_9_, v_a_10_, lean_box(0), v___f_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC___redArg___lam__0(lean_object* v_intro_13_, lean_object* v_x_14_, lean_object* v_hr_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Acc_recC___redArg(v_intro_13_, v_x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Acc_recC(lean_object* v_00_u03b1_17_, lean_object* v_r_18_, lean_object* v_motive_19_, lean_object* v_intro_20_, lean_object* v_a_21_, lean_object* v_t_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Acc_recC___redArg(v_intro_20_, v_a_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC___redArg(lean_object* v_m_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Acc_recC___redArg(v_m_24_, v_a_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecC(lean_object* v_00_u03b1_27_, lean_object* v_r_28_, lean_object* v_C_29_, lean_object* v_m_30_, lean_object* v_a_31_, lean_object* v_n_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Acc_recC___redArg(v_m_30_, v_a_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC___redArg(lean_object* v_a_34_, lean_object* v_m_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Acc_recC___redArg(v_m_35_, v_a_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Acc_ndrecOnC(lean_object* v_00_u03b1_37_, lean_object* v_r_38_, lean_object* v_C_39_, lean_object* v_a_40_, lean_object* v_n_41_, lean_object* v_m_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Acc_recC___redArg(v_m_42_, v_a_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg___lam__0(lean_object* v_F_44_, lean_object* v_x_u2081_45_, lean_object* v_h_46_, lean_object* v_ih_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_apply_2(v_F_44_, v_x_u2081_45_, v_ih_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC___redArg(lean_object* v_F_49_, lean_object* v_x_50_){
_start:
{
lean_object* v___f_51_; lean_object* v___x_52_; 
v___f_51_ = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(v___f_51_, 0, v_F_49_);
v___x_52_ = l_Acc_recC___redArg(v___f_51_, v_x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixFC(lean_object* v_00_u03b1_53_, lean_object* v_r_54_, lean_object* v_C_55_, lean_object* v_F_56_, lean_object* v_x_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___x_60_; 
v___f_59_ = lean_alloc_closure((void*)(l_WellFounded_fixFC___redArg___lam__0), 4, 1);
lean_closure_set(v___f_59_, 0, v_F_56_);
v___x_60_ = l_Acc_recC___redArg(v___f_59_, v_x_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg(lean_object* v_F_61_, lean_object* v_x_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; 
lean_inc(v_F_61_);
v___f_63_ = lean_alloc_closure((void*)(l_WellFounded_fixC___redArg___lam__0), 3, 1);
lean_closure_set(v___f_63_, 0, v_F_61_);
v___x_64_ = lean_apply_2(v_F_61_, v_x_62_, v___f_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC___redArg___lam__0(lean_object* v_F_65_, lean_object* v_y_66_, lean_object* v_x_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_WellFounded_fixC___redArg(v_F_65_, v_y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_fixC(lean_object* v_00_u03b1_69_, lean_object* v_C_70_, lean_object* v_r_71_, lean_object* v_hwf_72_, lean_object* v_F_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_WellFounded_fixC___redArg(v_F_73_, v_x_74_);
return v___x_75_;
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
