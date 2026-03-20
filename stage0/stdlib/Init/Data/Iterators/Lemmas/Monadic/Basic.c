// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Monadic.Basic
// Imports: public import Init.Data.Iterators.Basic
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
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg___lam__0___boxed(lean_object* v_step_1_, lean_object* v_it_x27_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_IterM_inductSteps___redArg___lam__0(v_step_1_, v_it_x27_2_, v_x_3_, v_x_4_);
lean_dec(v_x_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg___lam__1(lean_object* v_step_6_, lean_object* v_it_x27_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Std_IterM_inductSteps___redArg(v_step_6_, v_it_x27_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg(lean_object* v_step_10_, lean_object* v_it_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___x_14_; 
lean_inc(v_step_10_);
v___f_12_ = lean_alloc_closure((void*)(l_Std_IterM_inductSteps___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_12_, 0, v_step_10_);
lean_inc(v_step_10_);
v___f_13_ = lean_alloc_closure((void*)(l_Std_IterM_inductSteps___redArg___lam__1), 3, 1);
lean_closure_set(v___f_13_, 0, v_step_10_);
v___x_14_ = lean_apply_3(v_step_10_, v_it_11_, v___f_12_, v___f_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___redArg___lam__0(lean_object* v_step_15_, lean_object* v_it_x27_16_, lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Std_IterM_inductSteps___redArg(v_step_15_, v_it_x27_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps(lean_object* v_00_u03b1_20_, lean_object* v_m_21_, lean_object* v_00_u03b2_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_motive_25_, lean_object* v_step_26_, lean_object* v_it_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_IterM_inductSteps___redArg(v_step_26_, v_it_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSteps___boxed(lean_object* v_00_u03b1_29_, lean_object* v_m_30_, lean_object* v_00_u03b2_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_motive_34_, lean_object* v_step_35_, lean_object* v_it_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_IterM_inductSteps(v_00_u03b1_29_, v_m_30_, v_00_u03b2_31_, v_inst_32_, v_inst_33_, v_motive_34_, v_step_35_, v_it_36_);
lean_dec(v_inst_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips___redArg(lean_object* v_step_38_, lean_object* v_it_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___x_41_; 
lean_inc(v_step_38_);
v___f_40_ = lean_alloc_closure((void*)(l_Std_IterM_inductSkips___redArg___lam__0), 3, 1);
lean_closure_set(v___f_40_, 0, v_step_38_);
v___x_41_ = lean_apply_2(v_step_38_, v_it_39_, v___f_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips___redArg___lam__0(lean_object* v_step_42_, lean_object* v_it_x27_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Std_IterM_inductSkips___redArg(v_step_42_, v_it_x27_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips(lean_object* v_00_u03b1_46_, lean_object* v_m_47_, lean_object* v_00_u03b2_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_motive_51_, lean_object* v_step_52_, lean_object* v_it_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Std_IterM_inductSkips___redArg(v_step_52_, v_it_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_inductSkips___boxed(lean_object* v_00_u03b1_55_, lean_object* v_m_56_, lean_object* v_00_u03b2_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_motive_60_, lean_object* v_step_61_, lean_object* v_it_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_IterM_inductSkips(v_00_u03b1_55_, v_m_56_, v_00_u03b2_57_, v_inst_58_, v_inst_59_, v_motive_60_, v_step_61_, v_it_62_);
lean_dec(v_inst_58_);
return v_res_63_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
