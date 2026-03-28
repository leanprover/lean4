// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Access
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
LEAN_EXPORT lean_object* l_Std_IterM_nextAtIdx_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_nextAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_nextAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_nextAtIdx_x3f___redArg(lean_object* v_inst_1_, lean_object* v_it_2_, lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_it_2_, v_n_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_nextAtIdx_x3f(lean_object* v_00_u03b1_5_, lean_object* v_m_6_, lean_object* v_00_u03b2_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_it_10_, lean_object* v_n_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_2(v_inst_9_, v_it_10_, v_n_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_nextAtIdx_x3f___boxed(lean_object* v_00_u03b1_13_, lean_object* v_m_14_, lean_object* v_00_u03b2_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_it_18_, lean_object* v_n_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_IterM_nextAtIdx_x3f(v_00_u03b1_13_, v_m_14_, v_00_u03b2_15_, v_inst_16_, v_inst_17_, v_it_18_, v_n_19_);
lean_dec(v_inst_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___redArg___lam__0(lean_object* v_toPure_21_, lean_object* v_____do__lift_22_){
_start:
{
if (lean_obj_tag(v_____do__lift_22_) == 0)
{
lean_object* v_out_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_out_23_ = lean_ctor_get(v_____do__lift_22_, 1);
lean_inc(v_out_23_);
v___x_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_24_, 0, v_out_23_);
v___x_25_ = lean_apply_2(v_toPure_21_, lean_box(0), v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_2(v_toPure_21_, lean_box(0), v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed(lean_object* v_toPure_28_, lean_object* v_____do__lift_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_IterM_atIdx_x3f___redArg___lam__0(v_toPure_28_, v_____do__lift_29_);
lean_dec(v_____do__lift_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___redArg(lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_it_33_, lean_object* v_n_34_){
_start:
{
lean_object* v_toApplicative_35_; lean_object* v_toBind_36_; lean_object* v_toPure_37_; lean_object* v___x_38_; lean_object* v___f_39_; lean_object* v___x_40_; 
v_toApplicative_35_ = lean_ctor_get(v_inst_32_, 0);
lean_inc_ref(v_toApplicative_35_);
v_toBind_36_ = lean_ctor_get(v_inst_32_, 1);
lean_inc(v_toBind_36_);
lean_dec_ref(v_inst_32_);
v_toPure_37_ = lean_ctor_get(v_toApplicative_35_, 1);
lean_inc(v_toPure_37_);
lean_dec_ref(v_toApplicative_35_);
v___x_38_ = lean_apply_2(v_inst_31_, v_it_33_, v_n_34_);
v___f_39_ = lean_alloc_closure((void*)(l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_39_, 0, v_toPure_37_);
v___x_40_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v___x_38_, v___f_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f(lean_object* v_00_u03b1_41_, lean_object* v_m_42_, lean_object* v_00_u03b2_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_it_47_, lean_object* v_n_48_){
_start:
{
lean_object* v_toApplicative_49_; lean_object* v_toBind_50_; lean_object* v_toPure_51_; lean_object* v___x_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_toApplicative_49_ = lean_ctor_get(v_inst_46_, 0);
lean_inc_ref(v_toApplicative_49_);
v_toBind_50_ = lean_ctor_get(v_inst_46_, 1);
lean_inc(v_toBind_50_);
lean_dec_ref(v_inst_46_);
v_toPure_51_ = lean_ctor_get(v_toApplicative_49_, 1);
lean_inc(v_toPure_51_);
lean_dec_ref(v_toApplicative_49_);
v___x_52_ = lean_apply_2(v_inst_45_, v_it_47_, v_n_48_);
v___f_53_ = lean_alloc_closure((void*)(l_Std_IterM_atIdx_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_53_, 0, v_toPure_51_);
v___x_54_ = lean_apply_4(v_toBind_50_, lean_box(0), lean_box(0), v___x_52_, v___f_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_atIdx_x3f___boxed(lean_object* v_00_u03b1_55_, lean_object* v_m_56_, lean_object* v_00_u03b2_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_it_61_, lean_object* v_n_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_IterM_atIdx_x3f(v_00_u03b1_55_, v_m_56_, v_00_u03b2_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_it_61_, v_n_62_);
lean_dec(v_inst_58_);
return v_res_63_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
}
#ifdef __cplusplus
}
#endif
