// Lean compiler output
// Module: Init.While
// Imports: public import Init.Core
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
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(lean_object* v_inst_3_, lean_object* v_f_4_, lean_object* v_b_5_){
_start:
{
lean_object* v_toApplicative_6_; lean_object* v_toBind_7_; lean_object* v_toPure_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___x_12_; 
v_toApplicative_6_ = lean_ctor_get(v_inst_3_, 0);
v_toBind_7_ = lean_ctor_get(v_inst_3_, 1);
lean_inc(v_toBind_7_);
v_toPure_8_ = lean_ctor_get(v_toApplicative_6_, 1);
lean_inc(v_toPure_8_);
v___x_9_ = lean_box(0);
lean_inc(v_f_4_);
v___x_10_ = lean_apply_2(v_f_4_, v___x_9_, v_b_5_);
v___f_11_ = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_11_, 0, v_toPure_8_);
lean_closure_set(v___f_11_, 1, v_inst_3_);
lean_closure_set(v___f_11_, 2, v_f_4_);
v___x_12_ = lean_apply_4(v_toBind_7_, lean_box(0), lean_box(0), v___x_10_, v___f_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg___lam__0(lean_object* v_toPure_13_, lean_object* v_inst_14_, lean_object* v_f_15_, lean_object* v_____do__lift_16_){
_start:
{
if (lean_obj_tag(v_____do__lift_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_18_; 
lean_dec(v_f_15_);
lean_dec_ref(v_inst_14_);
v_a_17_ = lean_ctor_get(v_____do__lift_16_, 0);
lean_inc(v_a_17_);
lean_dec_ref(v_____do__lift_16_);
v___x_18_ = lean_apply_2(v_toPure_13_, lean_box(0), v_a_17_);
return v___x_18_;
}
else
{
lean_object* v_a_19_; lean_object* v___x_20_; 
lean_dec(v_toPure_13_);
v_a_19_ = lean_ctor_get(v_____do__lift_16_, 0);
lean_inc(v_a_19_);
lean_dec_ref(v_____do__lift_16_);
v___x_20_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_14_, v_f_15_, v_a_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object* v_00_u03b2_21_, lean_object* v_m_22_, lean_object* v_inst_23_, lean_object* v_f_24_, lean_object* v_b_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_23_, v_f_24_, v_b_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object* v_inst_27_, lean_object* v_init_28_, lean_object* v_f_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_27_, v_f_29_, v_init_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object* v_00_u03b2_31_, lean_object* v_m_32_, lean_object* v_inst_33_, lean_object* v_x_34_, lean_object* v_init_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_33_, v_f_36_, v_init_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object* v_inst_38_, lean_object* v_00_u03b2_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_38_, v___y_42_, v___y_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object* v_inst_44_){
_start:
{
lean_object* v___f_45_; 
v___f_45_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_45_, 0, v_inst_44_);
return v___f_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object* v_m_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___f_48_; 
v___f_48_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_48_, 0, v_inst_47_);
return v___f_48_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_While(builtin);
}
#ifdef __cplusplus
}
#endif
