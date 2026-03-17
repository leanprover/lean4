// Lean compiler output
// Module: Init.Data.Iterators.Internal.LawfulMonadLiftFunction
// Imports: public import Init.Control.Lawful.MonadLift
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
LEAN_EXPORT lean_object* l_Std_Internal_idToMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_idToMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_idToMonad___redArg(lean_object* v_inst_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_toApplicative_3_; lean_object* v_toPure_4_; lean_object* v___x_5_; 
v_toApplicative_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toApplicative_3_);
lean_dec_ref(v_inst_1_);
v_toPure_4_ = lean_ctor_get(v_toApplicative_3_, 1);
lean_inc(v_toPure_4_);
lean_dec_ref(v_toApplicative_3_);
v___x_5_ = lean_apply_2(v_toPure_4_, lean_box(0), v_x_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_idToMonad(lean_object* v_m_6_, lean_object* v_inst_7_, lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_toApplicative_10_; lean_object* v_toPure_11_; lean_object* v___x_12_; 
v_toApplicative_10_ = lean_ctor_get(v_inst_7_, 0);
lean_inc_ref(v_toApplicative_10_);
lean_dec_ref(v_inst_7_);
v_toPure_11_ = lean_ctor_get(v_toApplicative_10_, 1);
lean_inc(v_toPure_11_);
lean_dec_ref(v_toApplicative_10_);
v___x_12_ = lean_apply_2(v_toPure_11_, lean_box(0), v_x_9_);
return v___x_12_;
}
}
lean_object* runtime_initialize_Init_Control_Lawful_MonadLift(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Lawful_MonadLift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful_MonadLift(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_MonadLift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
}
#ifdef __cplusplus
}
#endif
