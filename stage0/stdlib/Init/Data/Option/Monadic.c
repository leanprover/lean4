// Lean compiler output
// Module: Init.Data.Option.Monadic
// Imports: import all Init.Data.Option.Instances public import Init.Control.Lawful public import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Monadic_0__Option_instForIn_x27InferInstanceMembershipOfMonad_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Monadic_0__Option_instForIn_x27InferInstanceMembershipOfMonad_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Monadic_0__Option_instForIn_x27InferInstanceMembershipOfMonad_match__1_splitter___redArg(lean_object* v_____do__lift_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_____do__lift_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_____do__lift_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_a_6_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_____do__lift_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Monadic_0__Option_instForIn_x27InferInstanceMembershipOfMonad_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_____do__lift_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_____do__lift_10_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v_a_13_ = lean_ctor_get(v_____do__lift_10_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_____do__lift_10_, 1);
v___x_14_ = lean_apply_1(v_h__1_11_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_a_15_ = lean_ctor_get(v_____do__lift_10_, 0);
lean_inc(v_a_15_);
lean_dec_ref_known(v_____do__lift_10_, 1);
v___x_16_ = lean_apply_1(v_h__2_12_, v_a_15_);
return v___x_16_;
}
}
}
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Monadic(builtin);
}
#ifdef __cplusplus
}
#endif
