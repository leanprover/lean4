// Lean compiler output
// Module: Init.Data.Dyadic.Inv
// Imports: public import Init.Data.Dyadic.Basic import Init.Data.Rat.Lemmas
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
lean_object* l_Dyadic_toRat(lean_object*);
lean_object* l_Rat_inv(lean_object*);
lean_object* l_Rat_toDyadic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_invAtPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_invAtPrec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_invAtPrec(lean_object* v_x_1_, lean_object* v_prec_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = l_Dyadic_toRat(v_x_1_);
v___x_4_ = l_Rat_inv(v___x_3_);
v___x_5_ = l_Rat_toDyadic(v___x_4_, v_prec_2_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_invAtPrec___boxed(lean_object* v_x_6_, lean_object* v_prec_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Dyadic_invAtPrec(v_x_6_, v_prec_7_);
lean_dec(v_prec_7_);
return v_res_8_;
}
}
lean_object* runtime_initialize_Init_Data_Dyadic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Dyadic_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Dyadic_Inv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Dyadic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Dyadic_Inv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Dyadic_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Dyadic_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Dyadic_Inv(builtin);
}
#ifdef __cplusplus
}
#endif
