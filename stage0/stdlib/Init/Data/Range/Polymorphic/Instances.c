// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Instances
// Imports: public import Init.Data.Range.Polymorphic.Basic import Init.Data.Nat.Lemmas import Init.ByCases import Init.Data.Option.Lemmas import Init.Omega
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_HasSize_ofClosed___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_HasSize_ofClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_HasSize_ofClosed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_HasSize_ofClosed___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_lo_2_, lean_object* v_hi_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_lo_2_, v_hi_3_);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_sub(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_HasSize_ofClosed___redArg(lean_object* v_inst_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(l_Std_Rxo_HasSize_ofClosed___redArg___lam__0), 3, 1);
lean_closure_set(v___f_8_, 0, v_inst_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_HasSize_ofClosed(lean_object* v_00_u03b1_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = lean_alloc_closure((void*)(l_Std_Rxo_HasSize_ofClosed___redArg___lam__0), 3, 1);
lean_closure_set(v___f_11_, 0, v_inst_10_);
return v___f_11_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
