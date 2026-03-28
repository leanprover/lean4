// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Attach
// Imports: public import Init.Data.Iterators.Combinators.Monadic.Attach
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
LEAN_EXPORT lean_object* l_Std_Iter_attachWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_attachWith___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_attachWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_attachWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_attachWith___redArg(lean_object* v_it_1_){
_start:
{
lean_inc(v_it_1_);
return v_it_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_attachWith___redArg___boxed(lean_object* v_it_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_Iter_attachWith___redArg(v_it_2_);
lean_dec(v_it_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_attachWith(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_inst_6_, lean_object* v_it_7_, lean_object* v_P_8_, lean_object* v_h_9_){
_start:
{
lean_inc(v_it_7_);
return v_it_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_attachWith___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_inst_12_, lean_object* v_it_13_, lean_object* v_P_14_, lean_object* v_h_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Iter_attachWith(v_00_u03b1_10_, v_00_u03b2_11_, v_inst_12_, v_it_13_, v_P_14_, v_h_15_);
lean_dec(v_it_13_);
lean_dec(v_inst_12_);
return v_res_16_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
