// Lean compiler output
// Module: Std.Data.Iterators.Combinators.TakeWhile
// Imports: public import Std.Data.Iterators.Combinators.Monadic.TakeWhile
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
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile___redArg(lean_object* v_it_1_){
_start:
{
lean_inc(v_it_1_);
return v_it_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile___redArg___boxed(lean_object* v_it_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_Iter_takeWhile___redArg(v_it_2_);
lean_dec(v_it_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_P_6_, lean_object* v_it_7_){
_start:
{
lean_inc(v_it_7_);
return v_it_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_takeWhile___boxed(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b2_9_, lean_object* v_P_10_, lean_object* v_it_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Iter_takeWhile(v_00_u03b1_8_, v_00_u03b2_9_, v_P_10_, v_it_11_);
lean_dec(v_it_11_);
lean_dec_ref(v_P_10_);
return v_res_12_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_TakeWhile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
}
#ifdef __cplusplus
}
#endif
