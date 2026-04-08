// Lean compiler output
// Module: Init.Data.Iterators.Producers.List
// Imports: public import Init.Data.Iterators.Producers.Monadic.List
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
LEAN_EXPORT lean_object* l_List_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_iter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_iter___redArg(lean_object* v_l_1_){
_start:
{
lean_inc(v_l_1_);
return v_l_1_;
}
}
LEAN_EXPORT lean_object* l_List_iter___redArg___boxed(lean_object* v_l_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_List_iter___redArg(v_l_2_);
lean_dec(v_l_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_List_iter(lean_object* v_00_u03b1_4_, lean_object* v_l_5_){
_start:
{
lean_inc(v_l_5_);
return v_l_5_;
}
}
LEAN_EXPORT lean_object* l_List_iter___boxed(lean_object* v_00_u03b1_6_, lean_object* v_l_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_List_iter(v_00_u03b1_6_, v_l_7_);
lean_dec(v_l_7_);
return v_res_8_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Producers_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Producers_List(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Producers_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Producers_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Producers_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Producers_List(builtin);
}
#ifdef __cplusplus
}
#endif
