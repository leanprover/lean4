// Lean compiler output
// Module: Std.Data.Iterators.Producers.Array
// Imports: public import Std.Data.Iterators.Producers.Monadic.Array
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
LEAN_EXPORT lean_object* l_Array_iterFromIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdx___redArg(lean_object* v_l_1_, lean_object* v_pos_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_l_1_);
lean_ctor_set(v___x_3_, 1, v_pos_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Array_iterFromIdx(lean_object* v_00_u03b1_4_, lean_object* v_l_5_, lean_object* v_pos_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_l_5_);
lean_ctor_set(v___x_7_, 1, v_pos_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Array_iter___redArg(lean_object* v_l_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_l_8_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Array_iter(lean_object* v_00_u03b1_11_, lean_object* v_l_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_l_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
return v___x_14_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Array(builtin);
}
#ifdef __cplusplus
}
#endif
