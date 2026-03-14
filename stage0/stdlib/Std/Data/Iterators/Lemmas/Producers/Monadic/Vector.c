// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic.Vector
// Imports: public import Std.Data.Iterators.Lemmas.Producers.Monadic.Array public import Std.Data.Iterators.Producers.Monadic.Vector public import Std.Data.Iterators.Lemmas.Consumers.Monadic public import Std.Data.Iterators.Lemmas.Producers.Monadic.List public import Init.Data.Array.Lemmas import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop import Init.Omega import Init.Data.Vector.Lemmas
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v_it_5_; lean_object* v_out_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_it_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_5_);
v_out_6_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_out_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_2(v_h__1_2_, v_it_5_, v_out_6_);
return v___x_7_;
}
case 1:
{
lean_object* v_it_8_; lean_object* v___x_9_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_it_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_8_);
lean_dec_ref(v_x_1_);
v___x_9_ = lean_apply_1(v_h__2_3_, v_it_8_);
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_apply_1(v_h__3_4_, v___x_10_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter(lean_object* v_m_12_, lean_object* v_00_u03b1_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter___redArg(v_x_15_, v_h__1_16_, v_h__2_17_, v_h__3_18_);
return v___x_19_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Vector(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
}
#ifdef __cplusplus
}
#endif
