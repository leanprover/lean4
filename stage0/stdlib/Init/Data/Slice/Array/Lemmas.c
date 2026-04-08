// Lean compiler output
// Module: Init.Data.Slice.Array.Lemmas
// Imports: public import Init.Data.Slice.Array.Iterator import all Init.Data.Array.Subarray import all Init.Data.Slice.Array.Basic import Init.Data.Slice.Lemmas import all Init.Data.Slice.Array.Iterator import all Init.Data.Slice.Operations import all Init.Data.Range.Polymorphic.Iterators import all Init.Data.Range.Polymorphic.Lemmas import Init.Data.Slice.List.Lemmas public import Init.Data.List.Control public import Init.Data.Nat.MinMax public import Init.Data.Slice.Array.Basic import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop public import Init.Data.Array.Subarray.Split import all Init.Data.Array.Subarray.Split import Init.Data.Slice.InternalLemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Lemmas_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Lemmas_0__Std_IterStep_successor_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Lemmas_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_Array_Lemmas_0__Std_IterStep_successor_match__1_splitter(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v_it_19_; lean_object* v_out_20_; lean_object* v___x_21_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__2_17_);
v_it_19_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_it_19_);
v_out_20_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_out_20_);
lean_dec_ref(v_x_15_);
v___x_21_ = lean_apply_2(v_h__1_16_, v_it_19_, v_out_20_);
return v___x_21_;
}
case 1:
{
lean_object* v_it_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__1_16_);
v_it_22_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_it_22_);
lean_dec_ref(v_x_15_);
v___x_23_ = lean_apply_1(v_h__2_17_, v_it_22_);
return v___x_23_;
}
default: 
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_17_);
lean_dec(v_h__1_16_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__3_18_, v___x_24_);
return v___x_25_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_InternalLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_Array_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_InternalLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_Array_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_InternalLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_InternalLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_Array_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
