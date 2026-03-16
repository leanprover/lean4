// Lean compiler output
// Module: Init.Data.Slice.List.Lemmas
// Imports: import all Init.Data.Slice.List.Basic public import Init.Data.Slice.List.Iterator import all Init.Data.Slice.List.Iterator import all Init.Data.Slice.Operations import all Init.Data.Range.Polymorphic.Iterators import all Init.Data.Range.Polymorphic.Lemmas import Init.Data.Iterators.Lemmas.Combinators.Take import Init.Data.Iterators.Lemmas.Producers.List import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop import Init.Data.Nat.Simproc import Init.Data.Slice.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter(lean_object* v_motive_8_, lean_object* v_x_9_, lean_object* v_h__1_10_, lean_object* v_h__2_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter___redArg(v_x_9_, v_h__1_10_, v_h__2_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter___redArg(lean_object* v_x_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_14_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_apply_1(v_h__2_15_, v___x_16_);
return v___x_17_;
}
else
{
lean_object* v_val_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_15_);
v_val_18_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_val_18_);
lean_dec_ref(v_x_13_);
v___x_19_ = lean_apply_1(v_h__1_14_, v_val_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter(lean_object* v_motive_20_, lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter___redArg(v_x_21_, v_h__1_22_, v_h__2_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter___redArg(lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec(v_h__2_27_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_apply_1(v_h__1_26_, v___x_28_);
return v___x_29_;
}
else
{
lean_object* v_val_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_26_);
v_val_30_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_val_30_);
lean_dec_ref(v_x_25_);
v___x_31_ = lean_apply_1(v_h__2_27_, v_val_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter(lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter___redArg(v_x_33_, v_h__1_34_, v_h__2_35_);
return v___x_36_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_List_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_List_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Producers_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_List_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
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
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_List_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_List_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_List_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_List_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Producers_List(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_List_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_List_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_List_Iterator(builtin);
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
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Producers_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_List_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
