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
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v_h__1_10_);
v___x_12_ = lean_box(0);
v___x_13_ = lean_apply_1(v_h__2_11_, v___x_12_);
return v___x_13_;
}
else
{
lean_object* v_val_14_; lean_object* v___x_15_; 
lean_dec(v_h__2_11_);
v_val_14_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_val_14_);
lean_dec_ref(v_x_9_);
v___x_15_ = lean_apply_1(v_h__1_10_, v_val_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter___redArg(lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_17_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__2_18_, v___x_19_);
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_18_);
v_val_21_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_val_21_);
lean_dec_ref(v_x_16_);
v___x_22_ = lean_apply_1(v_h__1_17_, v_val_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter(lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_h__1_25_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_apply_1(v_h__2_26_, v___x_27_);
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_26_);
v_val_29_ = lean_ctor_get(v_x_24_, 0);
lean_inc(v_val_29_);
lean_dec_ref(v_x_24_);
v___x_30_ = lean_apply_1(v_h__1_25_, v_val_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter___redArg(lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_33_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__1_32_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_32_);
v_val_36_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_val_36_);
lean_dec_ref(v_x_31_);
v___x_37_ = lean_apply_1(v_h__2_33_, v_val_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter(lean_object* v_motive_38_, lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_41_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_apply_1(v_h__1_40_, v___x_42_);
return v___x_43_;
}
else
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_h__1_40_);
v_val_44_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_val_44_);
lean_dec_ref(v_x_39_);
v___x_45_ = lean_apply_1(v_h__2_41_, v_val_44_);
return v___x_45_;
}
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
