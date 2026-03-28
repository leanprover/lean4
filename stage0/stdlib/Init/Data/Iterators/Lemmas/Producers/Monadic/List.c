// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Producers.Monadic.List
// Imports: public import Init.Data.Iterators.Producers.Monadic.List import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.List.ToArray
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(lean_object* v_it_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_it_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_2_);
v_head_6_ = lean_ctor_get(v_it_1_, 0);
lean_inc(v_head_6_);
v_tail_7_ = lean_ctor_get(v_it_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref(v_it_1_);
v___x_8_ = lean_apply_2(v_h__2_3_, v_head_6_, v_tail_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(lean_object* v_m_9_, lean_object* v_00_u03b1_10_, lean_object* v_motive_11_, lean_object* v_it_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
if (lean_obj_tag(v_it_12_) == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_14_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_apply_1(v_h__1_13_, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_19_; 
lean_dec(v_h__1_13_);
v_head_17_ = lean_ctor_get(v_it_12_, 0);
lean_inc(v_head_17_);
v_tail_18_ = lean_ctor_get(v_it_12_, 1);
lean_inc(v_tail_18_);
lean_dec_ref(v_it_12_);
v___x_19_ = lean_apply_2(v_h__2_14_, v_head_17_, v_tail_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_, lean_object* v_h__3_23_){
_start:
{
switch(lean_obj_tag(v_x_20_))
{
case 0:
{
lean_object* v_it_24_; lean_object* v_out_25_; lean_object* v___x_26_; 
lean_dec(v_h__3_23_);
lean_dec(v_h__2_22_);
v_it_24_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_it_24_);
v_out_25_ = lean_ctor_get(v_x_20_, 1);
lean_inc(v_out_25_);
lean_dec_ref(v_x_20_);
v___x_26_ = lean_apply_2(v_h__1_21_, v_it_24_, v_out_25_);
return v___x_26_;
}
case 1:
{
lean_object* v_it_27_; lean_object* v___x_28_; 
lean_dec(v_h__3_23_);
lean_dec(v_h__1_21_);
v_it_27_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_it_27_);
lean_dec_ref(v_x_20_);
v___x_28_ = lean_apply_1(v_h__2_22_, v_it_27_);
return v___x_28_;
}
default: 
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_22_);
lean_dec(v_h__1_21_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_apply_1(v_h__3_23_, v___x_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_m_33_, lean_object* v_motive_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_){
_start:
{
switch(lean_obj_tag(v_x_35_))
{
case 0:
{
lean_object* v_it_39_; lean_object* v_out_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_38_);
lean_dec(v_h__2_37_);
v_it_39_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_it_39_);
v_out_40_ = lean_ctor_get(v_x_35_, 1);
lean_inc(v_out_40_);
lean_dec_ref(v_x_35_);
v___x_41_ = lean_apply_2(v_h__1_36_, v_it_39_, v_out_40_);
return v___x_41_;
}
case 1:
{
lean_object* v_it_42_; lean_object* v___x_43_; 
lean_dec(v_h__3_38_);
lean_dec(v_h__1_36_);
v_it_42_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_it_42_);
lean_dec_ref(v_x_35_);
v___x_43_ = lean_apply_1(v_h__2_37_, v_it_42_);
return v___x_43_;
}
default: 
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_h__2_37_);
lean_dec(v_h__1_36_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_apply_1(v_h__3_38_, v___x_44_);
return v___x_45_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Producers_Monadic_List(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
}
#ifdef __cplusplus
}
#endif
