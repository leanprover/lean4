// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic.List
// Imports: public import Init.Data.Iterators.Lemmas.Producers.Monadic.List public import Std.Data.Iterators.Lemmas.Equivalence.Basic
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter___redArg(lean_object* v_l_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_l_1_) == 0)
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
v_head_6_ = lean_ctor_get(v_l_1_, 0);
lean_inc(v_head_6_);
v_tail_7_ = lean_ctor_get(v_l_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref(v_l_1_);
v___x_8_ = lean_apply_2(v_h__2_3_, v_head_6_, v_tail_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter(lean_object* v_00_u03b2_9_, lean_object* v_motive_10_, lean_object* v_l_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter___redArg(v_l_11_, v_h__1_12_, v_h__2_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(lean_object* v_it_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (lean_obj_tag(v_it_15_) == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_17_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_apply_1(v_h__1_16_, v___x_18_);
return v___x_19_;
}
else
{
lean_object* v_head_20_; lean_object* v_tail_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_16_);
v_head_20_ = lean_ctor_get(v_it_15_, 0);
lean_inc(v_head_20_);
v_tail_21_ = lean_ctor_get(v_it_15_, 1);
lean_inc(v_tail_21_);
lean_dec_ref(v_it_15_);
v___x_22_ = lean_apply_2(v_h__2_17_, v_head_20_, v_tail_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(lean_object* v_m_23_, lean_object* v_00_u03b1_24_, lean_object* v_motive_25_, lean_object* v_it_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(v_it_26_, v_h__1_27_, v_h__2_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_, lean_object* v_h__3_33_){
_start:
{
switch(lean_obj_tag(v_x_30_))
{
case 0:
{
lean_object* v_it_34_; lean_object* v_out_35_; lean_object* v___x_36_; 
lean_dec(v_h__3_33_);
lean_dec(v_h__2_32_);
v_it_34_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_it_34_);
v_out_35_ = lean_ctor_get(v_x_30_, 1);
lean_inc(v_out_35_);
lean_dec_ref(v_x_30_);
v___x_36_ = lean_apply_2(v_h__1_31_, v_it_34_, v_out_35_);
return v___x_36_;
}
case 1:
{
lean_object* v_it_37_; lean_object* v___x_38_; 
lean_dec(v_h__3_33_);
lean_dec(v_h__1_31_);
v_it_37_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_it_37_);
lean_dec_ref(v_x_30_);
v___x_38_ = lean_apply_1(v_h__2_32_, v_it_37_);
return v___x_38_;
}
default: 
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_32_);
lean_dec(v_h__1_31_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__3_33_, v___x_39_);
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(lean_object* v_m_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(v_x_44_, v_h__1_45_, v_h__2_46_, v_h__3_47_);
return v___x_48_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
}
#ifdef __cplusplus
}
#endif
