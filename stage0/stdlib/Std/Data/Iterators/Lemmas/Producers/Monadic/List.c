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
if (lean_obj_tag(v_l_11_) == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_h__2_13_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_apply_1(v_h__1_12_, v___x_14_);
return v___x_15_;
}
else
{
lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_12_);
v_head_16_ = lean_ctor_get(v_l_11_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_l_11_, 1);
lean_inc(v_tail_17_);
lean_dec_ref(v_l_11_);
v___x_18_ = lean_apply_2(v_h__2_13_, v_head_16_, v_tail_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(lean_object* v_it_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
if (lean_obj_tag(v_it_19_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_21_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_20_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_20_);
v_head_24_ = lean_ctor_get(v_it_19_, 0);
lean_inc(v_head_24_);
v_tail_25_ = lean_ctor_get(v_it_19_, 1);
lean_inc(v_tail_25_);
lean_dec_ref(v_it_19_);
v___x_26_ = lean_apply_2(v_h__2_21_, v_head_24_, v_tail_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(lean_object* v_m_27_, lean_object* v_00_u03b1_28_, lean_object* v_motive_29_, lean_object* v_it_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (lean_obj_tag(v_it_30_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_32_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__1_31_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_head_35_; lean_object* v_tail_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_31_);
v_head_35_ = lean_ctor_get(v_it_30_, 0);
lean_inc(v_head_35_);
v_tail_36_ = lean_ctor_get(v_it_30_, 1);
lean_inc(v_tail_36_);
lean_dec_ref(v_it_30_);
v___x_37_ = lean_apply_2(v_h__2_32_, v_head_35_, v_tail_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_, lean_object* v_h__3_41_){
_start:
{
switch(lean_obj_tag(v_x_38_))
{
case 0:
{
lean_object* v_it_42_; lean_object* v_out_43_; lean_object* v___x_44_; 
lean_dec(v_h__3_41_);
lean_dec(v_h__2_40_);
v_it_42_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_it_42_);
v_out_43_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_out_43_);
lean_dec_ref(v_x_38_);
v___x_44_ = lean_apply_2(v_h__1_39_, v_it_42_, v_out_43_);
return v___x_44_;
}
case 1:
{
lean_object* v_it_45_; lean_object* v___x_46_; 
lean_dec(v_h__3_41_);
lean_dec(v_h__1_39_);
v_it_45_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_it_45_);
lean_dec_ref(v_x_38_);
v___x_46_ = lean_apply_1(v_h__2_40_, v_it_45_);
return v___x_46_;
}
default: 
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_40_);
lean_dec(v_h__1_39_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__3_41_, v___x_47_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(lean_object* v_m_49_, lean_object* v_00_u03b1_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_, lean_object* v_h__3_55_){
_start:
{
switch(lean_obj_tag(v_x_52_))
{
case 0:
{
lean_object* v_it_56_; lean_object* v_out_57_; lean_object* v___x_58_; 
lean_dec(v_h__3_55_);
lean_dec(v_h__2_54_);
v_it_56_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_it_56_);
v_out_57_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_out_57_);
lean_dec_ref(v_x_52_);
v___x_58_ = lean_apply_2(v_h__1_53_, v_it_56_, v_out_57_);
return v___x_58_;
}
case 1:
{
lean_object* v_it_59_; lean_object* v___x_60_; 
lean_dec(v_h__3_55_);
lean_dec(v_h__1_53_);
v_it_59_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_it_59_);
lean_dec_ref(v_x_52_);
v___x_60_ = lean_apply_1(v_h__2_54_, v_it_59_);
return v___x_60_;
}
default: 
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_h__2_54_);
lean_dec(v_h__1_53_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_apply_1(v_h__3_55_, v___x_61_);
return v___x_62_;
}
}
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
