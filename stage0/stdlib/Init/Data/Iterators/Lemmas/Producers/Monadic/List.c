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
lean_object* v___x_15_; 
v___x_15_ = l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(v_it_12_, v_h__1_13_, v_h__2_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
_start:
{
switch(lean_obj_tag(v_x_16_))
{
case 0:
{
lean_object* v_it_20_; lean_object* v_out_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__2_18_);
v_it_20_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_it_20_);
v_out_21_ = lean_ctor_get(v_x_16_, 1);
lean_inc(v_out_21_);
lean_dec_ref(v_x_16_);
v___x_22_ = lean_apply_2(v_h__1_17_, v_it_20_, v_out_21_);
return v___x_22_;
}
case 1:
{
lean_object* v_it_23_; lean_object* v___x_24_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__1_17_);
v_it_23_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_it_23_);
lean_dec_ref(v_x_16_);
v___x_24_ = lean_apply_1(v_h__2_18_, v_it_23_);
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_18_);
lean_dec(v_h__1_17_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_apply_1(v_h__3_19_, v___x_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_m_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_, lean_object* v_h__3_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l___private_Init_Data_Iterators_Lemmas_Producers_Monadic_List_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(v_x_31_, v_h__1_32_, v_h__2_33_, v_h__3_34_);
return v___x_35_;
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
