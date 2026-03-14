// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Append
// Imports: public import Init.Data.Iterators.Combinators.Monadic.Append public import Init.Data.Iterators.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.Iterators.Lemmas.Monadic.Basic import Init.Data.List.Lemmas import Init.Data.List.ToArray
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
v___x_7_ = lean_apply_3(v_h__1_2_, v_it_5_, v_out_6_, lean_box(0));
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
v___x_9_ = lean_apply_2(v_h__2_3_, v_it_8_, lean_box(0));
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_apply_1(v_h__3_4_, lean_box(0));
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(lean_object* v_m_11_, lean_object* v_00_u03b2_12_, lean_object* v_00_u03b1_u2081_13_, lean_object* v_inst_14_, lean_object* v_it_u2081_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_, v_h__3_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___boxed(lean_object* v_m_22_, lean_object* v_00_u03b2_23_, lean_object* v_00_u03b1_u2081_24_, lean_object* v_inst_25_, lean_object* v_it_u2081_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(v_m_22_, v_00_u03b2_23_, v_00_u03b1_u2081_24_, v_inst_25_, v_it_u2081_26_, v_motive_27_, v_x_28_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
lean_dec(v_it_u2081_26_);
lean_dec(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___redArg(lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
switch(lean_obj_tag(v_x_33_))
{
case 0:
{
lean_object* v_it_37_; lean_object* v_out_38_; lean_object* v___x_39_; 
lean_dec(v_h__3_36_);
lean_dec(v_h__2_35_);
v_it_37_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_it_37_);
v_out_38_ = lean_ctor_get(v_x_33_, 1);
lean_inc(v_out_38_);
lean_dec_ref(v_x_33_);
v___x_39_ = lean_apply_3(v_h__1_34_, v_it_37_, v_out_38_, lean_box(0));
return v___x_39_;
}
case 1:
{
lean_object* v_it_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_36_);
lean_dec(v_h__1_34_);
v_it_40_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_it_40_);
lean_dec_ref(v_x_33_);
v___x_41_ = lean_apply_2(v_h__2_35_, v_it_40_, lean_box(0));
return v___x_41_;
}
default: 
{
lean_object* v___x_42_; 
lean_dec(v_h__2_35_);
lean_dec(v_h__1_34_);
v___x_42_ = lean_apply_1(v_h__3_36_, lean_box(0));
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(lean_object* v_00_u03b1_u2081_43_, lean_object* v_00_u03b2_44_, lean_object* v_m_45_, lean_object* v_inst_46_, lean_object* v_it_u2081_47_, lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_, lean_object* v_h__3_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___redArg(v_x_49_, v_h__1_50_, v_h__2_51_, v_h__3_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___boxed(lean_object* v_00_u03b1_u2081_54_, lean_object* v_00_u03b2_55_, lean_object* v_m_56_, lean_object* v_inst_57_, lean_object* v_it_u2081_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(v_00_u03b1_u2081_54_, v_00_u03b2_55_, v_m_56_, v_inst_57_, v_it_u2081_58_, v_motive_59_, v_x_60_, v_h__1_61_, v_h__2_62_, v_h__3_63_);
lean_dec(v_it_u2081_58_);
lean_dec(v_inst_57_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_, lean_object* v_h__3_68_){
_start:
{
switch(lean_obj_tag(v_x_65_))
{
case 0:
{
lean_object* v_it_69_; lean_object* v_out_70_; lean_object* v___x_71_; 
lean_dec(v_h__3_68_);
lean_dec(v_h__2_67_);
v_it_69_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_it_69_);
v_out_70_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_out_70_);
lean_dec_ref(v_x_65_);
v___x_71_ = lean_apply_2(v_h__1_66_, v_it_69_, v_out_70_);
return v___x_71_;
}
case 1:
{
lean_object* v_it_72_; lean_object* v___x_73_; 
lean_dec(v_h__3_68_);
lean_dec(v_h__1_66_);
v_it_72_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_it_72_);
lean_dec_ref(v_x_65_);
v___x_73_ = lean_apply_1(v_h__2_67_, v_it_72_);
return v___x_73_;
}
default: 
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__2_67_);
lean_dec(v_h__1_66_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__3_68_, v___x_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_m_78_, lean_object* v_motive_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_, lean_object* v_h__3_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(v_x_80_, v_h__1_81_, v_h__2_82_, v_h__3_83_);
return v___x_84_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
}
#ifdef __cplusplus
}
#endif
