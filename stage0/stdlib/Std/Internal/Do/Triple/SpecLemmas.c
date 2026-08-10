// Lean compiler output
// Module: Std.Internal.Do.Triple.SpecLemmas
// Imports: public import Std.Internal.Do.Triple.Basic public import Std.Do.Triple.SpecLemmas public import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic public import Init.Data.Slice.Array public import Init.Data.Iterators.Lemmas.Combinators.FilterMap public import Init.Data.Range import Init.Data.Iterators.Lemmas import Init.Data.List.Nat.Range import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.TakeDrop import Init.Data.Nat.Mod import Init.Data.Slice.Lemmas import Init.Omega public import Init.Data.String.Defs public import Init.Data.String.Iterate import Init.Data.String.Lemmas.Splits import Init.Data.String.Termination import Init.Data.String.Lemmas.Iterate public import Std.Internal.ForIn
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Except_wpInst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Except_wpInst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_RepeatVariant_ofMeasure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_RepeatVariant_ofMeasure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_RepeatVariant_ofMeasure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Except_wpInst_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__2_3_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Except_wpInst_match__1_splitter(lean_object* v_00_u03b5_8_, lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_12_);
v_a_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v_x_11_, 1);
v___x_15_ = lean_apply_1(v_h__2_13_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_13_);
v_a_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v_x_11_, 1);
v___x_17_ = lean_apply_1(v_h__1_12_, v_a_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_20_);
v_a_21_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v_x_18_, 1);
v___x_22_ = lean_apply_1(v_h__1_19_, v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_h__1_19_);
v_a_23_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref_known(v_x_18_, 1);
v___x_24_ = lean_apply_1(v_h__2_20_, v_a_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; 
lean_dec(v_h__2_29_);
v_a_30_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_a_30_);
lean_dec_ref_known(v_x_27_, 1);
v___x_31_ = lean_apply_1(v_h__1_28_, v_a_30_);
return v___x_31_;
}
else
{
lean_object* v_a_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_28_);
v_a_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_a_32_);
lean_dec_ref_known(v_x_27_, 1);
v___x_33_ = lean_apply_1(v_h__2_29_, v_a_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_RepeatVariant_ofMeasure___redArg___lam__0(lean_object* v_f_34_, lean_object* v_inst_35_, lean_object* v_a_36_, lean_object* v_n_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_apply_1(v_f_34_, v_a_36_);
v___x_39_ = lean_apply_2(v_inst_35_, v___x_38_, v_n_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_RepeatVariant_ofMeasure___redArg(lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_f_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
v___f_43_ = lean_alloc_closure((void*)(l_Std_Internal_Do_RepeatVariant_ofMeasure___redArg___lam__0), 4, 2);
lean_closure_set(v___f_43_, 0, v_f_42_);
lean_closure_set(v___f_43_, 1, v_inst_40_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v_inst_41_);
lean_ctor_set(v___x_44_, 1, v___f_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_RepeatVariant_ofMeasure(lean_object* v_Pred_45_, lean_object* v_inst_46_, lean_object* v_00_u03b1_47_, lean_object* v_00_u03b3_48_, lean_object* v_Fun_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_f_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_Internal_Do_RepeatVariant_ofMeasure___redArg(v_inst_50_, v_inst_51_, v_f_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object* v_____do__lift_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_____do__lift_54_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_56_);
v_a_57_ = lean_ctor_get(v_____do__lift_54_, 0);
lean_inc(v_a_57_);
lean_dec_ref_known(v_____do__lift_54_, 1);
v___x_58_ = lean_apply_1(v_h__1_55_, v_a_57_);
return v___x_58_;
}
else
{
lean_object* v_a_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_55_);
v_a_59_ = lean_ctor_get(v_____do__lift_54_, 0);
lean_inc(v_a_59_);
lean_dec_ref_known(v_____do__lift_54_, 1);
v___x_60_ = lean_apply_1(v_h__2_56_, v_a_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object* v_00_u03b2_61_, lean_object* v_motive_62_, lean_object* v_____do__lift_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_____do__lift_63_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_65_);
v_a_66_ = lean_ctor_get(v_____do__lift_63_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v_____do__lift_63_, 1);
v___x_67_ = lean_apply_1(v_h__1_64_, v_a_66_);
return v___x_67_;
}
else
{
lean_object* v_a_68_; lean_object* v___x_69_; 
lean_dec(v_h__1_64_);
v_a_68_ = lean_ctor_get(v_____do__lift_63_, 0);
lean_inc(v_a_68_);
lean_dec_ref_known(v_____do__lift_63_, 1);
v___x_69_ = lean_apply_1(v_h__2_65_, v_a_68_);
return v___x_69_;
}
}
}
lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_ForIn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_Triple_SpecLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin);
lean_object* initialize_Std_Internal_ForIn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
