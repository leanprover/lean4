// Lean compiler output
// Module: Std.WP.Triple.SpecLemmas
// Imports: public import Init.BinderNameHint public import Std.WP.Triple.Monad public import Std.WP.Monad public import Std.Do.Triple.SpecLemmas public import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic public import Init.Data.Slice.Array public import Init.Data.Iterators.Lemmas.Combinators.FilterMap public import Init.Data.Range import Init.Data.Iterators.Lemmas import Init.Data.List.Nat.Range import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.TakeDrop import Init.Data.Nat.Mod import Init.Data.Slice.Lemmas import Init.Omega public import Init.Data.String.Defs public import Init.Data.String.Iterate import Init.Data.String.Lemmas.Splits import Init.Data.String.Termination import Init.Data.String.Lemmas.Iterate public import Std.Internal.ForIn
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
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v_a_13_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_x_10_, 1);
v___x_14_ = lean_apply_1(v_h__1_11_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_a_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__2_12_, v_a_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk___redArg(lean_object* v_inv_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_apply_1(v_inv_17_, v_a_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_RepeatInvariant_mk(lean_object* v_00_u03b1_20_, lean_object* v_00_u03b2_21_, lean_object* v_Pred_22_, lean_object* v_inv_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_apply_1(v_inv_23_, v_a_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg(lean_object* v_inv_26_, uint8_t v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_box(v_a_27_);
v___x_30_ = lean_apply_2(v_inv_26_, v___x_29_, v_a_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg___boxed(lean_object* v_inv_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
uint8_t v_a_9__boxed_34_; lean_object* v_res_35_; 
v_a_9__boxed_34_ = lean_unbox(v_a_32_);
v_res_35_ = l_Std_WP_WhileInvariant_mk___redArg(v_inv_31_, v_a_9__boxed_34_, v_a_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk(lean_object* v_00_u03b1_36_, lean_object* v_Pred_37_, lean_object* v_inv_38_, uint8_t v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(v_a_39_);
v___x_42_ = lean_apply_2(v_inv_38_, v___x_41_, v_a_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___boxed(lean_object* v_00_u03b1_43_, lean_object* v_Pred_44_, lean_object* v_inv_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
uint8_t v_a_19__boxed_48_; lean_object* v_res_49_; 
v_a_19__boxed_48_ = lean_unbox(v_a_46_);
v_res_49_ = l_Std_WP_WhileInvariant_mk(v_00_u03b1_43_, v_Pred_44_, v_inv_45_, v_a_19__boxed_48_, v_a_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(lean_object* v_inv_50_, lean_object* v_a_51_){
_start:
{
if (lean_obj_tag(v_a_51_) == 0)
{
lean_object* v_val_52_; uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_val_52_ = lean_ctor_get(v_a_51_, 0);
lean_inc(v_val_52_);
lean_dec_ref_known(v_a_51_, 1);
v___x_53_ = 0;
v___x_54_ = lean_box(v___x_53_);
v___x_55_ = lean_apply_2(v_inv_50_, v___x_54_, v_val_52_);
return v___x_55_;
}
else
{
lean_object* v_val_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_val_56_ = lean_ctor_get(v_a_51_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v_a_51_, 1);
v___x_57_ = 1;
v___x_58_ = lean_box(v___x_57_);
v___x_59_ = lean_apply_2(v_inv_50_, v___x_58_, v_val_56_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant(lean_object* v_00_u03b1_60_, lean_object* v_Pred_61_, lean_object* v_inv_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(v_inv_62_, v_a_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg___lam__0(lean_object* v_f_65_, lean_object* v_inst_66_, lean_object* v_a_67_, lean_object* v_n_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_apply_1(v_f_65_, v_a_67_);
v___x_70_ = lean_apply_2(v_inst_66_, v___x_69_, v_n_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg(lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_f_73_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_75_; 
v___f_74_ = lean_alloc_closure((void*)(l_Std_WP_Variant_ofMeasure___redArg___lam__0), 4, 2);
lean_closure_set(v___f_74_, 0, v_f_73_);
lean_closure_set(v___f_74_, 1, v_inst_71_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_inst_72_);
lean_ctor_set(v___x_75_, 1, v___f_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure(lean_object* v_Pred_76_, lean_object* v_inst_77_, lean_object* v_00_u03b1_78_, lean_object* v_00_u03b3_79_, lean_object* v_Fun_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_f_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_WP_Variant_ofMeasure___redArg(v_inst_81_, v_inst_82_, v_f_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object* v_____do__lift_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_____do__lift_85_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_87_);
v_a_88_ = lean_ctor_get(v_____do__lift_85_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v_____do__lift_85_, 1);
v___x_89_ = lean_apply_1(v_h__1_86_, v_a_88_);
return v___x_89_;
}
else
{
lean_object* v_a_90_; lean_object* v___x_91_; 
lean_dec(v_h__1_86_);
v_a_90_ = lean_ctor_get(v_____do__lift_85_, 0);
lean_inc(v_a_90_);
lean_dec_ref_known(v_____do__lift_85_, 1);
v___x_91_ = lean_apply_1(v_h__2_87_, v_a_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object* v_00_u03b2_92_, lean_object* v_motive_93_, lean_object* v_____do__lift_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
if (lean_obj_tag(v_____do__lift_94_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; 
lean_dec(v_h__2_96_);
v_a_97_ = lean_ctor_get(v_____do__lift_94_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v_____do__lift_94_, 1);
v___x_98_ = lean_apply_1(v_h__1_95_, v_a_97_);
return v___x_98_;
}
else
{
lean_object* v_a_99_; lean_object* v___x_100_; 
lean_dec(v_h__1_95_);
v_a_99_ = lean_ctor_get(v_____do__lift_94_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v_____do__lift_94_, 1);
v___x_100_ = lean_apply_1(v_h__2_96_, v_a_99_);
return v___x_100_;
}
}
}
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Triple_Monad(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Monad(uint8_t builtin);
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
LEAN_EXPORT lean_object* runtime_initialize_Std_WP_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Triple_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Monad(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_WP_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* initialize_Std_WP_Triple_Monad(uint8_t builtin);
lean_object* initialize_Std_WP_Monad(uint8_t builtin);
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
LEAN_EXPORT lean_object* initialize_Std_WP_Triple_SpecLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Triple_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Monad(builtin);
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
res = runtime_initialize_Std_WP_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_WP_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_WP_Triple_SpecLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
