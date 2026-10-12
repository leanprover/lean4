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
lean_object* l_Std_WP_WhileInvariant_mk___redArg(lean_object* v_inv_26_, uint8_t v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_box(v_a_27_);
v___x_30_ = lean_apply_2(v_inv_26_, v___x_29_, v_a_28_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Std_WP_WhileInvariant_mk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inv_26_ = stack[0].m_obj;
uint8_t v_a_27_ = stack[1].m_num;
lean_object* v_a_28_ = stack[2].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_WP_WhileInvariant_mk___redArg(v_inv_26_, v_a_27_, v_a_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___redArg___boxed(lean_object* v_inv_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
uint8_t v_a_9__boxed_35_; lean_object* v_res_36_; 
v_a_9__boxed_35_ = lean_unbox(v_a_33_);
v_res_36_ = l_Std_WP_WhileInvariant_mk___redArg(v_inv_32_, v_a_9__boxed_35_, v_a_34_);
return v_res_36_;
}
}
lean_object* l_Std_WP_WhileInvariant_mk(lean_object* v_00_u03b1_37_, lean_object* v_Pred_38_, lean_object* v_inv_39_, uint8_t v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_box(v_a_40_);
v___x_43_ = lean_apply_2(v_inv_39_, v___x_42_, v_a_41_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Std_WP_WhileInvariant_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_inv_39_ = stack[2].m_obj;
uint8_t v_a_40_ = stack[3].m_num;
lean_object* v_a_41_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Std_WP_WhileInvariant_mk(lean_box(0), lean_box(0), v_inv_39_, v_a_40_, v_a_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_mk___boxed(lean_object* v_00_u03b1_45_, lean_object* v_Pred_46_, lean_object* v_inv_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
uint8_t v_a_25__boxed_50_; lean_object* v_res_51_; 
v_a_25__boxed_50_ = lean_unbox(v_a_48_);
v_res_51_ = l_Std_WP_WhileInvariant_mk(v_00_u03b1_45_, v_Pred_46_, v_inv_47_, v_a_25__boxed_50_, v_a_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(lean_object* v_inv_52_, lean_object* v_a_53_){
_start:
{
if (lean_obj_tag(v_a_53_) == 0)
{
lean_object* v_val_54_; uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_val_54_ = lean_ctor_get(v_a_53_, 0);
lean_inc(v_val_54_);
lean_dec_ref_known(v_a_53_, 1);
v___x_55_ = 0;
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_apply_2(v_inv_52_, v___x_56_, v_val_54_);
return v___x_57_;
}
else
{
lean_object* v_val_58_; uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_val_58_ = lean_ctor_get(v_a_53_, 0);
lean_inc(v_val_58_);
lean_dec_ref_known(v_a_53_, 1);
v___x_59_ = 1;
v___x_60_ = lean_box(v___x_59_);
v___x_61_ = lean_apply_2(v_inv_52_, v___x_60_, v_val_58_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_WhileInvariant_toRepeatInvariant(lean_object* v_00_u03b1_62_, lean_object* v_Pred_63_, lean_object* v_inv_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Std_WP_WhileInvariant_toRepeatInvariant___redArg(v_inv_64_, v_a_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg___lam__0(lean_object* v_f_67_, lean_object* v_inst_68_, lean_object* v_a_69_, lean_object* v_n_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_apply_1(v_f_67_, v_a_69_);
v___x_72_ = lean_apply_2(v_inst_68_, v___x_71_, v_n_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure___redArg(lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_f_75_){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; 
v___f_76_ = lean_alloc_closure((void*)(l_Std_WP_Variant_ofMeasure___redArg___lam__0), 4, 2);
lean_closure_set(v___f_76_, 0, v_f_75_);
lean_closure_set(v___f_76_, 1, v_inst_73_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v_inst_74_);
lean_ctor_set(v___x_77_, 1, v___f_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_Variant_ofMeasure(lean_object* v_Pred_78_, lean_object* v_inst_79_, lean_object* v_00_u03b1_80_, lean_object* v_00_u03b3_81_, lean_object* v_Fun_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_f_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Std_WP_Variant_ofMeasure___redArg(v_inst_83_, v_inst_84_, v_f_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(lean_object* v_____do__lift_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_){
_start:
{
if (lean_obj_tag(v_____do__lift_87_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_89_);
v_a_90_ = lean_ctor_get(v_____do__lift_87_, 0);
lean_inc(v_a_90_);
lean_dec_ref_known(v_____do__lift_87_, 1);
v___x_91_ = lean_apply_1(v_h__1_88_, v_a_90_);
return v___x_91_;
}
else
{
lean_object* v_a_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_88_);
v_a_92_ = lean_ctor_get(v_____do__lift_87_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v_____do__lift_87_, 1);
v___x_93_ = lean_apply_1(v_h__2_89_, v_a_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(lean_object* v_00_u03b2_94_, lean_object* v_motive_95_, lean_object* v_____do__lift_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
if (lean_obj_tag(v_____do__lift_96_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; 
lean_dec(v_h__2_98_);
v_a_99_ = lean_ctor_get(v_____do__lift_96_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v_____do__lift_96_, 1);
v___x_100_ = lean_apply_1(v_h__1_97_, v_a_99_);
return v___x_100_;
}
else
{
lean_object* v_a_101_; lean_object* v___x_102_; 
lean_dec(v_h__1_97_);
v_a_101_ = lean_ctor_get(v_____do__lift_96_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v_____do__lift_96_, 1);
v___x_102_ = lean_apply_1(v_h__2_98_, v_a_101_);
return v___x_102_;
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
