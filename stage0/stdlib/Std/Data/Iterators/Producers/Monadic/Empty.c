// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Empty
// Imports: public import Init.Data.Iterators.Consumers.Loop
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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_empty(lean_object* v_m_1_, lean_object* v_00_u03b2_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIterator___redArg___lam__0(lean_object* v_toPure_4_, lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_box(2);
v___x_7_ = lean_apply_2(v_toPure_4_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIterator___redArg(lean_object* v_inst_8_){
_start:
{
lean_object* v_toApplicative_9_; lean_object* v_toPure_10_; lean_object* v___f_11_; 
v_toApplicative_9_ = lean_ctor_get(v_inst_8_, 0);
lean_inc_ref(v_toApplicative_9_);
lean_dec_ref(v_inst_8_);
v_toPure_10_ = lean_ctor_get(v_toApplicative_9_, 1);
lean_inc(v_toPure_10_);
lean_dec_ref(v_toApplicative_9_);
v___f_11_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Empty_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v_toPure_10_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIterator(lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_Iterators_Types_Empty_instIterator___redArg(v_inst_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation(lean_object* v_m_16_, lean_object* v_00_u03b2_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation___boxed(lean_object* v_m_20_, lean_object* v_00_u03b2_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation(v_m_20_, v_00_u03b2_21_, v_inst_22_);
lean_dec_ref(v_inst_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_24_, lean_object* v_recur_25_, lean_object* v_it_26_, lean_object* v_____do__lift_27_){
_start:
{
if (lean_obj_tag(v_____do__lift_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_29_; 
lean_dec(v_recur_25_);
v_a_28_ = lean_ctor_get(v_____do__lift_27_, 0);
lean_inc(v_a_28_);
lean_dec_ref(v_____do__lift_27_);
v___x_29_ = lean_apply_2(v_toPure_24_, lean_box(0), v_a_28_);
return v___x_29_;
}
else
{
lean_object* v_a_30_; lean_object* v___x_31_; 
lean_dec(v_toPure_24_);
v_a_30_ = lean_ctor_get(v_____do__lift_27_, 0);
lean_inc(v_a_30_);
lean_dec_ref(v_____do__lift_27_);
v___x_31_ = lean_apply_4(v_recur_25_, v_it_26_, v_a_30_, lean_box(0), lean_box(0));
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_32_, lean_object* v_recur_33_, lean_object* v___y_34_, lean_object* v_acc_35_, lean_object* v_toBind_36_, lean_object* v_s_37_){
_start:
{
switch(lean_obj_tag(v_s_37_))
{
case 0:
{
lean_object* v_it_38_; lean_object* v_out_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_it_38_ = lean_ctor_get(v_s_37_, 0);
lean_inc(v_it_38_);
v_out_39_ = lean_ctor_get(v_s_37_, 1);
lean_inc(v_out_39_);
lean_dec_ref(v_s_37_);
v___f_40_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_40_, 0, v_toPure_32_);
lean_closure_set(v___f_40_, 1, v_recur_33_);
lean_closure_set(v___f_40_, 2, v_it_38_);
v___x_41_ = lean_apply_3(v___y_34_, v_out_39_, lean_box(0), v_acc_35_);
v___x_42_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v___x_41_, v___f_40_);
return v___x_42_;
}
case 1:
{
lean_object* v_it_43_; lean_object* v___x_44_; 
lean_dec(v_toBind_36_);
lean_dec(v___y_34_);
lean_dec(v_toPure_32_);
v_it_43_ = lean_ctor_get(v_s_37_, 0);
lean_inc(v_it_43_);
lean_dec_ref(v_s_37_);
v___x_44_ = lean_apply_4(v_recur_33_, v_it_43_, v_acc_35_, lean_box(0), lean_box(0));
return v___x_44_;
}
default: 
{
lean_object* v___x_45_; 
lean_dec(v_toBind_36_);
lean_dec(v___y_34_);
lean_dec(v_recur_33_);
v___x_45_ = lean_apply_2(v_toPure_32_, lean_box(0), v_acc_35_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__2(lean_object* v_inst_46_, lean_object* v_toPure_47_, lean_object* v___y_48_, lean_object* v_toBind_49_, lean_object* v_lift_50_, lean_object* v_it_51_, lean_object* v_acc_52_, lean_object* v_hP_53_, lean_object* v_recur_54_){
_start:
{
lean_object* v_toApplicative_55_; lean_object* v_toPure_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_toApplicative_55_ = lean_ctor_get(v_inst_46_, 0);
lean_inc_ref(v_toApplicative_55_);
lean_dec_ref(v_inst_46_);
v_toPure_56_ = lean_ctor_get(v_toApplicative_55_, 1);
lean_inc(v_toPure_56_);
lean_dec_ref(v_toApplicative_55_);
v___f_57_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_57_, 0, v_toPure_47_);
lean_closure_set(v___f_57_, 1, v_recur_54_);
lean_closure_set(v___f_57_, 2, v___y_48_);
lean_closure_set(v___f_57_, 3, v_acc_52_);
lean_closure_set(v___f_57_, 4, v_toBind_49_);
v___x_58_ = lean_box(2);
v___x_59_ = lean_apply_2(v_toPure_56_, lean_box(0), v___x_58_);
v___x_60_ = lean_apply_4(v_lift_50_, lean_box(0), lean_box(0), v___f_57_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__3(lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_lift_63_, lean_object* v_00_u03b3_64_, lean_object* v_Pl_65_, lean_object* v_it_66_, lean_object* v_init_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_toApplicative_69_; lean_object* v_toBind_70_; lean_object* v_toPure_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
v_toApplicative_69_ = lean_ctor_get(v_inst_61_, 0);
lean_inc_ref(v_toApplicative_69_);
v_toBind_70_ = lean_ctor_get(v_inst_61_, 1);
lean_inc(v_toBind_70_);
lean_dec_ref(v_inst_61_);
v_toPure_71_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_toPure_71_);
lean_dec_ref(v_toApplicative_69_);
v___f_72_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_72_, 0, v_inst_62_);
lean_closure_set(v___f_72_, 1, v_toPure_71_);
lean_closure_set(v___f_72_, 2, v___y_68_);
lean_closure_set(v___f_72_, 3, v_toBind_70_);
lean_closure_set(v___f_72_, 4, v_lift_63_);
v___x_73_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_72_, v_it_66_, v_init_67_, lean_box(0));
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop___redArg(lean_object* v_inst_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v___f_76_; 
v___f_76_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_76_, 0, v_inst_75_);
lean_closure_set(v___f_76_, 1, v_inst_74_);
return v___f_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Empty_instIteratorLoop(lean_object* v_m_77_, lean_object* v_00_u03b2_78_, lean_object* v_n_79_, lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_82_, 0, v_inst_81_);
lean_closure_set(v___f_82_, 1, v_inst_80_);
return v___f_82_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Monadic_Empty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Monadic_Empty(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Empty(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
}
#ifdef __cplusplus
}
#endif
