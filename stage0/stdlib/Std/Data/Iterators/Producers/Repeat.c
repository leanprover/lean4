// Lean compiler output
// Module: Std.Data.Iterators.Producers.Repeat
// Imports: public import Init.Data.Iterators.Consumers.Monadic
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_repeat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_repeat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_repeat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_repeat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0(lean_object* v_f_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
lean_inc(v_it_2_);
v___x_3_ = lean_apply_1(v_f_1_, v_it_2_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v_it_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIterator___redArg(lean_object* v_f_5_){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v_f_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIterator(lean_object* v_00_u03b1_7_, lean_object* v_f_8_){
_start:
{
lean_object* v___f_9_; 
v___f_9_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_9_, 0, v_f_8_);
return v___f_9_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation(lean_object* v_00_u03b1_10_, lean_object* v_f_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_13_, lean_object* v_f_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation(v_00_u03b1_13_, v_f_14_);
lean_dec(v_f_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_16_, lean_object* v_recur_17_, lean_object* v_it_18_, lean_object* v_____do__lift_19_){
_start:
{
if (lean_obj_tag(v_____do__lift_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_it_18_);
lean_dec(v_recur_17_);
v_a_20_ = lean_ctor_get(v_____do__lift_19_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v_____do__lift_19_);
v___x_21_ = lean_apply_2(v_toPure_16_, lean_box(0), v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_toPure_16_);
v_a_22_ = lean_ctor_get(v_____do__lift_19_, 0);
lean_inc(v_a_22_);
lean_dec_ref(v_____do__lift_19_);
v___x_23_ = lean_apply_4(v_recur_17_, v_it_18_, v_a_22_, lean_box(0), lean_box(0));
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_24_, lean_object* v_recur_25_, lean_object* v___y_26_, lean_object* v_acc_27_, lean_object* v_toBind_28_, lean_object* v_s_29_){
_start:
{
switch(lean_obj_tag(v_s_29_))
{
case 0:
{
lean_object* v_it_30_; lean_object* v_out_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_it_30_ = lean_ctor_get(v_s_29_, 0);
lean_inc(v_it_30_);
v_out_31_ = lean_ctor_get(v_s_29_, 1);
lean_inc(v_out_31_);
lean_dec_ref(v_s_29_);
v___f_32_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_32_, 0, v_toPure_24_);
lean_closure_set(v___f_32_, 1, v_recur_25_);
lean_closure_set(v___f_32_, 2, v_it_30_);
v___x_33_ = lean_apply_3(v___y_26_, v_out_31_, lean_box(0), v_acc_27_);
v___x_34_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v___x_33_, v___f_32_);
return v___x_34_;
}
case 1:
{
lean_object* v_it_35_; lean_object* v___x_36_; 
lean_dec(v_toBind_28_);
lean_dec(v___y_26_);
lean_dec(v_toPure_24_);
v_it_35_ = lean_ctor_get(v_s_29_, 0);
lean_inc(v_it_35_);
lean_dec_ref(v_s_29_);
v___x_36_ = lean_apply_4(v_recur_25_, v_it_35_, v_acc_27_, lean_box(0), lean_box(0));
return v___x_36_;
}
default: 
{
lean_object* v___x_37_; 
lean_dec(v_toBind_28_);
lean_dec(v___y_26_);
lean_dec(v_recur_25_);
v___x_37_ = lean_apply_2(v_toPure_24_, lean_box(0), v_acc_27_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_38_, lean_object* v___y_39_, lean_object* v_toBind_40_, lean_object* v_f_41_, lean_object* v_lift_42_, lean_object* v_it_43_, lean_object* v_acc_44_, lean_object* v_hP_45_, lean_object* v_recur_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___f_47_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_47_, 0, v_toPure_38_);
lean_closure_set(v___f_47_, 1, v_recur_46_);
lean_closure_set(v___f_47_, 2, v___y_39_);
lean_closure_set(v___f_47_, 3, v_acc_44_);
lean_closure_set(v___f_47_, 4, v_toBind_40_);
lean_inc(v_it_43_);
v___x_48_ = lean_apply_1(v_f_41_, v_it_43_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v_it_43_);
v___x_50_ = lean_apply_4(v_lift_42_, lean_box(0), lean_box(0), v___f_47_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_51_, lean_object* v_f_52_, lean_object* v_lift_53_, lean_object* v_00_u03b3_54_, lean_object* v_Pl_55_, lean_object* v_it_56_, lean_object* v_init_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_toApplicative_59_; lean_object* v_toBind_60_; lean_object* v_toPure_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
v_toApplicative_59_ = lean_ctor_get(v_inst_51_, 0);
lean_inc_ref(v_toApplicative_59_);
v_toBind_60_ = lean_ctor_get(v_inst_51_, 1);
lean_inc(v_toBind_60_);
lean_dec_ref(v_inst_51_);
v_toPure_61_ = lean_ctor_get(v_toApplicative_59_, 1);
lean_inc(v_toPure_61_);
lean_dec_ref(v_toApplicative_59_);
v___f_62_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_62_, 0, v_toPure_61_);
lean_closure_set(v___f_62_, 1, v___y_58_);
lean_closure_set(v___f_62_, 2, v_toBind_60_);
lean_closure_set(v___f_62_, 3, v_f_52_);
lean_closure_set(v___f_62_, 4, v_lift_53_);
v___x_63_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_62_, v_it_56_, v_init_57_, lean_box(0));
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg(lean_object* v_f_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___f_66_; 
v___f_66_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_66_, 0, v_inst_65_);
lean_closure_set(v___f_66_, 1, v_f_64_);
return v___f_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_RepeatIterator_instIteratorLoop(lean_object* v_00_u03b1_67_, lean_object* v_f_68_, lean_object* v_n_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___f_71_; 
v___f_71_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_71_, 0, v_inst_70_);
lean_closure_set(v___f_71_, 1, v_f_68_);
return v___f_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_repeat___redArg(lean_object* v_init_72_){
_start:
{
lean_inc(v_init_72_);
return v_init_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_repeat___redArg___boxed(lean_object* v_init_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Iter_repeat___redArg(v_init_73_);
lean_dec(v_init_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_repeat(lean_object* v_00_u03b1_75_, lean_object* v_f_76_, lean_object* v_init_77_){
_start:
{
lean_inc(v_init_77_);
return v_init_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_repeat___boxed(lean_object* v_00_u03b1_78_, lean_object* v_f_79_, lean_object* v_init_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_Iter_repeat(v_00_u03b1_78_, v_f_79_, v_init_80_);
lean_dec(v_init_80_);
lean_dec(v_f_79_);
return v_res_81_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Repeat(builtin);
}
#ifdef __cplusplus
}
#endif
