// Lean compiler output
// Module: Init.Data.String.Iter.Basic
// Imports: public import Init.Data.Iterators.Combinators.FilterMap public import Init.Data.Iterators.Consumers.Collect
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toStringList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Iter_toStringList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Iter_toStringList___redArg___closed__0 = (const lean_object*)&l_Std_Iter_toStringList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iter_toStringList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toStringList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toStringList___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_it_3_, lean_object* v_acc_4_, lean_object* v_recur_5_){
_start:
{
lean_object* v_val_6_; 
v_val_6_ = lean_apply_1(v_inst_1_, v_it_3_);
switch(lean_obj_tag(v_val_6_))
{
case 0:
{
lean_object* v_it_7_; lean_object* v_out_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_it_7_ = lean_ctor_get(v_val_6_, 0);
lean_inc(v_it_7_);
v_out_8_ = lean_ctor_get(v_val_6_, 1);
lean_inc(v_out_8_);
lean_dec_ref(v_val_6_);
v___x_9_ = lean_apply_1(v_inst_2_, v_out_8_);
v___x_10_ = lean_array_push(v_acc_4_, v___x_9_);
v___x_11_ = lean_apply_3(v_recur_5_, v_it_7_, v___x_10_, lean_box(0));
return v___x_11_;
}
case 1:
{
lean_object* v_it_12_; lean_object* v___x_13_; 
lean_dec_ref(v_inst_2_);
v_it_12_ = lean_ctor_get(v_val_6_, 0);
lean_inc(v_it_12_);
lean_dec_ref(v_val_6_);
v___x_13_ = lean_apply_3(v_recur_5_, v_it_12_, v_acc_4_, lean_box(0));
return v___x_13_;
}
default: 
{
lean_dec_ref(v_recur_5_);
lean_dec_ref(v_inst_2_);
return v_acc_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toStringList___redArg(lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_it_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___f_19_ = lean_alloc_closure((void*)(l_Std_Iter_toStringList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_19_, 0, v_inst_16_);
lean_closure_set(v___f_19_, 1, v_inst_17_);
v___x_20_ = ((lean_object*)(l_Std_Iter_toStringList___redArg___closed__0));
v___x_21_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_19_, v_it_18_, v___x_20_);
v___x_22_ = lean_array_to_list(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toStringList(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_it_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_28_ = lean_alloc_closure((void*)(l_Std_Iter_toStringList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_28_, 0, v_inst_25_);
lean_closure_set(v___f_28_, 1, v_inst_26_);
v___x_29_ = ((lean_object*)(l_Std_Iter_toStringList___redArg___closed__0));
v___x_30_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_28_, v_it_27_, v___x_29_);
v___x_31_ = lean_array_to_list(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray___redArg(lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_it_34_){
_start:
{
lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___f_35_ = lean_alloc_closure((void*)(l_Std_Iter_toStringList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_35_, 0, v_inst_32_);
lean_closure_set(v___f_35_, 1, v_inst_33_);
v___x_36_ = ((lean_object*)(l_Std_Iter_toStringList___redArg___closed__0));
v___x_37_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_35_, v_it_34_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_it_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___f_43_ = lean_alloc_closure((void*)(l_Std_Iter_toStringList___redArg___lam__0), 5, 2);
lean_closure_set(v___f_43_, 0, v_inst_40_);
lean_closure_set(v___f_43_, 1, v_inst_41_);
v___x_44_ = ((lean_object*)(l_Std_Iter_toStringList___redArg___closed__0));
v___x_45_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_43_, v_it_42_, v___x_44_);
return v___x_45_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Iter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Iter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Iter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Iter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Iter_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
