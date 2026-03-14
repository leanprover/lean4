// Lean compiler output
// Module: Lean.Data.NameMap.AdditionalOperations
// Imports: public import Lean.Data.NameMap.Basic public import Std.Data.TreeSet.AdditionalOperations
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
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(lean_object* v_f_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; lean_object* v___x_7_; 
v_k_3_ = lean_ctor_get(v_t_2_, 1);
lean_inc(v_k_3_);
v_v_4_ = lean_ctor_get(v_t_2_, 2);
lean_inc(v_v_4_);
v_l_5_ = lean_ctor_get(v_t_2_, 3);
lean_inc(v_l_5_);
v_r_6_ = lean_ctor_get(v_t_2_, 4);
lean_inc(v_r_6_);
lean_dec_ref(v_t_2_);
lean_inc_ref(v_f_1_);
lean_inc(v_k_3_);
v___x_7_ = lean_apply_2(v_f_1_, v_k_3_, v_v_4_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_impl_8_; lean_object* v_impl_9_; lean_object* v___x_10_; 
lean_dec(v_k_3_);
lean_inc_ref(v_f_1_);
v_impl_8_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_1_, v_l_5_);
v_impl_9_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_1_, v_r_6_);
v___x_10_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_8_, v_impl_9_);
return v___x_10_;
}
else
{
lean_object* v_val_11_; lean_object* v_impl_12_; lean_object* v_impl_13_; lean_object* v___x_14_; 
v_val_11_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_val_11_);
lean_dec_ref(v___x_7_);
lean_inc_ref(v_f_1_);
v_impl_12_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_1_, v_l_5_);
v_impl_13_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_1_, v_r_6_);
v___x_14_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_3_, v_val_11_, v_impl_12_, v_impl_13_);
return v___x_14_;
}
}
else
{
lean_object* v___x_15_; 
lean_dec_ref(v_f_1_);
v___x_15_ = lean_box(1);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap___redArg(lean_object* v_f_16_, lean_object* v_m_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_16_, v_m_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_f_21_, lean_object* v_m_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_21_, v_m_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_f_26_, lean_object* v_t_27_, lean_object* v_hl_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(v_f_26_, v_t_27_);
return v___x_29_;
}
}
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_AdditionalOperations(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_NameMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_NameMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_AdditionalOperations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_NameMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_NameMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_NameMap_AdditionalOperations(builtin);
}
#ifdef __cplusplus
}
#endif
