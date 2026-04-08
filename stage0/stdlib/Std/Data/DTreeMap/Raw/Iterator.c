// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.Iterator
// Imports: public import Std.Data.DTreeMap.Internal.Zipper public import Std.Data.DTreeMap.Raw.Basic import Init.Data.Iterators.Lemmas.Combinators.FilterMap
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
lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter___redArg(lean_object* v_m_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter___redArg___boxed(lean_object* v_m_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_DTreeMap_Raw_iter___redArg(v_m_3_);
lean_dec(v_m_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter(lean_object* v_00_u03b1_5_, lean_object* v_00_u03b2_6_, lean_object* v_cmp_7_, lean_object* v_m_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_iter___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_cmp_12_, lean_object* v_m_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Raw_iter(v_00_u03b1_10_, v_00_u03b2_11_, v_cmp_12_, v_m_13_);
lean_dec(v_m_13_);
lean_dec_ref(v_cmp_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter___redArg(lean_object* v_m_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter___redArg___boxed(lean_object* v_m_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_DTreeMap_Raw_keysIter___redArg(v_m_17_);
lean_dec(v_m_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_cmp_21_, lean_object* v_m_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysIter___boxed(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_cmp_26_, lean_object* v_m_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_DTreeMap_Raw_keysIter(v_00_u03b1_24_, v_00_u03b2_25_, v_cmp_26_, v_m_27_);
lean_dec(v_m_27_);
lean_dec_ref(v_cmp_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter___redArg(lean_object* v_m_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter___redArg___boxed(lean_object* v_m_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_DTreeMap_Raw_valuesIter___redArg(v_m_31_);
lean_dec(v_m_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_cmp_35_, lean_object* v_m_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesIter___boxed(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_cmp_40_, lean_object* v_m_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_DTreeMap_Raw_valuesIter(v_00_u03b1_38_, v_00_u03b2_39_, v_cmp_40_, v_m_41_);
lean_dec(v_m_41_);
lean_dec_ref(v_cmp_40_);
return v_res_42_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Raw_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Raw_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Raw_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
