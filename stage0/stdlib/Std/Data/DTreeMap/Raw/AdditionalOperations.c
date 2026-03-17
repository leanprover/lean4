// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.AdditionalOperations
// Imports: public import Std.Data.DTreeMap.AdditionalOperations
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
lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeTypeForall(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instCoeTypeForall(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filterMap___redArg(lean_object* v_f_3_, lean_object* v_t_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_3_, v_t_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filterMap(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_00_u03b3_8_, lean_object* v_cmp_9_, lean_object* v_f_10_, lean_object* v_t_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_10_, v_t_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filterMap___boxed(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_00_u03b3_15_, lean_object* v_cmp_16_, lean_object* v_f_17_, lean_object* v_t_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_DTreeMap_Raw_filterMap(v_00_u03b1_13_, v_00_u03b2_14_, v_00_u03b3_15_, v_cmp_16_, v_f_17_, v_t_18_);
lean_dec_ref(v_cmp_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_map___redArg(lean_object* v_f_20_, lean_object* v_t_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_20_, v_t_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_map(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_00_u03b3_25_, lean_object* v_cmp_26_, lean_object* v_f_27_, lean_object* v_t_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_27_, v_t_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_map___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_00_u03b3_32_, lean_object* v_cmp_33_, lean_object* v_f_34_, lean_object* v_t_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_DTreeMap_Raw_map(v_00_u03b1_30_, v_00_u03b2_31_, v_00_u03b3_32_, v_cmp_33_, v_f_34_, v_t_35_);
lean_dec_ref(v_cmp_33_);
return v_res_36_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
}
#ifdef __cplusplus
}
#endif
