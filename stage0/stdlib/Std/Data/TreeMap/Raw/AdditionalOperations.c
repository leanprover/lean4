// Lean compiler output
// Module: Std.Data.TreeMap.Raw.AdditionalOperations
// Imports: public import Std.Data.TreeMap.Basic public import Std.Data.TreeMap.Raw.Basic public import Std.Data.DTreeMap.Raw.AdditionalOperations
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
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___redArg(lean_object* v_f_1_, lean_object* v_t_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_1_, v_t_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_00_u03b3_6_, lean_object* v_cmp_7_, lean_object* v_f_8_, lean_object* v_t_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_DTreeMap_Internal_Impl_filterMap_x21___redArg(v_f_8_, v_t_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___boxed(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_00_u03b3_13_, lean_object* v_cmp_14_, lean_object* v_f_15_, lean_object* v_t_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_TreeMap_Raw_filterMap(v_00_u03b1_11_, v_00_u03b2_12_, v_00_u03b3_13_, v_cmp_14_, v_f_15_, v_t_16_);
lean_dec_ref(v_cmp_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___redArg(lean_object* v_f_18_, lean_object* v_t_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_18_, v_t_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_00_u03b3_23_, lean_object* v_cmp_24_, lean_object* v_f_25_, lean_object* v_t_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_25_, v_t_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___boxed(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_00_u03b3_30_, lean_object* v_cmp_31_, lean_object* v_f_32_, lean_object* v_t_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_TreeMap_Raw_map(v_00_u03b1_28_, v_00_u03b2_29_, v_00_u03b3_30_, v_cmp_31_, v_f_32_, v_t_33_);
lean_dec_ref(v_cmp_31_);
return v_res_34_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeMap_Raw_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeMap_Raw_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeMap_Raw_AdditionalOperations(builtin);
}
#ifdef __cplusplus
}
#endif
