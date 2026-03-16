// Lean compiler output
// Module: Std.Data.DHashMap.AdditionalOperations
// Imports: public import Std.Data.DHashMap.Internal.Raw public import Std.Data.DHashMap.Internal.WF
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___redArg(lean_object* v_f_1_, lean_object* v_m_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1_, v_m_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_00_u03b4_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_f_9_, lean_object* v_m_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_9_, v_m_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___boxed(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_00_u03b4_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_f_17_, lean_object* v_m_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_DHashMap_filterMap(v_00_u03b1_12_, v_00_u03b2_13_, v_00_u03b4_14_, v_inst_15_, v_inst_16_, v_f_17_, v_m_18_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_inst_15_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_map___redArg(lean_object* v_f_20_, lean_object* v_m_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_20_, v_m_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_map(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_00_u03b4_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_f_28_, lean_object* v_m_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_28_, v_m_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_map___boxed(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_00_u03b4_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_f_36_, lean_object* v_m_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_DHashMap_map(v_00_u03b1_31_, v_00_u03b2_32_, v_00_u03b4_33_, v_inst_34_, v_inst_35_, v_f_36_, v_m_37_);
lean_dec_ref(v_inst_35_);
lean_dec_ref(v_inst_34_);
return v_res_38_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Raw(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_Internal_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Internal_Raw(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Internal_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
}
#ifdef __cplusplus
}
#endif
