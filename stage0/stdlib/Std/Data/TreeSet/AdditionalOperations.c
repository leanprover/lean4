// Lean compiler output
// Module: Std.Data.TreeSet.AdditionalOperations
// Imports: public import Std.Data.TreeSet.Raw.Basic public import Std.Data.TreeMap.AdditionalOperations
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
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE___redArg(lean_object* v_cmp_1_, lean_object* v_t_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_1_, v_k_3_, v_t_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGE(lean_object* v_00_u03b1_5_, lean_object* v_cmp_6_, lean_object* v_inst_7_, lean_object* v_t_8_, lean_object* v_k_9_, lean_object* v_h_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_6_, v_k_9_, v_t_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT___redArg(lean_object* v_cmp_12_, lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_12_, v_k_14_, v_t_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getGT(lean_object* v_00_u03b1_16_, lean_object* v_cmp_17_, lean_object* v_inst_18_, lean_object* v_t_19_, lean_object* v_k_20_, lean_object* v_h_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_17_, v_k_20_, v_t_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE___redArg(lean_object* v_cmp_23_, lean_object* v_t_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_23_, v_k_25_, v_t_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLE(lean_object* v_00_u03b1_27_, lean_object* v_cmp_28_, lean_object* v_inst_29_, lean_object* v_t_30_, lean_object* v_k_31_, lean_object* v_h_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_28_, v_k_31_, v_t_30_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT___redArg(lean_object* v_cmp_34_, lean_object* v_t_35_, lean_object* v_k_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_34_, v_k_36_, v_t_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_getLT(lean_object* v_00_u03b1_38_, lean_object* v_cmp_39_, lean_object* v_inst_40_, lean_object* v_t_41_, lean_object* v_k_42_, lean_object* v_h_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_39_, v_k_42_, v_t_41_);
return v___x_44_;
}
}
lean_object* runtime_initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_AdditionalOperations(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeSet_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_AdditionalOperations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
}
#ifdef __cplusplus
}
#endif
