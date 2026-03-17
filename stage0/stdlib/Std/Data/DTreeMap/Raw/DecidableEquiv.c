// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.DecidableEquiv
// Imports: public import Std.Data.DTreeMap.Internal.Lemmas public import Std.Data.DTreeMap.Raw.Basic
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
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(lean_object* v_cmp_1_, lean_object* v_inst_2_, lean_object* v_t_u2081_3_, lean_object* v_t_u2082_4_){
_start:
{
uint8_t v_this_5_; 
v_this_5_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_1_, v_inst_2_, v_t_u2081_3_, v_t_u2082_4_);
return v_this_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_cmp_6_, lean_object* v_inst_7_, lean_object* v_t_u2081_8_, lean_object* v_t_u2082_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(v_cmp_6_, v_inst_7_, v_t_u2081_8_, v_t_u2082_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_cmp_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_t_u2081_19_, lean_object* v_t_u2082_20_, lean_object* v_h_u2081_21_, lean_object* v_h_u2082_22_){
_start:
{
uint8_t v_this_23_; 
v_this_23_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_14_, v_inst_17_, v_t_u2081_19_, v_t_u2082_20_);
return v_this_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_cmp_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_t_u2081_31_, lean_object* v_t_u2082_32_, lean_object* v_h_u2081_33_, lean_object* v_h_u2082_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_DTreeMap_Raw_instDecidableEquiv(v_00_u03b1_24_, v_00_u03b2_25_, v_cmp_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_inst_30_, v_t_u2081_31_, v_t_u2082_32_, v_h_u2081_33_, v_h_u2082_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
