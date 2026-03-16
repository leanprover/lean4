// Lean compiler output
// Module: Std.Data.DHashMap.RawDecidableEquiv
// Imports: public import Std.Data.DHashMap.Internal.RawLemmas
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableEquiv___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_m_u2081_4_, lean_object* v_m_u2082_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1_, v_inst_2_, v_inst_3_, v_m_u2081_4_, v_m_u2082_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_m_u2081_10_, lean_object* v_m_u2082_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_DHashMap_Raw_instDecidableEquiv___redArg(v_inst_7_, v_inst_8_, v_inst_9_, v_m_u2081_10_, v_m_u2082_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableEquiv(lean_object* v_00_u03b1_14_, lean_object* v_00_u03b2_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_m_u2081_21_, lean_object* v_m_u2082_22_, lean_object* v_h_u2081_23_, lean_object* v_h_u2082_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_16_, v_inst_18_, v_inst_19_, v_m_u2081_21_, v_m_u2082_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_m_u2081_33_, lean_object* v_m_u2082_34_, lean_object* v_h_u2081_35_, lean_object* v_h_u2082_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_DHashMap_Raw_instDecidableEquiv(v_00_u03b1_26_, v_00_u03b2_27_, v_inst_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_m_u2081_33_, v_m_u2082_34_, v_h_u2081_35_, v_h_u2082_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
