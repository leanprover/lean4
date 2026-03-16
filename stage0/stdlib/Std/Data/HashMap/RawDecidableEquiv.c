// Lean compiler output
// Module: Std.Data.HashMap.RawDecidableEquiv
// Imports: public import Std.Data.DHashMap.RawDecidableEquiv public import Std.Data.HashMap.Raw
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
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_apply_2(v_inst_1_, v___y_3_, v___y_4_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_k_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0(v_inst_7_, v_k_8_, v___y_9_, v___y_10_);
lean_dec(v_k_8_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableEquiv___redArg(lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_m_u2081_16_, lean_object* v_m_u2082_17_){
_start:
{
lean_object* v___f_18_; uint8_t v_this_19_; 
v___f_18_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instDecidableEquiv___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_18_, 0, v_inst_15_);
v_this_19_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_13_, v_inst_14_, v___f_18_, v_m_u2081_16_, v_m_u2082_17_);
return v_this_19_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_m_u2081_23_, lean_object* v_m_u2082_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg(v_inst_20_, v_inst_21_, v_inst_22_, v_m_u2081_23_, v_m_u2082_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableEquiv(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_m_u2081_34_, lean_object* v_m_u2082_35_, lean_object* v_h_u2081_36_, lean_object* v_h_u2082_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg(v_inst_29_, v_inst_31_, v_inst_32_, v_m_u2081_34_, v_m_u2082_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_m_u2081_46_, lean_object* v_m_u2082_47_, lean_object* v_h_u2081_48_, lean_object* v_h_u2082_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Std_HashMap_Raw_instDecidableEquiv(v_00_u03b1_39_, v_00_u03b2_40_, v_inst_41_, v_inst_42_, v_inst_43_, v_inst_44_, v_inst_45_, v_m_u2081_46_, v_m_u2082_47_, v_h_u2081_48_, v_h_u2082_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashMap_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_RawDecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
