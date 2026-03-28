// Lean compiler output
// Module: Std.Data.TreeMap.DecidableEquiv
// Imports: public import Std.Data.DTreeMap.DecidableEquiv public import Std.Data.TreeMap.Basic
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
LEAN_EXPORT uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_apply_2(v_inst_1_, v___y_3_, v___y_4_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_k_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(v_inst_7_, v_k_8_, v___y_9_, v___y_10_);
lean_dec(v_k_8_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_13_, lean_object* v_inst_14_, lean_object* v_t_u2081_15_, lean_object* v_t_u2082_16_){
_start:
{
lean_object* v___f_17_; uint8_t v_this_18_; 
v___f_17_ = lean_alloc_closure((void*)(l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_17_, 0, v_inst_14_);
v_this_18_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_13_, v___f_17_, v_t_u2081_15_, v_t_u2082_16_);
return v_this_18_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_19_, lean_object* v_inst_20_, lean_object* v_t_u2081_21_, lean_object* v_t_u2082_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_19_, v_inst_20_, v_t_u2081_21_, v_t_u2082_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_cmp_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_t_u2081_32_, lean_object* v_t_u2082_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_27_, v_inst_30_, v_t_u2081_32_, v_t_u2082_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_cmp_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_t_u2081_42_, lean_object* v_t_u2082_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_35_, v_00_u03b2_36_, v_cmp_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_inst_41_, v_t_u2081_42_, v_t_u2082_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
