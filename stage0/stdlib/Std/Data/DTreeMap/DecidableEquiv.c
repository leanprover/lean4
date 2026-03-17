// Lean compiler output
// Module: Std.Data.DTreeMap.DecidableEquiv
// Imports: public import Std.Data.DTreeMap.Raw
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_1_, lean_object* v_inst_2_, lean_object* v_t_u2081_3_, lean_object* v_t_u2082_4_){
_start:
{
uint8_t v_this_5_; 
v_this_5_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_1_, v_inst_2_, v_t_u2081_3_, v_t_u2082_4_);
return v_this_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_6_, lean_object* v_inst_7_, lean_object* v_t_u2081_8_, lean_object* v_t_u2082_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_6_, v_inst_7_, v_t_u2081_8_, v_t_u2082_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_cmp_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_t_u2081_19_, lean_object* v_t_u2082_20_){
_start:
{
uint8_t v_this_21_; 
v_this_21_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_14_, v_inst_17_, v_t_u2081_19_, v_t_u2082_20_);
return v_this_21_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_cmp_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_t_u2081_29_, lean_object* v_t_u2082_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Std_DTreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_22_, v_00_u03b2_23_, v_cmp_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_t_u2081_29_, v_t_u2082_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
