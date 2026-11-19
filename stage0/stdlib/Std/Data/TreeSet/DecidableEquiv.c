// Lean compiler output
// Module: Std.Data.TreeSet.DecidableEquiv
// Imports: public import Std.Data.TreeMap.DecidableEquiv public import Std.Data.TreeSet.Basic
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
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_instBEqOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___lam__0(lean_object* v___x_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_instBEqOfDecidableEq___redArg___lam__0(v___x_1_, v___y_3_, v___y_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___lam__0___boxed(lean_object* v___x_6_, lean_object* v_k_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___lam__0(v___x_6_, v_k_7_, v___y_8_, v___y_9_);
lean_dec(v_k_7_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
static lean_object* _init_l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___f_13_; 
v___x_12_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_13_ = lean_alloc_closure((void*)(l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_13_, 0, v___x_12_);
return v___f_13_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(lean_object* v_cmp_14_, lean_object* v_t_u2081_15_, lean_object* v_t_u2082_16_){
_start:
{
lean_object* v___f_17_; uint8_t v___x_18_; 
v___f_17_ = lean_obj_once(&l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0, &l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0_once, _init_l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0);
v___x_18_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_14_, v___f_17_, v_t_u2081_15_, v_t_u2082_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___boxed(lean_object* v_cmp_19_, lean_object* v_t_u2081_20_, lean_object* v_t_u2082_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(v_cmp_19_, v_t_u2081_20_, v_t_u2082_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(lean_object* v_00_u03b1_24_, lean_object* v_cmp_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_t_u2081_28_, lean_object* v_t_u2082_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(v_cmp_25_, v_t_u2081_28_, v_t_u2082_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___boxed(lean_object* v_00_u03b1_31_, lean_object* v_cmp_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_t_u2081_35_, lean_object* v_t_u2082_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(v_00_u03b1_31_, v_cmp_32_, v_inst_33_, v_inst_34_, v_t_u2081_35_, v_t_u2082_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_DecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeSet_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_DecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeSet_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeSet_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
