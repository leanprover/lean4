// Lean compiler output
// Module: Std.Data.TreeSet.Raw.DecidableEquiv
// Imports: public import Std.Data.TreeMap.Raw.DecidableEquiv public import Std.Data.TreeSet.Raw.Basic
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_TreeMap_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___f_2_; 
v___x_1_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_2_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2_, 0, v___x_1_);
return v___f_2_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg(lean_object* v_cmp_3_, lean_object* v_t_u2081_4_, lean_object* v_t_u2082_5_){
_start:
{
lean_object* v___f_6_; uint8_t v_this_7_; 
v___f_6_ = lean_obj_once(&l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0, &l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0_once, _init_l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0);
v_this_7_ = l_Std_TreeMap_Raw_instDecidableEquiv___redArg(v_cmp_3_, v___f_6_, v_t_u2081_4_, v_t_u2082_5_);
return v_this_7_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_cmp_8_, lean_object* v_t_u2081_9_, lean_object* v_t_u2082_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_TreeSet_Raw_instDecidableEquiv___redArg(v_cmp_8_, v_t_u2081_9_, v_t_u2082_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableEquiv(lean_object* v_00_u03b1_13_, lean_object* v_cmp_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_t_u2081_17_, lean_object* v_t_u2082_18_, lean_object* v_h_u2081_19_, lean_object* v_h_u2082_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = l_Std_TreeSet_Raw_instDecidableEquiv___redArg(v_cmp_14_, v_t_u2081_17_, v_t_u2082_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_22_, lean_object* v_cmp_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_t_u2081_26_, lean_object* v_t_u2082_27_, lean_object* v_h_u2081_28_, lean_object* v_h_u2082_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Std_TreeSet_Raw_instDecidableEquiv(v_00_u03b1_22_, v_cmp_23_, v_inst_24_, v_inst_25_, v_t_u2081_26_, v_t_u2082_27_, v_h_u2081_28_, v_h_u2082_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Raw_DecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
