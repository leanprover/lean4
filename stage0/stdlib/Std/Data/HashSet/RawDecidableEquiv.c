// Lean compiler output
// Module: Std.Data.HashSet.RawDecidableEquiv
// Imports: public import Std.Data.HashMap.RawDecidableEquiv public import Std.Data.HashSet.Raw
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
uint8_t l_Std_HashMap_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___f_2_; 
v___x_1_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_2_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2_, 0, v___x_1_);
return v___f_2_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv___redArg(lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_m_u2081_5_, lean_object* v_m_u2082_6_){
_start:
{
lean_object* v___f_7_; uint8_t v_this_8_; 
v___f_7_ = lean_obj_once(&l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0, &l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0_once, _init_l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0);
v_this_8_ = l_Std_HashMap_Raw_instDecidableEquiv___redArg(v_inst_3_, v_inst_4_, v___f_7_, v_m_u2081_5_, v_m_u2082_6_);
return v_this_8_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_m_u2081_11_, lean_object* v_m_u2082_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg(v_inst_9_, v_inst_10_, v_m_u2081_11_, v_m_u2082_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_m_u2081_19_, lean_object* v_m_u2082_20_, lean_object* v_h_u2081_21_, lean_object* v_h_u2082_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg(v_inst_16_, v_inst_18_, v_m_u2081_19_, v_m_u2082_20_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_m_u2081_28_, lean_object* v_m_u2082_29_, lean_object* v_h_u2081_30_, lean_object* v_h_u2082_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Std_HashSet_Raw_instDecidableEquiv(v_00_u03b1_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_m_u2081_28_, v_m_u2082_29_, v_h_u2081_30_, v_h_u2082_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Raw(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashSet_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_RawDecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
