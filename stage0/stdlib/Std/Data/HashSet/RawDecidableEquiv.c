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
uint8_t l_instBEqOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv___redArg___lam__0(lean_object* v___x_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_instBEqOfDecidableEq___redArg___lam__0(v___x_1_, v___y_3_, v___y_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___lam__0___boxed(lean_object* v___x_6_, lean_object* v_k_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg___lam__0(v___x_6_, v_k_7_, v___y_8_, v___y_9_);
lean_dec(v_k_7_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___f_13_; 
v___x_12_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_13_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instDecidableEquiv___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_13_, 0, v___x_12_);
return v___f_13_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_m_u2081_16_, lean_object* v_m_u2082_17_){
_start:
{
lean_object* v___f_18_; uint8_t v___x_19_; 
v___f_18_ = lean_obj_once(&l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0, &l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0_once, _init_l_Std_HashSet_Raw_instDecidableEquiv___redArg___closed__0);
v___x_19_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_14_, v_inst_15_, v___f_18_, v_m_u2081_16_, v_m_u2082_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_m_u2081_22_, lean_object* v_m_u2082_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg(v_inst_20_, v_inst_21_, v_m_u2081_22_, v_m_u2082_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableEquiv(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_m_u2081_30_, lean_object* v_m_u2082_31_, lean_object* v_h_u2081_32_, lean_object* v_h_u2082_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Std_HashSet_Raw_instDecidableEquiv___redArg(v_inst_27_, v_inst_29_, v_m_u2081_30_, v_m_u2082_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_m_u2081_39_, lean_object* v_m_u2082_40_, lean_object* v_h_u2081_41_, lean_object* v_h_u2082_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Std_HashSet_Raw_instDecidableEquiv(v_00_u03b1_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_m_u2081_39_, v_m_u2082_40_, v_h_u2081_41_, v_h_u2082_42_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_RawDecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Raw(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_RawDecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
