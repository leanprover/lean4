// Lean compiler output
// Module: Std.Data.HashMap.DecidableEquiv
// Imports: public import Std.Data.DHashMap.DecidableEquiv public import Std.Data.HashMap.Basic
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
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableEquivOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableEquivOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_apply_2(v_inst_1_, v___y_3_, v___y_4_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_k_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
uint8_t v_res_7_;
v_res_7_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0(v_inst_1_, v_k_2_, v___y_3_, v___y_4_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed(lean_object* v_inst_8_, lean_object* v_k_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0(v_inst_8_, v_k_9_, v___y_10_, v___y_11_);
lean_dec(v_k_9_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_m_u2081_17_, lean_object* v_m_u2082_18_){
_start:
{
lean_object* v___f_19_; uint8_t v___x_20_; 
v___f_19_ = lean_alloc_closure((void*)(l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_19_, 0, v_inst_16_);
v___x_20_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_14_, v_inst_15_, v___f_19_, v_m_u2081_17_, v_m_u2082_18_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_14_ = stack[0].m_obj;
lean_object* v_inst_15_ = stack[1].m_obj;
lean_object* v_inst_16_ = stack[2].m_obj;
lean_object* v_m_u2081_17_ = stack[3].m_obj;
lean_object* v_m_u2082_18_ = stack[4].m_obj;
uint8_t v_res_21_;
v_res_21_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(v_inst_14_, v_inst_15_, v_inst_16_, v_m_u2081_17_, v_m_u2082_18_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg___boxed(lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_m_u2081_25_, lean_object* v_m_u2082_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(v_inst_22_, v_inst_23_, v_inst_24_, v_m_u2081_25_, v_m_u2082_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
uint8_t l_Std_HashMap_instDecidableEquivOfLawfulBEq(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_m_u2081_36_, lean_object* v_m_u2082_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq___redArg(v_inst_31_, v_inst_33_, v_inst_34_, v_m_u2081_36_, v_m_u2082_37_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Std_HashMap_instDecidableEquivOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_31_ = stack[2].m_obj;
lean_object* v_inst_33_ = stack[4].m_obj;
lean_object* v_inst_34_ = stack[5].m_obj;
lean_object* v_m_u2081_36_ = stack[7].m_obj;
lean_object* v_m_u2082_37_ = stack[8].m_obj;
uint8_t v_res_39_;
v_res_39_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq(lean_box(0), lean_box(0), v_inst_31_, lean_box(0), v_inst_33_, v_inst_34_, lean_box(0), v_m_u2081_36_, v_m_u2082_37_);
stack->m_num = v_res_39_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableEquivOfLawfulBEq___boxed(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_m_u2081_47_, lean_object* v_m_u2082_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Std_HashMap_instDecidableEquivOfLawfulBEq(v_00_u03b1_40_, v_00_u03b2_41_, v_inst_42_, v_inst_43_, v_inst_44_, v_inst_45_, v_inst_46_, v_m_u2081_47_, v_m_u2082_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_DecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_DecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashMap_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
