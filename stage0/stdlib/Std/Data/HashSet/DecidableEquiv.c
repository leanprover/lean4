// Lean compiler output
// Module: Std.Data.HashSet.DecidableEquiv
// Imports: public import Std.Data.HashMap.DecidableEquiv public import Std.Data.HashSet.Basic
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
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableEquivOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableEquivOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0(lean_object* v___x_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_instBEqOfDecidableEq___redArg___lam__0(v___x_1_, v___y_3_, v___y_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v_k_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0(v___x_1_, v_k_2_, v___y_3_, v___y_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed(lean_object* v___x_7_, lean_object* v_k_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0(v___x_7_, v_k_8_, v___y_9_, v___y_10_);
lean_dec(v_k_8_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
static lean_object* _init_l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___f_14_; 
v___x_13_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_14_ = lean_alloc_closure((void*)(l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_14_, 0, v___x_13_);
return v___f_14_;
}
}
uint8_t l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_m_u2081_17_, lean_object* v_m_u2082_18_){
_start:
{
lean_object* v___f_19_; uint8_t v___x_20_; 
v___f_19_ = lean_obj_once(&l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0, &l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0_once, _init_l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___closed__0);
v___x_20_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_15_, v_inst_16_, v___f_19_, v_m_u2081_17_, v_m_u2082_18_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_15_ = stack[0].m_obj;
lean_object* v_inst_16_ = stack[1].m_obj;
lean_object* v_m_u2081_17_ = stack[2].m_obj;
lean_object* v_m_u2082_18_ = stack[3].m_obj;
uint8_t v_res_21_;
v_res_21_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(v_inst_15_, v_inst_16_, v_m_u2081_17_, v_m_u2082_18_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg___boxed(lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_m_u2081_24_, lean_object* v_m_u2082_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(v_inst_22_, v_inst_23_, v_m_u2081_24_, v_m_u2082_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
uint8_t l_Std_HashSet_instDecidableEquivOfLawfulBEq(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_m_u2081_32_, lean_object* v_m_u2082_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq___redArg(v_inst_29_, v_inst_31_, v_m_u2081_32_, v_m_u2082_33_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Std_HashSet_instDecidableEquivOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_29_ = stack[1].m_obj;
lean_object* v_inst_31_ = stack[3].m_obj;
lean_object* v_m_u2081_32_ = stack[4].m_obj;
lean_object* v_m_u2082_33_ = stack[5].m_obj;
uint8_t v_res_35_;
v_res_35_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq(lean_box(0), v_inst_29_, lean_box(0), v_inst_31_, v_m_u2081_32_, v_m_u2082_33_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableEquivOfLawfulBEq___boxed(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_m_u2081_40_, lean_object* v_m_u2082_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Std_HashSet_instDecidableEquivOfLawfulBEq(v_00_u03b1_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_m_u2081_40_, v_m_u2082_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_DecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashSet_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_DecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashSet_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashSet_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
