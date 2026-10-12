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
uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_apply_2(v_inst_1_, v___y_3_, v___y_4_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_k_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
uint8_t v_res_7_;
v_res_7_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(v_inst_1_, v_k_2_, v___y_3_, v___y_4_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0___boxed(lean_object* v_inst_8_, lean_object* v_k_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0(v_inst_8_, v_k_9_, v___y_10_, v___y_11_);
lean_dec(v_k_9_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object* v_cmp_14_, lean_object* v_inst_15_, lean_object* v_t_u2081_16_, lean_object* v_t_u2082_17_){
_start:
{
lean_object* v___f_18_; uint8_t v___x_19_; 
v___f_18_ = lean_alloc_closure((void*)(l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_18_, 0, v_inst_15_);
v___x_19_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_14_, v___f_18_, v_t_u2081_16_, v_t_u2082_17_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_14_ = stack[0].m_obj;
lean_object* v_inst_15_ = stack[1].m_obj;
lean_object* v_t_u2081_16_ = stack[2].m_obj;
lean_object* v_t_u2082_17_ = stack[3].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_14_, v_inst_15_, v_t_u2081_16_, v_t_u2082_17_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(lean_object* v_cmp_21_, lean_object* v_inst_22_, lean_object* v_t_u2081_23_, lean_object* v_t_u2082_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_21_, v_inst_22_, v_t_u2081_23_, v_t_u2082_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_cmp_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_t_u2081_34_, lean_object* v_t_u2082_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(v_cmp_29_, v_inst_32_, v_t_u2081_34_, v_t_u2082_35_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_29_ = stack[2].m_obj;
lean_object* v_inst_32_ = stack[5].m_obj;
lean_object* v_t_u2081_34_ = stack[7].m_obj;
lean_object* v_t_u2082_35_ = stack[8].m_obj;
uint8_t v_res_37_;
v_res_37_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(lean_box(0), lean_box(0), v_cmp_29_, lean_box(0), lean_box(0), v_inst_32_, lean_box(0), v_t_u2081_34_, v_t_u2082_35_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_cmp_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_t_u2081_45_, lean_object* v_t_u2082_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq(v_00_u03b1_38_, v_00_u03b2_39_, v_cmp_40_, v_inst_41_, v_inst_42_, v_inst_43_, v_inst_44_, v_t_u2081_45_, v_t_u2082_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeMap_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
