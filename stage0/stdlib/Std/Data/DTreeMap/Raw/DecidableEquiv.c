// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.DecidableEquiv
// Imports: public import Std.Data.DTreeMap.Internal.Lemmas public import Std.Data.DTreeMap.Raw.Basic
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(lean_object* v_cmp_1_, lean_object* v_inst_2_, lean_object* v_t_u2081_3_, lean_object* v_t_u2082_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_1_, v_inst_2_, v_t_u2081_3_, v_t_u2082_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instDecidableEquiv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
lean_object* v_t_u2081_3_ = stack[2].m_obj;
lean_object* v_t_u2082_4_ = stack[3].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(v_cmp_1_, v_inst_2_, v_t_u2081_3_, v_t_u2082_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_cmp_7_, lean_object* v_inst_8_, lean_object* v_t_u2081_9_, lean_object* v_t_u2082_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_DTreeMap_Raw_instDecidableEquiv___redArg(v_cmp_7_, v_inst_8_, v_t_u2081_9_, v_t_u2082_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
uint8_t l_Std_DTreeMap_Raw_instDecidableEquiv(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_cmp_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_t_u2081_20_, lean_object* v_t_u2082_21_, lean_object* v_h_u2081_22_, lean_object* v_h_u2082_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_15_, v_inst_18_, v_t_u2081_20_, v_t_u2082_21_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instDecidableEquiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_15_ = stack[2].m_obj;
lean_object* v_inst_18_ = stack[5].m_obj;
lean_object* v_t_u2081_20_ = stack[7].m_obj;
lean_object* v_t_u2082_21_ = stack[8].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Std_DTreeMap_Raw_instDecidableEquiv(lean_box(0), lean_box(0), v_cmp_15_, lean_box(0), lean_box(0), v_inst_18_, lean_box(0), v_t_u2081_20_, v_t_u2082_21_, lean_box(0), lean_box(0));
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_cmp_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_t_u2081_33_, lean_object* v_t_u2082_34_, lean_object* v_h_u2081_35_, lean_object* v_h_u2082_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_DTreeMap_Raw_instDecidableEquiv(v_00_u03b1_26_, v_00_u03b2_27_, v_cmp_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_t_u2081_33_, v_t_u2082_34_, v_h_u2081_35_, v_h_u2082_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
}
#ifdef __cplusplus
}
#endif
