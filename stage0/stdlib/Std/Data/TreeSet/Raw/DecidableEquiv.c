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
uint8_t l_instBEqOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_Raw_instDecidableEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0(lean_object* v___x_1_, lean_object* v_k_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_instBEqOfDecidableEq___redArg___lam__0(v___x_1_, v___y_3_, v___y_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v_k_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0(v___x_1_, v_k_2_, v___y_3_, v___y_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0___boxed(lean_object* v___x_7_, lean_object* v_k_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0(v___x_7_, v_k_8_, v___y_9_, v___y_10_);
lean_dec(v_k_8_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
static lean_object* _init_l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___f_14_; 
v___x_13_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_14_ = lean_alloc_closure((void*)(l_Std_TreeSet_Raw_instDecidableEquiv___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_14_, 0, v___x_13_);
return v___f_14_;
}
}
uint8_t l_Std_TreeSet_Raw_instDecidableEquiv___redArg(lean_object* v_cmp_15_, lean_object* v_t_u2081_16_, lean_object* v_t_u2082_17_){
_start:
{
lean_object* v___f_18_; uint8_t v___x_19_; 
v___f_18_ = lean_obj_once(&l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0, &l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0_once, _init_l_Std_TreeSet_Raw_instDecidableEquiv___redArg___closed__0);
v___x_19_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_15_, v___f_18_, v_t_u2081_16_, v_t_u2082_17_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instDecidableEquiv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_15_ = stack[0].m_obj;
lean_object* v_t_u2081_16_ = stack[1].m_obj;
lean_object* v_t_u2082_17_ = stack[2].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Std_TreeSet_Raw_instDecidableEquiv___redArg(v_cmp_15_, v_t_u2081_16_, v_t_u2082_17_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___redArg___boxed(lean_object* v_cmp_21_, lean_object* v_t_u2081_22_, lean_object* v_t_u2082_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Std_TreeSet_Raw_instDecidableEquiv___redArg(v_cmp_21_, v_t_u2081_22_, v_t_u2082_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
uint8_t l_Std_TreeSet_Raw_instDecidableEquiv(lean_object* v_00_u03b1_26_, lean_object* v_cmp_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_t_u2081_30_, lean_object* v_t_u2082_31_, lean_object* v_h_u2081_32_, lean_object* v_h_u2082_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Std_TreeSet_Raw_instDecidableEquiv___redArg(v_cmp_27_, v_t_u2081_30_, v_t_u2082_31_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Std_TreeSet_Raw_instDecidableEquiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_27_ = stack[1].m_obj;
lean_object* v_t_u2081_30_ = stack[4].m_obj;
lean_object* v_t_u2082_31_ = stack[5].m_obj;
uint8_t v_res_35_;
v_res_35_ = l_Std_TreeSet_Raw_instDecidableEquiv(lean_box(0), v_cmp_27_, lean_box(0), lean_box(0), v_t_u2081_30_, v_t_u2082_31_, lean_box(0), lean_box(0));
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Std_TreeSet_Raw_instDecidableEquiv___boxed(lean_object* v_00_u03b1_36_, lean_object* v_cmp_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_t_u2081_40_, lean_object* v_t_u2082_41_, lean_object* v_h_u2081_42_, lean_object* v_h_u2082_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Std_TreeSet_Raw_instDecidableEquiv(v_00_u03b1_36_, v_cmp_37_, v_inst_38_, v_inst_39_, v_t_u2081_40_, v_t_u2082_41_, v_h_u2081_42_, v_h_u2082_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_DecidableEquiv(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Raw_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
