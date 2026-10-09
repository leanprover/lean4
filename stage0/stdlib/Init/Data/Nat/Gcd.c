// Lean compiler output
// Module: Init.Data.Nat.Gcd
// Imports: public import Init.NotationExtra public import Init.Data.Nat.Div.Basic import Init.Data.Nat.Dvd import Init.RCases import Init.WFTactics
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_gcd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT void l_Nat_gcd_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1_ = stack[0].m_obj;
lean_object* v_n_2_ = stack[1].m_obj;
lean_object* v_res_3_;
v_res_3_ = lean_nat_gcd(v_m_1_, v_n_2_);
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Nat_gcd___boxed(lean_object* v_m_4_, lean_object* v_n_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_nat_gcd(v_m_4_, v_n_5_);
lean_dec(v_n_5_);
lean_dec(v_m_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg(lean_object* v_k_7_, lean_object* v_m_8_, lean_object* v_n_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_10_ = lean_nat_gcd(v_k_7_, v_m_8_);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_nat_dec_eq(v___x_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_n_9_);
v___x_13_ = lean_nat_div(v_k_7_, v___x_10_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_10_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v___x_15_; 
lean_dec(v___x_10_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_11_);
lean_ctor_set(v___x_15_, 1, v_n_9_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg___boxed(lean_object* v_k_16_, lean_object* v_m_17_, lean_object* v_n_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_16_, v_m_17_, v_n_18_);
lean_dec(v_m_17_);
lean_dec(v_k_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd(lean_object* v_k_20_, lean_object* v_m_21_, lean_object* v_n_22_, lean_object* v_h_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_20_, v_m_21_, v_n_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___boxed(lean_object* v_k_25_, lean_object* v_m_26_, lean_object* v_n_27_, lean_object* v_h_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Nat_dvdProdDvdOfDvdProd(v_k_25_, v_m_26_, v_n_27_, v_h_28_);
lean_dec(v_m_26_);
lean_dec(v_k_25_);
return v_res_29_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Gcd(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Gcd(builtin);
}
#ifdef __cplusplus
}
#endif
