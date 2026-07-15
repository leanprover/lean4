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
LEAN_EXPORT lean_object* l_Nat_gcd___boxed(lean_object* v_m_3_, lean_object* v_n_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_nat_gcd(v_m_3_, v_n_4_);
lean_dec(v_n_4_);
lean_dec(v_m_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg(lean_object* v_k_6_, lean_object* v_m_7_, lean_object* v_n_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_9_ = lean_nat_gcd(v_k_6_, v_m_7_);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_nat_dec_eq(v___x_9_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v_n_8_);
v___x_12_ = lean_nat_div(v_k_6_, v___x_9_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_9_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
else
{
lean_object* v___x_14_; 
lean_dec(v___x_9_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_10_);
lean_ctor_set(v___x_14_, 1, v_n_8_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg___boxed(lean_object* v_k_15_, lean_object* v_m_16_, lean_object* v_n_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_15_, v_m_16_, v_n_17_);
lean_dec(v_m_16_);
lean_dec(v_k_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd(lean_object* v_k_19_, lean_object* v_m_20_, lean_object* v_n_21_, lean_object* v_h_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_19_, v_m_20_, v_n_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Nat_dvdProdDvdOfDvdProd___boxed(lean_object* v_k_24_, lean_object* v_m_25_, lean_object* v_n_26_, lean_object* v_h_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Nat_dvdProdDvdOfDvdProd(v_k_24_, v_m_25_, v_n_26_, v_h_27_);
lean_dec(v_m_25_);
lean_dec(v_k_24_);
return v_res_28_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
