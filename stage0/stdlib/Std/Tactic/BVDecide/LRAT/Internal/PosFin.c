// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.PosFin
// Imports: public import Init.Data.Hashable
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
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_eq(v_a_1_, v_b_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg___boxed(lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___redArg(v_a_4_, v_b_5_);
lean_dec(v_b_5_);
lean_dec(v_a_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin(lean_object* v_n_8_, lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_eq(v_a_9_, v_b_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(lean_object* v_n_12_, lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin(v_n_12_, v_a_13_, v_b_14_);
lean_dec(v_b_14_);
lean_dec(v_a_13_);
lean_dec(v_n_12_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0(lean_object* v_p_17_){
_start:
{
lean_inc(v_p_17_);
return v_p_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0___boxed(lean_object* v_p_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___lam__0(v_p_18_);
lean_dec(v_p_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat(lean_object* v_n_21_){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___closed__0));
return v___f_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat___boxed(lean_object* v_n_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Tactic_BVDecide_LRAT_Internal_instCoeOutPosFinNat(v_n_23_);
lean_dec(v_n_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin(lean_object* v_n_26_){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin___boxed(lean_object* v_n_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Tactic_BVDecide_LRAT_Internal_instHashablePosFin(v_n_28_);
lean_dec(v_n_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin(lean_object* v_n_31_){
_start:
{
lean_object* v___f_32_; 
v___f_32_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___closed__0));
return v___f_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin___boxed(lean_object* v_n_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringPosFin(v_n_33_);
lean_dec(v_n_33_);
return v_res_34_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
}
#ifdef __cplusplus
}
#endif
