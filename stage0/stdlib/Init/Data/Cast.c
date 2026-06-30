// Lean compiler output
// Module: Init.Data.Cast
// Imports: public import Init.Coe
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
LEAN_EXPORT lean_object* l_instNatCastNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instNatCastNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_instNatCastNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instNatCastNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNatCastNat___closed__0 = (const lean_object*)&l_instNatCastNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instNatCastNat = (const lean_object*)&l_instNatCastNat___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instNatCastNat___lam__0(lean_object* v_n_1_){
_start:
{
lean_inc(v_n_1_);
return v_n_1_;
}
}
LEAN_EXPORT lean_object* l_instNatCastNat___lam__0___boxed(lean_object* v_n_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_instNatCastNat___lam__0(v_n_2_);
lean_dec(v_n_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___redArg(lean_object* v_inst_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_inst_6_, v_a_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast(lean_object* v_R_9_, lean_object* v_inst_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_1(v_inst_10_, v_a_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast___redArg(lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_closure((void*)(l_Nat_cast), 3, 2);
lean_closure_set(v___x_14_, 0, lean_box(0));
lean_closure_set(v___x_14_, 1, v_inst_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_instCoeTailNatOfNatCast(lean_object* v_R_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_closure((void*)(l_Nat_cast), 3, 2);
lean_closure_set(v___x_17_, 0, lean_box(0));
lean_closure_set(v___x_17_, 1, v_inst_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast___redArg(lean_object* v_inst_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_alloc_closure((void*)(l_Nat_cast), 3, 2);
lean_closure_set(v___x_19_, 0, lean_box(0));
lean_closure_set(v___x_19_, 1, v_inst_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_instCoeHTCTNatOfNatCast(lean_object* v_R_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_closure((void*)(l_Nat_cast), 3, 2);
lean_closure_set(v___x_22_, 0, lean_box(0));
lean_closure_set(v___x_22_, 1, v_inst_21_);
return v___x_22_;
}
}
lean_object* runtime_initialize_Init_Coe(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Cast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Cast(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Coe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Cast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Cast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Cast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Cast(builtin);
}
#ifdef __cplusplus
}
#endif
