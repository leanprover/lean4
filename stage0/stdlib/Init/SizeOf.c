// Lean compiler output
// Module: Init.SizeOf
// Imports: public import Init.Notation import Init.Tactics
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
LEAN_EXPORT lean_object* l_default_sizeOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_default_sizeOf___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSizeOfDefault___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_default_sizeOf___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instSizeOfDefault___closed__0 = (const lean_object*)&l_instSizeOfDefault___closed__0_value;
LEAN_EXPORT lean_object* l_instSizeOfDefault(lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_instSizeOfNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSizeOfNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSizeOfNat___closed__0 = (const lean_object*)&l_instSizeOfNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instSizeOfNat = (const lean_object*)&l_instSizeOfNat___closed__0_value;
LEAN_EXPORT lean_object* l_instSizeOfForallUnit___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfForallUnit___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instSizeOfForallUnit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_default_sizeOf(lean_object* v_00_u03b1_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(0u);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_default_sizeOf___boxed(lean_object* v_00_u03b1_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_default_sizeOf(v_00_u03b1_4_, v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_instSizeOfDefault(lean_object* v_00_u03b1_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = ((lean_object*)(l_instSizeOfDefault___closed__0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_instSizeOfNat___lam__0(lean_object* v_n_10_){
_start:
{
lean_inc(v_n_10_);
return v_n_10_;
}
}
LEAN_EXPORT lean_object* l_instSizeOfNat___lam__0___boxed(lean_object* v_n_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_instSizeOfNat___lam__0(v_n_11_);
lean_dec(v_n_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_instSizeOfForallUnit___redArg___lam__0(lean_object* v_inst_15_, lean_object* v_f_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_f_16_, v___x_17_);
v___x_19_ = lean_apply_1(v_inst_15_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_instSizeOfForallUnit___redArg(lean_object* v_inst_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = lean_alloc_closure((void*)(l_instSizeOfForallUnit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_21_, 0, v_inst_20_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_instSizeOfForallUnit(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = lean_alloc_closure((void*)(l_instSizeOfForallUnit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_24_, 0, v_inst_23_);
return v___f_24_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Init_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_SizeOf(builtin);
}
#ifdef __cplusplus
}
#endif
