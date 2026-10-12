// Lean compiler output
// Module: Init.Data.String.Hashable
// Imports: public import Init.Data.Hashable public import Init.Data.String.Defs
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_String_instHashableRaw_hash(lean_object*);
LEAN_EXPORT lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
static const lean_closure_object l_String_instHashableRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHashableRaw_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHashableRaw___closed__0 = (const lean_object*)&l_String_instHashableRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHashableRaw = (const lean_object*)&l_String_instHashableRaw___closed__0_value;
LEAN_EXPORT uint64_t l_String_instHashablePos_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_String_instHashablePos_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos(lean_object*);
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos__1(lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object* v_x_1_){
_start:
{
uint64_t v___x_2_; uint64_t v___x_3_; uint64_t v___x_4_; 
v___x_2_ = 0ULL;
v___x_3_ = lean_uint64_of_nat(v_x_1_);
v___x_4_ = lean_uint64_mix_hash(v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT void l_String_instHashableRaw_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint64_t v_res_5_;
v_res_5_ = l_String_instHashableRaw_hash(v_x_1_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_String_instHashableRaw_hash___boxed(lean_object* v_x_6_){
_start:
{
uint64_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_String_instHashableRaw_hash(v_x_6_);
lean_dec(v_x_6_);
v_r_8_ = lean_box_uint64(v_res_7_);
return v_r_8_;
}
}
uint64_t l_String_instHashablePos_hash___redArg(lean_object* v_x_11_){
_start:
{
uint64_t v___x_12_; uint64_t v___x_13_; uint64_t v___x_14_; uint64_t v___x_15_; 
v___x_12_ = 0ULL;
v___x_13_ = l_String_instHashableRaw_hash(v_x_11_);
v___x_14_ = lean_uint64_mix_hash(v___x_12_, v___x_13_);
v___x_15_ = lean_uint64_mix_hash(v___x_14_, v___x_12_);
return v___x_15_;
}
}
LEAN_EXPORT void l_String_instHashablePos_hash___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_11_ = stack[0].m_obj;
uint64_t v_res_16_;
v_res_16_ = l_String_instHashablePos_hash___redArg(v_x_11_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___redArg___boxed(lean_object* v_x_17_){
_start:
{
uint64_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_String_instHashablePos_hash___redArg(v_x_17_);
lean_dec(v_x_17_);
v_r_19_ = lean_box_uint64(v_res_18_);
return v_r_19_;
}
}
uint64_t l_String_instHashablePos_hash(lean_object* v_s_20_, lean_object* v_x_21_){
_start:
{
uint64_t v___x_22_; 
v___x_22_ = l_String_instHashablePos_hash___redArg(v_x_21_);
return v___x_22_;
}
}
LEAN_EXPORT void l_String_instHashablePos_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_20_ = stack[0].m_obj;
lean_object* v_x_21_ = stack[1].m_obj;
uint64_t v_res_23_;
v_res_23_ = l_String_instHashablePos_hash(v_s_20_, v_x_21_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___boxed(lean_object* v_s_24_, lean_object* v_x_25_){
_start:
{
uint64_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_String_instHashablePos_hash(v_s_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec_ref(v_s_24_);
v_r_27_ = lean_box_uint64(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos(lean_object* v_s_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_alloc_closure((void*)(l_String_instHashablePos_hash___boxed), 2, 1);
lean_closure_set(v___x_29_, 0, v_s_28_);
return v___x_29_;
}
}
uint64_t l_String_instHashablePos__1_hash___redArg(lean_object* v_x_30_){
_start:
{
uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; 
v___x_31_ = 0ULL;
v___x_32_ = l_String_instHashableRaw_hash(v_x_30_);
v___x_33_ = lean_uint64_mix_hash(v___x_31_, v___x_32_);
v___x_34_ = lean_uint64_mix_hash(v___x_33_, v___x_31_);
return v___x_34_;
}
}
LEAN_EXPORT void l_String_instHashablePos__1_hash___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_30_ = stack[0].m_obj;
uint64_t v_res_35_;
v_res_35_ = l_String_instHashablePos__1_hash___redArg(v_x_30_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___redArg___boxed(lean_object* v_x_36_){
_start:
{
uint64_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_String_instHashablePos__1_hash___redArg(v_x_36_);
lean_dec(v_x_36_);
v_r_38_ = lean_box_uint64(v_res_37_);
return v_r_38_;
}
}
uint64_t l_String_instHashablePos__1_hash(lean_object* v_s_39_, lean_object* v_x_40_){
_start:
{
uint64_t v___x_41_; 
v___x_41_ = l_String_instHashablePos__1_hash___redArg(v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l_String_instHashablePos__1_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_39_ = stack[0].m_obj;
lean_object* v_x_40_ = stack[1].m_obj;
uint64_t v_res_42_;
v_res_42_ = l_String_instHashablePos__1_hash(v_s_39_, v_x_40_);
stack->m_num = v_res_42_;
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___boxed(lean_object* v_s_43_, lean_object* v_x_44_){
_start:
{
uint64_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_String_instHashablePos__1_hash(v_s_43_, v_x_44_);
lean_dec(v_x_44_);
lean_dec_ref(v_s_43_);
v_r_46_ = lean_box_uint64(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1(lean_object* v_s_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_alloc_closure((void*)(l_String_instHashablePos__1_hash___boxed), 2, 1);
lean_closure_set(v___x_48_, 0, v_s_47_);
return v___x_48_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Hashable(builtin);
}
#ifdef __cplusplus
}
#endif
