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
LEAN_EXPORT uint64_t l_String_instHashableRaw_hash(lean_object* v_x_1_){
_start:
{
uint64_t v___x_2_; uint64_t v___x_3_; uint64_t v___x_4_; 
v___x_2_ = 0ULL;
v___x_3_ = lean_uint64_of_nat(v_x_1_);
v___x_4_ = lean_uint64_mix_hash(v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_instHashableRaw_hash___boxed(lean_object* v_x_5_){
_start:
{
uint64_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_String_instHashableRaw_hash(v_x_5_);
lean_dec(v_x_5_);
v_r_7_ = lean_box_uint64(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos_hash___redArg(lean_object* v_x_10_){
_start:
{
uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v___x_13_; uint64_t v___x_14_; 
v___x_11_ = 0ULL;
v___x_12_ = l_String_instHashableRaw_hash(v_x_10_);
v___x_13_ = lean_uint64_mix_hash(v___x_11_, v___x_12_);
v___x_14_ = lean_uint64_mix_hash(v___x_13_, v___x_11_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___redArg___boxed(lean_object* v_x_15_){
_start:
{
uint64_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_String_instHashablePos_hash___redArg(v_x_15_);
lean_dec(v_x_15_);
v_r_17_ = lean_box_uint64(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos_hash(lean_object* v_s_18_, lean_object* v_x_19_){
_start:
{
uint64_t v___x_20_; 
v___x_20_ = l_String_instHashablePos_hash___redArg(v_x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___boxed(lean_object* v_s_21_, lean_object* v_x_22_){
_start:
{
uint64_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_String_instHashablePos_hash(v_s_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec_ref(v_s_21_);
v_r_24_ = lean_box_uint64(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos(lean_object* v_s_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_closure((void*)(l_String_instHashablePos_hash___boxed), 2, 1);
lean_closure_set(v___x_26_, 0, v_s_25_);
return v___x_26_;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash___redArg(lean_object* v_x_27_){
_start:
{
uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; 
v___x_28_ = 0ULL;
v___x_29_ = l_String_instHashableRaw_hash(v_x_27_);
v___x_30_ = lean_uint64_mix_hash(v___x_28_, v___x_29_);
v___x_31_ = lean_uint64_mix_hash(v___x_30_, v___x_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___redArg___boxed(lean_object* v_x_32_){
_start:
{
uint64_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_String_instHashablePos__1_hash___redArg(v_x_32_);
lean_dec(v_x_32_);
v_r_34_ = lean_box_uint64(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash(lean_object* v_s_35_, lean_object* v_x_36_){
_start:
{
uint64_t v___x_37_; 
v___x_37_ = l_String_instHashablePos__1_hash___redArg(v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___boxed(lean_object* v_s_38_, lean_object* v_x_39_){
_start:
{
uint64_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_String_instHashablePos__1_hash(v_s_38_, v_x_39_);
lean_dec(v_x_39_);
lean_dec_ref(v_s_38_);
v_r_41_ = lean_box_uint64(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1(lean_object* v_s_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_alloc_closure((void*)(l_String_instHashablePos__1_hash___boxed), 2, 1);
lean_closure_set(v___x_43_, 0, v_s_42_);
return v___x_43_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
