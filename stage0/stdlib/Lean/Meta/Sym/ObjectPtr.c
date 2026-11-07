// Lean compiler output
// Module: Lean.Meta.Sym.ObjectPtr
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableObjectPtr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableObjectPtr_unsafe__1___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableObjectPtr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableObjectPtr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instHashableObjectPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableObjectPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instHashableObjectPtr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instHashableObjectPtr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instHashableObjectPtr = (const lean_object*)&l_Lean_Meta_Sym_instHashableObjectPtr___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqObjectPtr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqObjectPtr_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqObjectPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqObjectPtr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instBEqObjectPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqObjectPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instBEqObjectPtr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instBEqObjectPtr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instBEqObjectPtr = (const lean_object*)&l_Lean_Meta_Sym_instBEqObjectPtr___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1___redArg(lean_object* v_a_1_){
_start:
{
lean_inc(v_a_1_);
return v_a_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1___redArg___boxed(lean_object* v_a_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1___redArg(v_a_2_);
lean_dec(v_a_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1(lean_object* v_00_u03b1_4_, lean_object* v_a_5_){
_start:
{
lean_inc(v_a_5_);
return v_a_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1___boxed(lean_object* v_00_u03b1_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_Meta_Sym_ObjectPtr_0__Lean_Meta_Sym_ObjectPtr_of_unsafe__1(v_00_u03b1_6_, v_a_7_);
lean_dec(v_a_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of___redArg(lean_object* v_a_9_){
_start:
{
lean_inc(v_a_9_);
return v_a_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of___redArg___boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Meta_Sym_ObjectPtr_of___redArg(v_a_10_);
lean_dec(v_a_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of(lean_object* v_00_u03b1_12_, lean_object* v_a_13_){
_start:
{
lean_inc(v_a_13_);
return v_a_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ObjectPtr_of___boxed(lean_object* v_00_u03b1_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_Sym_ObjectPtr_of(v_00_u03b1_14_, v_a_15_);
lean_dec(v_a_15_);
return v_res_16_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableObjectPtr_unsafe__1(lean_object* v_k_17_){
_start:
{
size_t v___x_18_; size_t v___x_19_; size_t v___x_20_; uint64_t v___x_21_; 
v___x_18_ = lean_ptr_addr(v_k_17_);
v___x_19_ = ((size_t)3ULL);
v___x_20_ = lean_usize_shift_right(v___x_18_, v___x_19_);
v___x_21_ = lean_usize_to_uint64(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableObjectPtr_unsafe__1___boxed(lean_object* v_k_22_){
_start:
{
uint64_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Lean_Meta_Sym_instHashableObjectPtr_unsafe__1(v_k_22_);
lean_dec(v_k_22_);
v_r_24_ = lean_box_uint64(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableObjectPtr___lam__0(lean_object* v_k_25_){
_start:
{
size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; uint64_t v___x_29_; 
v___x_26_ = lean_ptr_addr(v_k_25_);
v___x_27_ = ((size_t)3ULL);
v___x_28_ = lean_usize_shift_right(v___x_26_, v___x_27_);
v___x_29_ = lean_usize_to_uint64(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableObjectPtr___lam__0___boxed(lean_object* v_k_30_){
_start:
{
uint64_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Meta_Sym_instHashableObjectPtr___lam__0(v_k_30_);
lean_dec(v_k_30_);
v_r_32_ = lean_box_uint64(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqObjectPtr_unsafe__1(lean_object* v_k_u2081_35_, lean_object* v_k_u2082_36_){
_start:
{
size_t v___x_37_; size_t v___x_38_; uint8_t v___x_39_; 
v___x_37_ = lean_ptr_addr(v_k_u2081_35_);
v___x_38_ = lean_ptr_addr(v_k_u2082_36_);
v___x_39_ = lean_usize_dec_eq(v___x_37_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqObjectPtr_unsafe__1___boxed(lean_object* v_k_u2081_40_, lean_object* v_k_u2082_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Lean_Meta_Sym_instBEqObjectPtr_unsafe__1(v_k_u2081_40_, v_k_u2082_41_);
lean_dec(v_k_u2082_41_);
lean_dec(v_k_u2081_40_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqObjectPtr___lam__0(lean_object* v_k_u2081_44_, lean_object* v_k_u2082_45_){
_start:
{
size_t v___x_46_; size_t v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_ptr_addr(v_k_u2081_44_);
v___x_47_ = lean_ptr_addr(v_k_u2082_45_);
v___x_48_ = lean_usize_dec_eq(v___x_46_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqObjectPtr___lam__0___boxed(lean_object* v_k_u2081_49_, lean_object* v_k_u2082_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_Meta_Sym_instBEqObjectPtr___lam__0(v_k_u2081_49_, v_k_u2082_50_);
lean_dec(v_k_u2082_50_);
lean_dec(v_k_u2081_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_ObjectPtr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_ObjectPtr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_ObjectPtr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ObjectPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_ObjectPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_ObjectPtr(builtin);
}
#ifdef __cplusplus
}
#endif
