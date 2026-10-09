// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EMatchTheoremPtr
// Imports: public import Lean.Meta.Tactic.Grind.EMatchTheorem
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isSameEMatchTheoremPtr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSameEMatchTheoremPtr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremPtr = (const lean_object*)&l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremPtr = (const lean_object*)&l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value;
uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
size_t v___x_3_; size_t v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_ptr_addr(v_a_1_);
v___x_4_ = lean_ptr_addr(v_b_2_);
v___x_5_ = lean_usize_dec_eq(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
uint8_t v_res_6_;
v_res_6_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_a_1_, v_b_2_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1___boxed(lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_a_7_, v_b_8_);
lean_dec_ref(v_b_8_);
lean_dec_ref(v_a_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l_Lean_Meta_Grind_isSameEMatchTheoremPtr(lean_object* v_a_11_, lean_object* v_b_12_){
_start:
{
size_t v___x_13_; size_t v___x_14_; uint8_t v___x_15_; 
v___x_13_ = lean_ptr_addr(v_a_11_);
v___x_14_ = lean_ptr_addr(v_b_12_);
v___x_15_ = lean_usize_dec_eq(v___x_13_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isSameEMatchTheoremPtr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_11_ = stack[0].m_obj;
lean_object* v_b_12_ = stack[1].m_obj;
uint8_t v_res_16_;
v_res_16_ = l_Lean_Meta_Grind_isSameEMatchTheoremPtr(v_a_11_, v_b_12_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSameEMatchTheoremPtr___boxed(lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Meta_Grind_isSameEMatchTheoremPtr(v_a_17_, v_b_18_);
lean_dec_ref(v_b_18_);
lean_dec_ref(v_a_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(lean_object* v_thm_21_){
_start:
{
size_t v___x_22_; size_t v___x_23_; size_t v___x_24_; uint64_t v___x_25_; 
v___x_22_ = lean_ptr_addr(v_thm_21_);
v___x_23_ = ((size_t)3ULL);
v___x_24_ = lean_usize_shift_right(v___x_22_, v___x_23_);
v___x_25_ = lean_usize_to_uint64(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_21_ = stack[0].m_obj;
uint64_t v_res_26_;
v_res_26_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_thm_21_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1___boxed(lean_object* v_thm_27_){
_start:
{
uint64_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_thm_27_);
lean_dec_ref(v_thm_27_);
v_r_29_ = lean_box_uint64(v_res_28_);
return v_r_29_;
}
}
uint64_t l_Lean_Meta_Grind_hashEMatchTheoremPtr(lean_object* v_thm_30_){
_start:
{
size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; uint64_t v___x_34_; 
v___x_31_ = lean_ptr_addr(v_thm_30_);
v___x_32_ = ((size_t)3ULL);
v___x_33_ = lean_usize_shift_right(v___x_31_, v___x_32_);
v___x_34_ = lean_usize_to_uint64(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_hashEMatchTheoremPtr_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_30_ = stack[0].m_obj;
uint64_t v_res_35_;
v_res_35_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr(v_thm_30_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_hashEMatchTheoremPtr___boxed(lean_object* v_thm_36_){
_start:
{
uint64_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr(v_thm_36_);
lean_dec_ref(v_thm_36_);
v_r_38_ = lean_box_uint64(v_res_37_);
return v_r_38_;
}
}
uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0(lean_object* v_k_39_){
_start:
{
size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; uint64_t v___x_43_; 
v___x_40_ = lean_ptr_addr(v_k_39_);
v___x_41_ = ((size_t)3ULL);
v___x_42_ = lean_usize_shift_right(v___x_40_, v___x_41_);
v___x_43_ = lean_usize_to_uint64(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_39_ = stack[0].m_obj;
uint64_t v_res_44_;
v_res_44_ = l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0(v_k_39_);
stack->m_num = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0___boxed(lean_object* v_k_45_){
_start:
{
uint64_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___lam__0(v_k_45_);
lean_dec_ref(v_k_45_);
v_r_47_ = lean_box_uint64(v_res_46_);
return v_r_47_;
}
}
uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0(lean_object* v_k_u2081_50_, lean_object* v_k_u2082_51_){
_start:
{
size_t v___x_52_; size_t v___x_53_; uint8_t v___x_54_; 
v___x_52_ = lean_ptr_addr(v_k_u2081_50_);
v___x_53_ = lean_ptr_addr(v_k_u2082_51_);
v___x_54_ = lean_usize_dec_eq(v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_u2081_50_ = stack[0].m_obj;
lean_object* v_k_u2082_51_ = stack[1].m_obj;
uint8_t v_res_55_;
v_res_55_ = l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0(v_k_u2081_50_, v_k_u2082_51_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0___boxed(lean_object* v_k_u2081_56_, lean_object* v_k_u2082_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___lam__0(v_k_u2081_56_, v_k_u2082_57_);
lean_dec_ref(v_k_u2082_57_);
lean_dec_ref(v_k_u2081_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
}
#ifdef __cplusplus
}
#endif
