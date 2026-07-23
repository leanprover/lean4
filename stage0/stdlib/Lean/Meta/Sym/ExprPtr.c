// Lean compiler output
// Module: Lean.Meta.Sym.ExprPtr
// Imports: public import Lean.Expr
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isSameExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isSameExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_hashPtrExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_hashPtrExpr___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableExprPtr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instHashableExprPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instHashableExprPtr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instHashableExprPtr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instHashableExprPtr = (const lean_object*)&l_Lean_Meta_Sym_instHashableExprPtr___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqExprPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instBEqExprPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instBEqExprPtr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instBEqExprPtr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instBEqExprPtr = (const lean_object*)&l_Lean_Meta_Sym_instBEqExprPtr___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
size_t v___x_3_; size_t v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_ptr_addr(v_a_1_);
v___x_4_ = lean_ptr_addr(v_b_2_);
v___x_5_ = lean_usize_dec_eq(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_6_, v_b_7_);
lean_dec_ref(v_b_7_);
lean_dec_ref(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isSameExpr(lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
size_t v___x_12_; size_t v___x_13_; uint8_t v___x_14_; 
v___x_12_ = lean_ptr_addr(v_a_10_);
v___x_13_ = lean_ptr_addr(v_b_11_);
v___x_14_ = lean_usize_dec_eq(v___x_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isSameExpr___boxed(lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Meta_Sym_isSameExpr(v_a_15_, v_b_16_);
lean_dec_ref(v_b_16_);
lean_dec_ref(v_a_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object* v_e_19_){
_start:
{
size_t v___x_20_; size_t v___x_21_; size_t v___x_22_; uint64_t v___x_23_; 
v___x_20_ = lean_ptr_addr(v_e_19_);
v___x_21_ = ((size_t)3ULL);
v___x_22_ = lean_usize_shift_right(v___x_20_, v___x_21_);
v___x_23_ = lean_usize_to_uint64(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object* v_e_24_){
_start:
{
uint64_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_24_);
lean_dec_ref(v_e_24_);
v_r_26_ = lean_box_uint64(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_hashPtrExpr(lean_object* v_e_27_){
_start:
{
size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; uint64_t v___x_31_; 
v___x_28_ = lean_ptr_addr(v_e_27_);
v___x_29_ = ((size_t)3ULL);
v___x_30_ = lean_usize_shift_right(v___x_28_, v___x_29_);
v___x_31_ = lean_usize_to_uint64(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_hashPtrExpr___boxed(lean_object* v_e_32_){
_start:
{
uint64_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Meta_Sym_hashPtrExpr(v_e_32_);
lean_dec_ref(v_e_32_);
v_r_34_ = lean_box_uint64(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableExprPtr___lam__0(lean_object* v_k_35_){
_start:
{
size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; uint64_t v___x_39_; 
v___x_36_ = lean_ptr_addr(v_k_35_);
v___x_37_ = ((size_t)3ULL);
v___x_38_ = lean_usize_shift_right(v___x_36_, v___x_37_);
v___x_39_ = lean_usize_to_uint64(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object* v_k_40_){
_start:
{
uint64_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Lean_Meta_Sym_instHashableExprPtr___lam__0(v_k_40_);
lean_dec_ref(v_k_40_);
v_r_42_ = lean_box_uint64(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqExprPtr___lam__0(lean_object* v_k_u2081_45_, lean_object* v_k_u2082_46_){
_start:
{
size_t v___x_47_; size_t v___x_48_; uint8_t v___x_49_; 
v___x_47_ = lean_ptr_addr(v_k_u2081_45_);
v___x_48_ = lean_ptr_addr(v_k_u2082_46_);
v___x_49_ = lean_usize_dec_eq(v___x_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object* v_k_u2081_50_, lean_object* v_k_u2082_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_Meta_Sym_instBEqExprPtr___lam__0(v_k_u2081_50_, v_k_u2082_51_);
lean_dec_ref(v_k_u2082_51_);
lean_dec_ref(v_k_u2081_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_ExprPtr(builtin);
}
#ifdef __cplusplus
}
#endif
