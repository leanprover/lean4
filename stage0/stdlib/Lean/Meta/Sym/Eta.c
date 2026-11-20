// Lean compiler output
// Module: Lean.Meta.Sym.Eta
// Imports: public import Lean.Meta.Sym.ExprPtr public import Lean.Meta.Basic import Lean.Meta.Transform
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
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isEtaReducible(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isEtaReducible___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_etaReduceAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_isEtaReducible___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_etaReduceAll___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_etaReduceAll___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_etaReduceAll___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_etaReduceAll___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_etaReduceAll___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_etaReduceAll___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(lean_object* v_e_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_zero_3_; uint8_t v_isZero_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v_isZero_4_ = lean_nat_dec_eq(v_a_2_, v_zero_3_);
if (v_isZero_4_ == 1)
{
uint8_t v___x_5_; 
lean_dec(v_a_2_);
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; uint8_t v___x_8_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_a_2_, v_one_6_);
lean_dec(v_a_2_);
v___x_8_ = lean_expr_has_loose_bvar(v_e_1_, v_n_7_);
if (v___x_8_ == 0)
{
v_a_2_ = v_n_7_;
goto _start;
}
else
{
lean_dec(v_n_7_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go___boxed(lean_object* v_e_10_, lean_object* v_a_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(v_e_10_, v_a_11_);
lean_dec_ref(v_e_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(lean_object* v_e_14_, lean_object* v_n_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_Lean_Expr_hasLooseBVars(v_e_14_);
if (v___x_16_ == 0)
{
lean_dec(v_n_15_);
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(v_e_14_, v_n_15_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange___boxed(lean_object* v_e_18_, lean_object* v_n_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(v_e_18_, v_n_19_);
lean_dec_ref(v_e_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(lean_object* v_n_22_, lean_object* v_default_23_, lean_object* v_body_24_, lean_object* v_m_25_, lean_object* v_i_26_){
_start:
{
lean_object* v_zero_27_; uint8_t v_isZero_28_; 
v_zero_27_ = lean_unsigned_to_nat(0u);
v_isZero_28_ = lean_nat_dec_eq(v_m_25_, v_zero_27_);
if (v_isZero_28_ == 1)
{
uint8_t v___x_29_; 
lean_dec(v_i_26_);
lean_dec(v_m_25_);
lean_inc(v_n_22_);
v___x_29_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(v_body_24_, v_n_22_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
v___x_30_ = lean_expr_lower_loose_bvars(v_body_24_, v_n_22_, v_n_22_);
lean_dec(v_n_22_);
return v___x_30_;
}
else
{
lean_dec(v_n_22_);
lean_inc_ref(v_default_23_);
return v_default_23_;
}
}
else
{
if (lean_obj_tag(v_body_24_) == 5)
{
lean_object* v_arg_31_; 
v_arg_31_ = lean_ctor_get(v_body_24_, 1);
if (lean_obj_tag(v_arg_31_) == 0)
{
lean_object* v_fn_32_; lean_object* v_deBruijnIndex_33_; uint8_t v___x_34_; 
v_fn_32_ = lean_ctor_get(v_body_24_, 0);
v_deBruijnIndex_33_ = lean_ctor_get(v_arg_31_, 0);
v___x_34_ = lean_nat_dec_eq(v_deBruijnIndex_33_, v_i_26_);
if (v___x_34_ == 0)
{
lean_dec(v_i_26_);
lean_dec(v_m_25_);
lean_dec(v_n_22_);
lean_inc_ref(v_default_23_);
return v_default_23_;
}
else
{
lean_object* v_one_35_; lean_object* v_n_36_; lean_object* v___x_37_; 
v_one_35_ = lean_unsigned_to_nat(1u);
v_n_36_ = lean_nat_sub(v_m_25_, v_one_35_);
lean_dec(v_m_25_);
v___x_37_ = lean_nat_add(v_i_26_, v_one_35_);
lean_dec(v_i_26_);
v_body_24_ = v_fn_32_;
v_m_25_ = v_n_36_;
v_i_26_ = v___x_37_;
goto _start;
}
}
else
{
lean_dec(v_i_26_);
lean_dec(v_m_25_);
lean_dec(v_n_22_);
lean_inc_ref(v_default_23_);
return v_default_23_;
}
}
else
{
lean_dec(v_i_26_);
lean_dec(v_m_25_);
lean_dec(v_n_22_);
lean_inc_ref(v_default_23_);
return v_default_23_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go___boxed(lean_object* v_n_39_, lean_object* v_default_40_, lean_object* v_body_41_, lean_object* v_m_42_, lean_object* v_i_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(v_n_39_, v_default_40_, v_body_41_, v_m_42_, v_i_43_);
lean_dec_ref(v_body_41_);
lean_dec_ref(v_default_40_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(lean_object* v_body_45_, lean_object* v_n_46_, lean_object* v_i_47_, lean_object* v_default_48_){
_start:
{
lean_object* v___x_49_; 
lean_inc(v_n_46_);
v___x_49_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(v_n_46_, v_default_48_, v_body_45_, v_n_46_, v_i_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux___boxed(lean_object* v_body_50_, lean_object* v_n_51_, lean_object* v_i_52_, lean_object* v_default_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(v_body_50_, v_n_51_, v_i_52_, v_default_53_);
lean_dec_ref(v_default_53_);
lean_dec_ref(v_body_50_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(lean_object* v_e_55_, lean_object* v_body_56_, lean_object* v_n_57_){
_start:
{
if (lean_obj_tag(v_body_56_) == 6)
{
lean_object* v_body_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_body_58_ = lean_ctor_get(v_body_56_, 2);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_n_57_, v___x_59_);
lean_dec(v_n_57_);
v_body_56_ = v_body_58_;
v_n_57_ = v___x_60_;
goto _start;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_57_);
v___x_63_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(v_n_57_, v_e_55_, v_body_56_, v_n_57_, v___x_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go___boxed(lean_object* v_e_64_, lean_object* v_body_65_, lean_object* v_n_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_64_, v_body_65_, v_n_66_);
lean_dec_ref(v_body_65_);
lean_dec_ref(v_e_64_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce(lean_object* v_e_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_Expr_isLambda(v_e_68_);
if (v___x_69_ == 0)
{
lean_inc_ref(v_e_68_);
return v_e_68_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_68_, v_e_68_, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce___boxed(lean_object* v_e_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Sym_etaReduce(v_e_72_);
lean_dec_ref(v_e_72_);
return v_res_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isEtaReducible(lean_object* v_e_74_){
_start:
{
lean_object* v___x_75_; size_t v___x_76_; size_t v___x_77_; uint8_t v___x_78_; 
v___x_75_ = l_Lean_Meta_Sym_etaReduce(v_e_74_);
v___x_76_ = lean_ptr_addr(v_e_74_);
v___x_77_ = lean_ptr_addr(v___x_75_);
lean_dec_ref(v___x_75_);
v___x_78_ = lean_usize_dec_eq(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isEtaReducible___boxed(lean_object* v_e_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lean_Meta_Sym_isEtaReducible(v_e_81_);
lean_dec_ref(v_e_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(lean_object* v_a_84_, lean_object* v_b_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_dec(v_b_85_);
lean_dec_ref(v_a_84_);
return v_x_86_;
}
else
{
lean_object* v_key_87_; lean_object* v_value_88_; lean_object* v_tail_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_103_; 
v_key_87_ = lean_ctor_get(v_x_86_, 0);
v_value_88_ = lean_ctor_get(v_x_86_, 1);
v_tail_89_ = lean_ctor_get(v_x_86_, 2);
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_103_ == 0)
{
v___x_91_ = v_x_86_;
v_isShared_92_ = v_isSharedCheck_103_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_tail_89_);
lean_inc(v_value_88_);
lean_inc(v_key_87_);
lean_dec(v_x_86_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_103_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
size_t v___x_93_; size_t v___x_94_; uint8_t v___x_95_; 
v___x_93_ = lean_ptr_addr(v_key_87_);
v___x_94_ = lean_ptr_addr(v_a_84_);
v___x_95_ = lean_usize_dec_eq(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_84_, v_b_85_, v_tail_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 2, v___x_96_);
v___x_98_ = v___x_91_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_key_87_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_value_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
else
{
lean_object* v___x_101_; 
lean_dec(v_value_88_);
lean_dec(v_key_87_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_b_85_);
lean_ctor_set(v___x_91_, 0, v_a_84_);
v___x_101_ = v___x_91_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_84_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_b_85_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_tail_89_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
return v_x_104_;
}
else
{
lean_object* v_key_106_; lean_object* v_value_107_; lean_object* v_tail_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_134_; 
v_key_106_ = lean_ctor_get(v_x_105_, 0);
v_value_107_ = lean_ctor_get(v_x_105_, 1);
v_tail_108_ = lean_ctor_get(v_x_105_, 2);
v_isSharedCheck_134_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_134_ == 0)
{
v___x_110_ = v_x_105_;
v_isShared_111_ = v_isSharedCheck_134_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_tail_108_);
lean_inc(v_value_107_);
lean_inc(v_key_106_);
lean_dec(v_x_105_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_134_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v_fold_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; size_t v___x_123_; size_t v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_112_ = lean_array_get_size(v_x_104_);
v___x_113_ = lean_ptr_addr(v_key_106_);
v___x_114_ = ((size_t)3ULL);
v___x_115_ = lean_usize_shift_right(v___x_113_, v___x_114_);
v___x_116_ = lean_usize_to_uint64(v___x_115_);
v___x_117_ = 32ULL;
v___x_118_ = lean_uint64_shift_right(v___x_116_, v___x_117_);
v_fold_119_ = lean_uint64_xor(v___x_116_, v___x_118_);
v___x_120_ = 16ULL;
v___x_121_ = lean_uint64_shift_right(v_fold_119_, v___x_120_);
v___x_122_ = lean_uint64_xor(v_fold_119_, v___x_121_);
v___x_123_ = lean_uint64_to_usize(v___x_122_);
v___x_124_ = lean_usize_of_nat(v___x_112_);
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_sub(v___x_124_, v___x_125_);
v___x_127_ = lean_usize_land(v___x_123_, v___x_126_);
v___x_128_ = lean_array_uget_borrowed(v_x_104_, v___x_127_);
lean_inc(v___x_128_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 2, v___x_128_);
v___x_130_ = v___x_110_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_key_106_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_value_107_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v___x_128_);
v___x_130_ = v_reuseFailAlloc_133_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; 
v___x_131_ = lean_array_uset(v_x_104_, v___x_127_, v___x_130_);
v_x_104_ = v___x_131_;
v_x_105_ = v_tail_108_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(lean_object* v_i_135_, lean_object* v_source_136_, lean_object* v_target_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_array_get_size(v_source_136_);
v___x_139_ = lean_nat_dec_lt(v_i_135_, v___x_138_);
if (v___x_139_ == 0)
{
lean_dec_ref(v_source_136_);
lean_dec(v_i_135_);
return v_target_137_;
}
else
{
lean_object* v_es_140_; lean_object* v___x_141_; lean_object* v_source_142_; lean_object* v_target_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_es_140_ = lean_array_fget(v_source_136_, v_i_135_);
v___x_141_ = lean_box(0);
v_source_142_ = lean_array_fset(v_source_136_, v_i_135_, v___x_141_);
v_target_143_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_137_, v_es_140_);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_add(v_i_135_, v___x_144_);
lean_dec(v_i_135_);
v_i_135_ = v___x_145_;
v_source_136_ = v_source_142_;
v_target_137_ = v_target_143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(lean_object* v_data_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_nbuckets_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_148_ = lean_array_get_size(v_data_147_);
v___x_149_ = lean_unsigned_to_nat(2u);
v_nbuckets_150_ = lean_nat_mul(v___x_148_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_box(0);
v___x_153_ = lean_mk_array(v_nbuckets_150_, v___x_152_);
v___x_154_ = lean_array_propagate_mark(v_data_147_, v___x_153_);
v___x_155_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v___x_151_, v_data_147_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
else
{
lean_object* v_key_159_; lean_object* v_tail_160_; size_t v___x_161_; size_t v___x_162_; uint8_t v___x_163_; 
v_key_159_ = lean_ctor_get(v_x_157_, 0);
v_tail_160_ = lean_ctor_get(v_x_157_, 2);
v___x_161_ = lean_ptr_addr(v_key_159_);
v___x_162_ = lean_ptr_addr(v_a_156_);
v___x_163_ = lean_usize_dec_eq(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
v_x_157_ = v_tail_160_;
goto _start;
}
else
{
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_165_, v_x_166_);
lean_dec(v_x_166_);
lean_dec_ref(v_a_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object* v_m_169_, lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
lean_object* v_size_172_; lean_object* v_buckets_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_219_; 
v_size_172_ = lean_ctor_get(v_m_169_, 0);
v_buckets_173_ = lean_ctor_get(v_m_169_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_m_169_);
if (v_isSharedCheck_219_ == 0)
{
v___x_175_ = v_m_169_;
v_isShared_176_ = v_isSharedCheck_219_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_buckets_173_);
lean_inc(v_size_172_);
lean_dec(v_m_169_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_219_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v_fold_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v_bkt_193_; uint8_t v___x_194_; 
v___x_177_ = lean_array_get_size(v_buckets_173_);
v___x_178_ = lean_ptr_addr(v_a_170_);
v___x_179_ = ((size_t)3ULL);
v___x_180_ = lean_usize_shift_right(v___x_178_, v___x_179_);
v___x_181_ = lean_usize_to_uint64(v___x_180_);
v___x_182_ = 32ULL;
v___x_183_ = lean_uint64_shift_right(v___x_181_, v___x_182_);
v_fold_184_ = lean_uint64_xor(v___x_181_, v___x_183_);
v___x_185_ = 16ULL;
v___x_186_ = lean_uint64_shift_right(v_fold_184_, v___x_185_);
v___x_187_ = lean_uint64_xor(v_fold_184_, v___x_186_);
v___x_188_ = lean_uint64_to_usize(v___x_187_);
v___x_189_ = lean_usize_of_nat(v___x_177_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_sub(v___x_189_, v___x_190_);
v___x_192_ = lean_usize_land(v___x_188_, v___x_191_);
v_bkt_193_ = lean_array_uget_borrowed(v_buckets_173_, v___x_192_);
v___x_194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_170_, v_bkt_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v_size_x27_196_; lean_object* v___x_197_; lean_object* v_buckets_x27_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v_size_x27_196_ = lean_nat_add(v_size_172_, v___x_195_);
lean_dec(v_size_172_);
lean_inc(v_bkt_193_);
v___x_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_197_, 0, v_a_170_);
lean_ctor_set(v___x_197_, 1, v_b_171_);
lean_ctor_set(v___x_197_, 2, v_bkt_193_);
v_buckets_x27_198_ = lean_array_uset(v_buckets_173_, v___x_192_, v___x_197_);
v___x_199_ = lean_unsigned_to_nat(4u);
v___x_200_ = lean_nat_mul(v_size_x27_196_, v___x_199_);
v___x_201_ = lean_unsigned_to_nat(3u);
v___x_202_ = lean_nat_div(v___x_200_, v___x_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_array_get_size(v_buckets_x27_198_);
v___x_204_ = lean_nat_dec_le(v___x_202_, v___x_203_);
lean_dec(v___x_202_);
if (v___x_204_ == 0)
{
lean_object* v_val_205_; lean_object* v___x_207_; 
v_val_205_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_buckets_x27_198_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v_val_205_);
lean_ctor_set(v___x_175_, 0, v_size_x27_196_);
v___x_207_ = v___x_175_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_size_x27_196_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_val_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
else
{
lean_object* v___x_210_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v_buckets_x27_198_);
lean_ctor_set(v___x_175_, 0, v_size_x27_196_);
v___x_210_ = v___x_175_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_size_x27_196_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_buckets_x27_198_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v___x_212_; lean_object* v_buckets_x27_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
lean_inc(v_bkt_193_);
v___x_212_ = lean_box(0);
v_buckets_x27_213_ = lean_array_uset(v_buckets_173_, v___x_192_, v___x_212_);
v___x_214_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_170_, v_b_171_, v_bkt_193_);
v___x_215_ = lean_array_uset(v_buckets_x27_213_, v___x_192_, v___x_214_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_215_);
v___x_217_ = v___x_175_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_size_172_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object* v_e_220_, lean_object* v_e_x27_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_224_ = lean_st_ref_take(v_a_222_);
lean_inc_ref(v_e_x27_221_);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_224_, v_e_220_, v_e_x27_221_);
v___x_226_ = lean_st_ref_put(v_a_222_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v_e_x27_221_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object* v_e_228_, lean_object* v_e_x27_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_228_, v_e_x27_229_, v_a_230_);
lean_dec(v_a_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object* v_e_233_, lean_object* v_e_x27_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_233_, v_e_x27_234_, v_a_235_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object* v_e_240_, lean_object* v_e_x27_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_240_, v_e_x27_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object* v_00_u03b2_247_, lean_object* v_m_248_, lean_object* v_a_249_, lean_object* v_b_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_248_, v_a_249_, v_b_250_);
return v___x_251_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object* v_00_u03b2_252_, lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_256_, lean_object* v_a_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_256_, v_a_257_, v_x_258_);
lean_dec(v_x_258_);
lean_dec_ref(v_a_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(lean_object* v_00_u03b2_261_, lean_object* v_data_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_data_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(lean_object* v_00_u03b2_264_, lean_object* v_a_265_, lean_object* v_b_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_265_, v_b_266_, v_x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_269_, lean_object* v_i_270_, lean_object* v_source_271_, lean_object* v_target_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v_i_270_, v_source_271_, v_target_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_275_, v_x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = l_Lean_maxRecDepthErrorMessage;
v___x_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
v___x_286_ = l_Lean_MessageData_ofFormat(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
v___x_288_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2));
v___x_289_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object* v_ref_290_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_ref_290_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object* v_ref_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object* v_00_u03b1_298_, lean_object* v_ref_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_299_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object* v_00_u03b1_305_, lean_object* v_ref_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_305_, v_ref_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_314_; 
v___x_314_ = lean_box(0);
return v___x_314_;
}
else
{
lean_object* v_key_315_; lean_object* v_value_316_; lean_object* v_tail_317_; size_t v___x_318_; size_t v___x_319_; uint8_t v___x_320_; 
v_key_315_ = lean_ctor_get(v_x_313_, 0);
v_value_316_ = lean_ctor_get(v_x_313_, 1);
v_tail_317_ = lean_ctor_get(v_x_313_, 2);
v___x_318_ = lean_ptr_addr(v_key_315_);
v___x_319_ = lean_ptr_addr(v_a_312_);
v___x_320_ = lean_usize_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
v_x_313_ = v_tail_317_;
goto _start;
}
else
{
lean_object* v___x_322_; 
lean_inc(v_value_316_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v_value_316_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_323_, v_x_324_);
lean_dec(v_x_324_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object* v_m_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_buckets_328_; lean_object* v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v_fold_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_buckets_328_ = lean_ctor_get(v_m_326_, 1);
v___x_329_ = lean_array_get_size(v_buckets_328_);
v___x_330_ = lean_ptr_addr(v_a_327_);
v___x_331_ = ((size_t)3ULL);
v___x_332_ = lean_usize_shift_right(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_to_uint64(v___x_332_);
v___x_334_ = 32ULL;
v___x_335_ = lean_uint64_shift_right(v___x_333_, v___x_334_);
v_fold_336_ = lean_uint64_xor(v___x_333_, v___x_335_);
v___x_337_ = 16ULL;
v___x_338_ = lean_uint64_shift_right(v_fold_336_, v___x_337_);
v___x_339_ = lean_uint64_xor(v_fold_336_, v___x_338_);
v___x_340_ = lean_uint64_to_usize(v___x_339_);
v___x_341_ = lean_usize_of_nat(v___x_329_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v___x_341_, v___x_342_);
v___x_344_ = lean_usize_land(v___x_340_, v___x_343_);
v___x_345_ = lean_array_uget_borrowed(v_buckets_328_, v___x_344_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_327_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_347_, v_a_348_);
lean_dec_ref(v_a_348_);
lean_dec_ref(v_m_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object* v_e_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_toCold_355_; lean_object* v_currRecDepth_356_; lean_object* v_ref_357_; uint16_t v_optionFlags_358_; uint8_t v_suppressElabErrors_359_; uint8_t v_checkDeprecated_360_; uint8_t v_isRecordingDeps_361_; lean_object* v_maxRecDepth_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_toCold_355_ = lean_ctor_get(v_a_352_, 0);
v_currRecDepth_356_ = lean_ctor_get(v_a_352_, 1);
v_ref_357_ = lean_ctor_get(v_a_352_, 2);
v_optionFlags_358_ = lean_ctor_get_uint16(v_a_352_, sizeof(void*)*3);
v_suppressElabErrors_359_ = lean_ctor_get_uint8(v_a_352_, sizeof(void*)*3 + 2);
v_checkDeprecated_360_ = lean_ctor_get_uint8(v_a_352_, sizeof(void*)*3 + 3);
v_isRecordingDeps_361_ = lean_ctor_get_uint8(v_a_352_, sizeof(void*)*3 + 4);
v_maxRecDepth_494_ = lean_ctor_get(v_toCold_355_, 3);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_nat_dec_eq(v_maxRecDepth_494_, v___x_495_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
v___x_497_ = lean_nat_dec_eq(v_currRecDepth_356_, v_maxRecDepth_494_);
if (v___x_497_ == 0)
{
goto v___jp_362_;
}
else
{
lean_object* v___x_498_; 
lean_dec_ref(v_e_350_);
lean_inc(v_ref_357_);
v___x_498_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_357_);
return v___x_498_;
}
}
else
{
goto v___jp_362_;
}
v___jp_362_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_currRecDepth_356_, v___x_363_);
lean_inc(v_ref_357_);
lean_inc_ref(v_toCold_355_);
v___x_365_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_365_, 0, v_toCold_355_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
lean_ctor_set(v___x_365_, 2, v_ref_357_);
lean_ctor_set_uint16(v___x_365_, sizeof(void*)*3, v_optionFlags_358_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 2, v_suppressElabErrors_359_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 3, v_checkDeprecated_360_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 4, v_isRecordingDeps_361_);
v___x_366_ = lean_st_ref_get(v_a_351_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_366_, v_e_350_);
lean_dec(v___x_366_);
if (lean_obj_tag(v___x_367_) == 1)
{
lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref_known(v___x_365_, 3);
lean_dec_ref(v_e_350_);
v_val_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 0);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_val_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_dec(v___x_367_);
switch(lean_obj_tag(v_e_350_))
{
case 7:
{
lean_object* v_binderName_376_; lean_object* v_binderType_377_; lean_object* v_body_378_; uint8_t v_binderInfo_379_; lean_object* v___x_380_; 
v_binderName_376_ = lean_ctor_get(v_e_350_, 0);
v_binderType_377_ = lean_ctor_get(v_e_350_, 1);
v_body_378_ = lean_ctor_get(v_e_350_, 2);
v_binderInfo_379_ = lean_ctor_get_uint8(v_e_350_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_377_);
v___x_380_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_377_, v_a_351_, v___x_365_, v_a_353_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
lean_inc_ref(v_body_378_);
v___x_382_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_378_, v_a_351_, v___x_365_, v_a_353_);
lean_dec_ref_known(v___x_365_, 3);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; size_t v___x_384_; size_t v___x_385_; uint8_t v___x_386_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = lean_ptr_addr(v_binderType_377_);
v___x_385_ = lean_ptr_addr(v_a_381_);
v___x_386_ = lean_usize_dec_eq(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_inc(v_binderName_376_);
v___x_387_ = l_Lean_Expr_forallE___override(v_binderName_376_, v_a_381_, v_a_383_, v_binderInfo_379_);
v___x_388_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_387_, v_a_351_);
return v___x_388_;
}
else
{
size_t v___x_389_; size_t v___x_390_; uint8_t v___x_391_; 
v___x_389_ = lean_ptr_addr(v_body_378_);
v___x_390_ = lean_ptr_addr(v_a_383_);
v___x_391_ = lean_usize_dec_eq(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_inc(v_binderName_376_);
v___x_392_ = l_Lean_Expr_forallE___override(v_binderName_376_, v_a_381_, v_a_383_, v_binderInfo_379_);
v___x_393_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_392_, v_a_351_);
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_379_, v_binderInfo_379_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_inc(v_binderName_376_);
v___x_395_ = l_Lean_Expr_forallE___override(v_binderName_376_, v_a_381_, v_a_383_, v_binderInfo_379_);
v___x_396_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_395_, v_a_351_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; 
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_inc_ref(v_e_350_);
v___x_397_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v_e_350_, v_a_351_);
return v___x_397_;
}
}
}
}
else
{
lean_dec(v_a_381_);
lean_dec_ref_known(v_e_350_, 3);
return v___x_382_;
}
}
else
{
lean_dec_ref_known(v_e_350_, 3);
lean_dec_ref_known(v___x_365_, 3);
return v___x_380_;
}
}
case 6:
{
lean_object* v_binderName_398_; lean_object* v_binderType_399_; lean_object* v_body_400_; uint8_t v_binderInfo_401_; lean_object* v___x_402_; lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; uint8_t v___x_406_; 
v_binderName_398_ = lean_ctor_get(v_e_350_, 0);
v_binderType_399_ = lean_ctor_get(v_e_350_, 1);
v_body_400_ = lean_ctor_get(v_e_350_, 2);
v_binderInfo_401_ = lean_ctor_get_uint8(v_e_350_, sizeof(void*)*3 + 8);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_350_, v_e_350_, v___x_402_);
v___x_404_ = lean_ptr_addr(v_e_350_);
v___x_405_ = lean_ptr_addr(v___x_403_);
v___x_406_ = lean_usize_dec_eq(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_403_, v_a_351_, v___x_365_, v_a_353_);
lean_dec_ref_known(v___x_365_, 3);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v_a_408_, v_a_351_);
return v___x_409_;
}
else
{
lean_dec_ref_known(v_e_350_, 3);
return v___x_407_;
}
}
else
{
lean_object* v___x_410_; 
lean_dec_ref(v___x_403_);
lean_inc_ref(v_binderType_399_);
v___x_410_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_399_, v_a_351_, v___x_365_, v_a_353_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_412_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
lean_inc_ref(v_body_400_);
v___x_412_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_400_, v_a_351_, v___x_365_, v_a_353_);
lean_dec_ref_known(v___x_365_, 3);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = lean_ptr_addr(v_binderType_399_);
v___x_415_ = lean_ptr_addr(v_a_411_);
v___x_416_ = lean_usize_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_inc(v_binderName_398_);
v___x_417_ = l_Lean_Expr_lam___override(v_binderName_398_, v_a_411_, v_a_413_, v_binderInfo_401_);
v___x_418_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_417_, v_a_351_);
return v___x_418_;
}
else
{
size_t v___x_419_; size_t v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_ptr_addr(v_body_400_);
v___x_420_ = lean_ptr_addr(v_a_413_);
v___x_421_ = lean_usize_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_inc(v_binderName_398_);
v___x_422_ = l_Lean_Expr_lam___override(v_binderName_398_, v_a_411_, v_a_413_, v_binderInfo_401_);
v___x_423_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_422_, v_a_351_);
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_401_, v_binderInfo_401_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_inc(v_binderName_398_);
v___x_425_ = l_Lean_Expr_lam___override(v_binderName_398_, v_a_411_, v_a_413_, v_binderInfo_401_);
v___x_426_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_425_, v_a_351_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_dec(v_a_413_);
lean_dec(v_a_411_);
lean_inc_ref(v_e_350_);
v___x_427_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v_e_350_, v_a_351_);
return v___x_427_;
}
}
}
}
else
{
lean_dec(v_a_411_);
lean_dec_ref_known(v_e_350_, 3);
return v___x_412_;
}
}
else
{
lean_dec_ref_known(v_e_350_, 3);
lean_dec_ref_known(v___x_365_, 3);
return v___x_410_;
}
}
}
case 8:
{
lean_object* v_declName_428_; lean_object* v_type_429_; lean_object* v_value_430_; lean_object* v_body_431_; uint8_t v_nondep_432_; lean_object* v___x_433_; 
v_declName_428_ = lean_ctor_get(v_e_350_, 0);
v_type_429_ = lean_ctor_get(v_e_350_, 1);
v_value_430_ = lean_ctor_get(v_e_350_, 2);
v_body_431_ = lean_ctor_get(v_e_350_, 3);
v_nondep_432_ = lean_ctor_get_uint8(v_e_350_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_429_);
v___x_433_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_429_, v_a_351_, v___x_365_, v_a_353_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
lean_inc_ref(v_value_430_);
v___x_435_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_430_, v_a_351_, v___x_365_, v_a_353_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
lean_inc_ref(v_body_431_);
v___x_437_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_431_, v_a_351_, v___x_365_, v_a_353_);
lean_dec_ref_known(v___x_365_, 3);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; size_t v___x_439_; size_t v___x_440_; uint8_t v___x_441_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_ptr_addr(v_type_429_);
v___x_440_ = lean_ptr_addr(v_a_434_);
v___x_441_ = lean_usize_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_inc(v_declName_428_);
v___x_442_ = l_Lean_Expr_letE___override(v_declName_428_, v_a_434_, v_a_436_, v_a_438_, v_nondep_432_);
v___x_443_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_442_, v_a_351_);
return v___x_443_;
}
else
{
size_t v___x_444_; size_t v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_ptr_addr(v_value_430_);
v___x_445_ = lean_ptr_addr(v_a_436_);
v___x_446_ = lean_usize_dec_eq(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_inc(v_declName_428_);
v___x_447_ = l_Lean_Expr_letE___override(v_declName_428_, v_a_434_, v_a_436_, v_a_438_, v_nondep_432_);
v___x_448_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_447_, v_a_351_);
return v___x_448_;
}
else
{
size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v_body_431_);
v___x_450_ = lean_ptr_addr(v_a_438_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_inc(v_declName_428_);
v___x_452_ = l_Lean_Expr_letE___override(v_declName_428_, v_a_434_, v_a_436_, v_a_438_, v_nondep_432_);
v___x_453_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_452_, v_a_351_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
lean_dec(v_a_438_);
lean_dec(v_a_436_);
lean_dec(v_a_434_);
lean_inc_ref(v_e_350_);
v___x_454_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v_e_350_, v_a_351_);
return v___x_454_;
}
}
}
}
else
{
lean_dec(v_a_436_);
lean_dec(v_a_434_);
lean_dec_ref_known(v_e_350_, 4);
return v___x_437_;
}
}
else
{
lean_dec(v_a_434_);
lean_dec_ref_known(v_e_350_, 4);
lean_dec_ref_known(v___x_365_, 3);
return v___x_435_;
}
}
else
{
lean_dec_ref_known(v_e_350_, 4);
lean_dec_ref_known(v___x_365_, 3);
return v___x_433_;
}
}
case 5:
{
lean_object* v_fn_455_; lean_object* v_arg_456_; lean_object* v___x_457_; 
v_fn_455_ = lean_ctor_get(v_e_350_, 0);
v_arg_456_ = lean_ctor_get(v_e_350_, 1);
lean_inc_ref(v_fn_455_);
v___x_457_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_455_, v_a_351_, v___x_365_, v_a_353_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
lean_inc_ref(v_arg_456_);
v___x_459_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_456_, v_a_351_, v___x_365_, v_a_353_);
lean_dec_ref_known(v___x_365_, 3);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; size_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = lean_ptr_addr(v_fn_455_);
v___x_462_ = lean_ptr_addr(v_a_458_);
v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = l_Lean_Expr_app___override(v_a_458_, v_a_460_);
v___x_465_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_464_, v_a_351_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_ptr_addr(v_arg_456_);
v___x_467_ = lean_ptr_addr(v_a_460_);
v___x_468_ = lean_usize_dec_eq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = l_Lean_Expr_app___override(v_a_458_, v_a_460_);
v___x_470_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_469_, v_a_351_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; 
lean_dec(v_a_460_);
lean_dec(v_a_458_);
lean_inc_ref(v_e_350_);
v___x_471_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v_e_350_, v_a_351_);
return v___x_471_;
}
}
}
else
{
lean_dec(v_a_458_);
lean_dec_ref_known(v_e_350_, 2);
return v___x_459_;
}
}
else
{
lean_dec_ref_known(v_e_350_, 2);
lean_dec_ref_known(v___x_365_, 3);
return v___x_457_;
}
}
case 10:
{
lean_object* v_data_472_; lean_object* v_expr_473_; lean_object* v___x_474_; 
v_data_472_ = lean_ctor_get(v_e_350_, 0);
v_expr_473_ = lean_ctor_get(v_e_350_, 1);
lean_inc_ref(v_expr_473_);
v___x_474_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_473_, v_a_351_, v___x_365_, v_a_353_);
lean_dec_ref_known(v___x_365_, 3);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; size_t v___x_476_; size_t v___x_477_; uint8_t v___x_478_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = lean_ptr_addr(v_expr_473_);
v___x_477_ = lean_ptr_addr(v_a_475_);
v___x_478_ = lean_usize_dec_eq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_inc(v_data_472_);
v___x_479_ = l_Lean_Expr_mdata___override(v_data_472_, v_a_475_);
v___x_480_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_479_, v_a_351_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
lean_dec(v_a_475_);
lean_inc_ref(v_e_350_);
v___x_481_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v_e_350_, v_a_351_);
return v___x_481_;
}
}
else
{
lean_dec_ref_known(v_e_350_, 2);
return v___x_474_;
}
}
case 11:
{
lean_object* v_typeName_482_; lean_object* v_idx_483_; lean_object* v_struct_484_; lean_object* v___x_485_; 
v_typeName_482_ = lean_ctor_get(v_e_350_, 0);
v_idx_483_ = lean_ctor_get(v_e_350_, 1);
v_struct_484_ = lean_ctor_get(v_e_350_, 2);
lean_inc_ref(v_struct_484_);
v___x_485_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_484_, v_a_351_, v___x_365_, v_a_353_);
lean_dec_ref_known(v___x_365_, 3);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; size_t v___x_487_; size_t v___x_488_; uint8_t v___x_489_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = lean_ptr_addr(v_struct_484_);
v___x_488_ = lean_ptr_addr(v_a_486_);
v___x_489_ = lean_usize_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc(v_idx_483_);
lean_inc(v_typeName_482_);
v___x_490_ = l_Lean_Expr_proj___override(v_typeName_482_, v_idx_483_, v_a_486_);
v___x_491_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v___x_490_, v_a_351_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_a_486_);
lean_inc_ref(v_e_350_);
v___x_492_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_350_, v_e_350_, v_a_351_);
return v___x_492_;
}
}
else
{
lean_dec_ref_known(v_e_350_, 3);
return v___x_485_;
}
}
default: 
{
lean_object* v___x_493_; 
lean_dec_ref_known(v___x_365_, 3);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_e_350_);
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object* v_e_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object* v_00_u03b2_505_, lean_object* v_m_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_506_, v_a_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_509_, v_m_510_, v_a_511_);
lean_dec_ref(v_a_511_);
lean_dec_ref(v_m_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object* v_00_u03b2_513_, lean_object* v_a_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_517_, v_a_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec_ref(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object* v_e_521_, lean_object* v_c_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_st_mk_ref(v_c_522_);
v___x_527_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_521_, v___x_526_, v_a_523_, v_a_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_537_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_537_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = lean_st_ref_get(v___x_526_);
lean_dec(v___x_526_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_a_528_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v___x_526_);
v_a_538_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_527_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_527_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object* v_e_546_, lean_object* v_c_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_546_, v_c_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
return v_res_551_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__1(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_box(0);
v___x_554_ = lean_unsigned_to_nat(16u);
v___x_555_ = lean_mk_array(v___x_554_, v___x_553_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__2(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__1, &l_Lean_Meta_Sym_etaReduceAll___closed__1_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__1);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object* v_e_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Meta_Sym_etaReduceAll___closed__0));
v___x_564_ = lean_find_expr(v___x_563_, v_e_559_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_e_559_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__2, &l_Lean_Meta_Sym_etaReduceAll___closed__2_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__2);
v___x_567_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_559_, v___x_566_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_fst_572_; lean_object* v___x_574_; 
v_fst_572_ = lean_ctor_get(v_a_568_, 0);
lean_inc(v_fst_572_);
lean_dec(v_a_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_fst_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_fst_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_567_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_567_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object* v_e_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_Sym_etaReduceAll(v_e_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
return v_res_589_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Eta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Eta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Eta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Eta(builtin);
}
#ifdef __cplusplus
}
#endif
