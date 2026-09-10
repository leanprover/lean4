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
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_nbuckets_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_148_ = lean_array_get_size(v_data_147_);
v___x_149_ = lean_unsigned_to_nat(2u);
v_nbuckets_150_ = lean_nat_mul(v___x_148_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_box(0);
v___x_153_ = lean_mk_array(v_nbuckets_150_, v___x_152_);
v___x_154_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v___x_151_, v_data_147_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
else
{
lean_object* v_key_158_; lean_object* v_tail_159_; size_t v___x_160_; size_t v___x_161_; uint8_t v___x_162_; 
v_key_158_ = lean_ctor_get(v_x_156_, 0);
v_tail_159_ = lean_ctor_get(v_x_156_, 2);
v___x_160_ = lean_ptr_addr(v_key_158_);
v___x_161_ = lean_ptr_addr(v_a_155_);
v___x_162_ = lean_usize_dec_eq(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
v_x_156_ = v_tail_159_;
goto _start;
}
else
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_164_, lean_object* v_x_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_164_, v_x_165_);
lean_dec(v_x_165_);
lean_dec_ref(v_a_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object* v_m_168_, lean_object* v_a_169_, lean_object* v_b_170_){
_start:
{
lean_object* v_size_171_; lean_object* v_buckets_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_218_; 
v_size_171_ = lean_ctor_get(v_m_168_, 0);
v_buckets_172_ = lean_ctor_get(v_m_168_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_m_168_);
if (v_isSharedCheck_218_ == 0)
{
v___x_174_ = v_m_168_;
v_isShared_175_ = v_isSharedCheck_218_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_buckets_172_);
lean_inc(v_size_171_);
lean_dec(v_m_168_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_218_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v_fold_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v_bkt_192_; uint8_t v___x_193_; 
v___x_176_ = lean_array_get_size(v_buckets_172_);
v___x_177_ = lean_ptr_addr(v_a_169_);
v___x_178_ = ((size_t)3ULL);
v___x_179_ = lean_usize_shift_right(v___x_177_, v___x_178_);
v___x_180_ = lean_usize_to_uint64(v___x_179_);
v___x_181_ = 32ULL;
v___x_182_ = lean_uint64_shift_right(v___x_180_, v___x_181_);
v_fold_183_ = lean_uint64_xor(v___x_180_, v___x_182_);
v___x_184_ = 16ULL;
v___x_185_ = lean_uint64_shift_right(v_fold_183_, v___x_184_);
v___x_186_ = lean_uint64_xor(v_fold_183_, v___x_185_);
v___x_187_ = lean_uint64_to_usize(v___x_186_);
v___x_188_ = lean_usize_of_nat(v___x_176_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_sub(v___x_188_, v___x_189_);
v___x_191_ = lean_usize_land(v___x_187_, v___x_190_);
v_bkt_192_ = lean_array_uget_borrowed(v_buckets_172_, v___x_191_);
v___x_193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_169_, v_bkt_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v_size_x27_195_; lean_object* v___x_196_; lean_object* v_buckets_x27_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v_size_x27_195_ = lean_nat_add(v_size_171_, v___x_194_);
lean_dec(v_size_171_);
lean_inc(v_bkt_192_);
v___x_196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_196_, 0, v_a_169_);
lean_ctor_set(v___x_196_, 1, v_b_170_);
lean_ctor_set(v___x_196_, 2, v_bkt_192_);
v_buckets_x27_197_ = lean_array_uset(v_buckets_172_, v___x_191_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(4u);
v___x_199_ = lean_nat_mul(v_size_x27_195_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(3u);
v___x_201_ = lean_nat_div(v___x_199_, v___x_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_array_get_size(v_buckets_x27_197_);
v___x_203_ = lean_nat_dec_le(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
if (v___x_203_ == 0)
{
lean_object* v_val_204_; lean_object* v___x_206_; 
v_val_204_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_buckets_x27_197_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v_val_204_);
lean_ctor_set(v___x_174_, 0, v_size_x27_195_);
v___x_206_ = v___x_174_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_size_x27_195_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_val_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
else
{
lean_object* v___x_209_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v_buckets_x27_197_);
lean_ctor_set(v___x_174_, 0, v_size_x27_195_);
v___x_209_ = v___x_174_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_size_x27_195_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_buckets_x27_197_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v___x_211_; lean_object* v_buckets_x27_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
lean_inc(v_bkt_192_);
v___x_211_ = lean_box(0);
v_buckets_x27_212_ = lean_array_uset(v_buckets_172_, v___x_191_, v___x_211_);
v___x_213_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_169_, v_b_170_, v_bkt_192_);
v___x_214_ = lean_array_uset(v_buckets_x27_212_, v___x_191_, v___x_213_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_214_);
v___x_216_ = v___x_174_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_size_171_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object* v_e_219_, lean_object* v_e_x27_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_st_ref_take(v_a_221_);
lean_inc_ref(v_e_x27_220_);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_223_, v_e_219_, v_e_x27_220_);
v___x_225_ = lean_st_ref_put(v_a_221_, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_e_x27_220_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object* v_e_227_, lean_object* v_e_x27_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_227_, v_e_x27_228_, v_a_229_);
lean_dec(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object* v_e_232_, lean_object* v_e_x27_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_232_, v_e_x27_233_, v_a_234_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object* v_e_239_, lean_object* v_e_x27_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_239_, v_e_x27_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object* v_00_u03b2_246_, lean_object* v_m_247_, lean_object* v_a_248_, lean_object* v_b_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_247_, v_a_248_, v_b_249_);
return v___x_250_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object* v_00_u03b2_251_, lean_object* v_a_252_, lean_object* v_x_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_252_, v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_255_, v_a_256_, v_x_257_);
lean_dec(v_x_257_);
lean_dec_ref(v_a_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(lean_object* v_00_u03b2_260_, lean_object* v_data_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_data_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(lean_object* v_00_u03b2_263_, lean_object* v_a_264_, lean_object* v_b_265_, lean_object* v_x_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_264_, v_b_265_, v_x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_268_, lean_object* v_i_269_, lean_object* v_source_270_, lean_object* v_target_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v_i_269_, v_source_270_, v_target_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_274_, v_x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = l_Lean_maxRecDepthErrorMessage;
v___x_283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
v___x_285_ = l_Lean_MessageData_ofFormat(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
v___x_287_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2));
v___x_288_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object* v_ref_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_ref_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object* v_ref_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object* v_00_u03b1_297_, lean_object* v_ref_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_298_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object* v_00_u03b1_304_, lean_object* v_ref_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_304_, v_ref_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object* v_a_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v_key_314_; lean_object* v_value_315_; lean_object* v_tail_316_; size_t v___x_317_; size_t v___x_318_; uint8_t v___x_319_; 
v_key_314_ = lean_ctor_get(v_x_312_, 0);
v_value_315_ = lean_ctor_get(v_x_312_, 1);
v_tail_316_ = lean_ctor_get(v_x_312_, 2);
v___x_317_ = lean_ptr_addr(v_key_314_);
v___x_318_ = lean_ptr_addr(v_a_311_);
v___x_319_ = lean_usize_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
v_x_312_ = v_tail_316_;
goto _start;
}
else
{
lean_object* v___x_321_; 
lean_inc(v_value_315_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v_value_315_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object* v_m_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_buckets_327_; lean_object* v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v_fold_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_buckets_327_ = lean_ctor_get(v_m_325_, 1);
v___x_328_ = lean_array_get_size(v_buckets_327_);
v___x_329_ = lean_ptr_addr(v_a_326_);
v___x_330_ = ((size_t)3ULL);
v___x_331_ = lean_usize_shift_right(v___x_329_, v___x_330_);
v___x_332_ = lean_usize_to_uint64(v___x_331_);
v___x_333_ = 32ULL;
v___x_334_ = lean_uint64_shift_right(v___x_332_, v___x_333_);
v_fold_335_ = lean_uint64_xor(v___x_332_, v___x_334_);
v___x_336_ = 16ULL;
v___x_337_ = lean_uint64_shift_right(v_fold_335_, v___x_336_);
v___x_338_ = lean_uint64_xor(v_fold_335_, v___x_337_);
v___x_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = lean_usize_of_nat(v___x_328_);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_sub(v___x_340_, v___x_341_);
v___x_343_ = lean_usize_land(v___x_339_, v___x_342_);
v___x_344_ = lean_array_uget_borrowed(v_buckets_327_, v___x_343_);
v___x_345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_326_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object* v_m_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_346_, v_a_347_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_m_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_toCold_354_; lean_object* v_currRecDepth_355_; lean_object* v_ref_356_; uint8_t v_diag_357_; uint8_t v_suppressElabErrors_358_; lean_object* v_maxRecDepth_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_toCold_354_ = lean_ctor_get(v_a_351_, 0);
v_currRecDepth_355_ = lean_ctor_get(v_a_351_, 1);
v_ref_356_ = lean_ctor_get(v_a_351_, 2);
v_diag_357_ = lean_ctor_get_uint8(v_a_351_, sizeof(void*)*3);
v_suppressElabErrors_358_ = lean_ctor_get_uint8(v_a_351_, sizeof(void*)*3 + 1);
v_maxRecDepth_491_ = lean_ctor_get(v_toCold_354_, 3);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_nat_dec_eq(v_maxRecDepth_491_, v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_eq(v_currRecDepth_355_, v_maxRecDepth_491_);
if (v___x_494_ == 0)
{
goto v___jp_359_;
}
else
{
lean_object* v___x_495_; 
lean_dec_ref(v_e_349_);
lean_inc(v_ref_356_);
v___x_495_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_356_);
return v___x_495_;
}
}
else
{
goto v___jp_359_;
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_st_ref_get(v_a_350_);
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_360_, v_e_349_);
lean_dec(v___x_360_);
if (lean_obj_tag(v___x_361_) == 1)
{
lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v_e_349_);
v_val_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 0);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_val_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___x_361_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_currRecDepth_355_, v___x_370_);
lean_inc(v_ref_356_);
lean_inc_ref(v_toCold_354_);
v___x_372_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_372_, 0, v_toCold_354_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
lean_ctor_set(v___x_372_, 2, v_ref_356_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*3, v_diag_357_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*3 + 1, v_suppressElabErrors_358_);
switch(lean_obj_tag(v_e_349_))
{
case 7:
{
lean_object* v_binderName_373_; lean_object* v_binderType_374_; lean_object* v_body_375_; uint8_t v_binderInfo_376_; lean_object* v___x_377_; 
v_binderName_373_ = lean_ctor_get(v_e_349_, 0);
v_binderType_374_ = lean_ctor_get(v_e_349_, 1);
v_body_375_ = lean_ctor_get(v_e_349_, 2);
v_binderInfo_376_ = lean_ctor_get_uint8(v_e_349_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_374_);
v___x_377_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_374_, v_a_350_, v___x_372_, v_a_352_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v___x_377_, 1);
lean_inc_ref(v_body_375_);
v___x_379_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_375_, v_a_350_, v___x_372_, v_a_352_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; size_t v___x_381_; size_t v___x_382_; uint8_t v___x_383_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = lean_ptr_addr(v_binderType_374_);
v___x_382_ = lean_ptr_addr(v_a_378_);
v___x_383_ = lean_usize_dec_eq(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_inc(v_binderName_373_);
v___x_384_ = l_Lean_Expr_forallE___override(v_binderName_373_, v_a_378_, v_a_380_, v_binderInfo_376_);
v___x_385_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_384_, v_a_350_);
return v___x_385_;
}
else
{
size_t v___x_386_; size_t v___x_387_; uint8_t v___x_388_; 
v___x_386_ = lean_ptr_addr(v_body_375_);
v___x_387_ = lean_ptr_addr(v_a_380_);
v___x_388_ = lean_usize_dec_eq(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_inc(v_binderName_373_);
v___x_389_ = l_Lean_Expr_forallE___override(v_binderName_373_, v_a_378_, v_a_380_, v_binderInfo_376_);
v___x_390_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_389_, v_a_350_);
return v___x_390_;
}
else
{
uint8_t v___x_391_; 
v___x_391_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_376_, v_binderInfo_376_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_inc(v_binderName_373_);
v___x_392_ = l_Lean_Expr_forallE___override(v_binderName_373_, v_a_378_, v_a_380_, v_binderInfo_376_);
v___x_393_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_392_, v_a_350_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; 
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_inc_ref(v_e_349_);
v___x_394_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v_e_349_, v_a_350_);
return v___x_394_;
}
}
}
}
else
{
lean_dec(v_a_378_);
lean_dec_ref_known(v_e_349_, 3);
return v___x_379_;
}
}
else
{
lean_dec_ref_known(v_e_349_, 3);
lean_dec_ref_known(v___x_372_, 3);
return v___x_377_;
}
}
case 6:
{
lean_object* v_binderName_395_; lean_object* v_binderType_396_; lean_object* v_body_397_; uint8_t v_binderInfo_398_; lean_object* v___x_399_; lean_object* v___x_400_; size_t v___x_401_; size_t v___x_402_; uint8_t v___x_403_; 
v_binderName_395_ = lean_ctor_get(v_e_349_, 0);
v_binderType_396_ = lean_ctor_get(v_e_349_, 1);
v_body_397_ = lean_ctor_get(v_e_349_, 2);
v_binderInfo_398_ = lean_ctor_get_uint8(v_e_349_, sizeof(void*)*3 + 8);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_349_, v_e_349_, v___x_399_);
v___x_401_ = lean_ptr_addr(v_e_349_);
v___x_402_ = lean_ptr_addr(v___x_400_);
v___x_403_ = lean_usize_dec_eq(v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_400_, v_a_350_, v___x_372_, v_a_352_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
v___x_406_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v_a_405_, v_a_350_);
return v___x_406_;
}
else
{
lean_dec_ref_known(v_e_349_, 3);
return v___x_404_;
}
}
else
{
lean_object* v___x_407_; 
lean_dec_ref(v___x_400_);
lean_inc_ref(v_binderType_396_);
v___x_407_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_396_, v_a_350_, v___x_372_, v_a_352_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
lean_inc_ref(v_body_397_);
v___x_409_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_397_, v_a_350_, v___x_372_, v_a_352_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; size_t v___x_411_; size_t v___x_412_; uint8_t v___x_413_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = lean_ptr_addr(v_binderType_396_);
v___x_412_ = lean_ptr_addr(v_a_408_);
v___x_413_ = lean_usize_dec_eq(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_inc(v_binderName_395_);
v___x_414_ = l_Lean_Expr_lam___override(v_binderName_395_, v_a_408_, v_a_410_, v_binderInfo_398_);
v___x_415_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_414_, v_a_350_);
return v___x_415_;
}
else
{
size_t v___x_416_; size_t v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_ptr_addr(v_body_397_);
v___x_417_ = lean_ptr_addr(v_a_410_);
v___x_418_ = lean_usize_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc(v_binderName_395_);
v___x_419_ = l_Lean_Expr_lam___override(v_binderName_395_, v_a_408_, v_a_410_, v_binderInfo_398_);
v___x_420_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_419_, v_a_350_);
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_398_, v_binderInfo_398_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_inc(v_binderName_395_);
v___x_422_ = l_Lean_Expr_lam___override(v_binderName_395_, v_a_408_, v_a_410_, v_binderInfo_398_);
v___x_423_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_422_, v_a_350_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
lean_dec(v_a_410_);
lean_dec(v_a_408_);
lean_inc_ref(v_e_349_);
v___x_424_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v_e_349_, v_a_350_);
return v___x_424_;
}
}
}
}
else
{
lean_dec(v_a_408_);
lean_dec_ref_known(v_e_349_, 3);
return v___x_409_;
}
}
else
{
lean_dec_ref_known(v_e_349_, 3);
lean_dec_ref_known(v___x_372_, 3);
return v___x_407_;
}
}
}
case 8:
{
lean_object* v_declName_425_; lean_object* v_type_426_; lean_object* v_value_427_; lean_object* v_body_428_; uint8_t v_nondep_429_; lean_object* v___x_430_; 
v_declName_425_ = lean_ctor_get(v_e_349_, 0);
v_type_426_ = lean_ctor_get(v_e_349_, 1);
v_value_427_ = lean_ctor_get(v_e_349_, 2);
v_body_428_ = lean_ctor_get(v_e_349_, 3);
v_nondep_429_ = lean_ctor_get_uint8(v_e_349_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_426_);
v___x_430_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_426_, v_a_350_, v___x_372_, v_a_352_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
lean_inc_ref(v_value_427_);
v___x_432_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_427_, v_a_350_, v___x_372_, v_a_352_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
lean_inc_ref(v_body_428_);
v___x_434_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_428_, v_a_350_, v___x_372_, v_a_352_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; size_t v___x_436_; size_t v___x_437_; uint8_t v___x_438_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = lean_ptr_addr(v_type_426_);
v___x_437_ = lean_ptr_addr(v_a_431_);
v___x_438_ = lean_usize_dec_eq(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_inc(v_declName_425_);
v___x_439_ = l_Lean_Expr_letE___override(v_declName_425_, v_a_431_, v_a_433_, v_a_435_, v_nondep_429_);
v___x_440_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_439_, v_a_350_);
return v___x_440_;
}
else
{
size_t v___x_441_; size_t v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_ptr_addr(v_value_427_);
v___x_442_ = lean_ptr_addr(v_a_433_);
v___x_443_ = lean_usize_dec_eq(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_inc(v_declName_425_);
v___x_444_ = l_Lean_Expr_letE___override(v_declName_425_, v_a_431_, v_a_433_, v_a_435_, v_nondep_429_);
v___x_445_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_444_, v_a_350_);
return v___x_445_;
}
else
{
size_t v___x_446_; size_t v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_ptr_addr(v_body_428_);
v___x_447_ = lean_ptr_addr(v_a_435_);
v___x_448_ = lean_usize_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc(v_declName_425_);
v___x_449_ = l_Lean_Expr_letE___override(v_declName_425_, v_a_431_, v_a_433_, v_a_435_, v_nondep_429_);
v___x_450_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_449_, v_a_350_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; 
lean_dec(v_a_435_);
lean_dec(v_a_433_);
lean_dec(v_a_431_);
lean_inc_ref(v_e_349_);
v___x_451_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v_e_349_, v_a_350_);
return v___x_451_;
}
}
}
}
else
{
lean_dec(v_a_433_);
lean_dec(v_a_431_);
lean_dec_ref_known(v_e_349_, 4);
return v___x_434_;
}
}
else
{
lean_dec(v_a_431_);
lean_dec_ref_known(v_e_349_, 4);
lean_dec_ref_known(v___x_372_, 3);
return v___x_432_;
}
}
else
{
lean_dec_ref_known(v_e_349_, 4);
lean_dec_ref_known(v___x_372_, 3);
return v___x_430_;
}
}
case 5:
{
lean_object* v_fn_452_; lean_object* v_arg_453_; lean_object* v___x_454_; 
v_fn_452_ = lean_ctor_get(v_e_349_, 0);
v_arg_453_ = lean_ctor_get(v_e_349_, 1);
lean_inc_ref(v_fn_452_);
v___x_454_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_452_, v_a_350_, v___x_372_, v_a_352_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
lean_inc_ref(v_arg_453_);
v___x_456_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_453_, v_a_350_, v___x_372_, v_a_352_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; size_t v___x_458_; size_t v___x_459_; uint8_t v___x_460_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = lean_ptr_addr(v_fn_452_);
v___x_459_ = lean_ptr_addr(v_a_455_);
v___x_460_ = lean_usize_dec_eq(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = l_Lean_Expr_app___override(v_a_455_, v_a_457_);
v___x_462_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_461_, v_a_350_);
return v___x_462_;
}
else
{
size_t v___x_463_; size_t v___x_464_; uint8_t v___x_465_; 
v___x_463_ = lean_ptr_addr(v_arg_453_);
v___x_464_ = lean_ptr_addr(v_a_457_);
v___x_465_ = lean_usize_dec_eq(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = l_Lean_Expr_app___override(v_a_455_, v_a_457_);
v___x_467_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_466_, v_a_350_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
lean_dec(v_a_457_);
lean_dec(v_a_455_);
lean_inc_ref(v_e_349_);
v___x_468_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v_e_349_, v_a_350_);
return v___x_468_;
}
}
}
else
{
lean_dec(v_a_455_);
lean_dec_ref_known(v_e_349_, 2);
return v___x_456_;
}
}
else
{
lean_dec_ref_known(v_e_349_, 2);
lean_dec_ref_known(v___x_372_, 3);
return v___x_454_;
}
}
case 10:
{
lean_object* v_data_469_; lean_object* v_expr_470_; lean_object* v___x_471_; 
v_data_469_ = lean_ctor_get(v_e_349_, 0);
v_expr_470_ = lean_ctor_get(v_e_349_, 1);
lean_inc_ref(v_expr_470_);
v___x_471_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_470_, v_a_350_, v___x_372_, v_a_352_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; size_t v___x_473_; size_t v___x_474_; uint8_t v___x_475_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = lean_ptr_addr(v_expr_470_);
v___x_474_ = lean_ptr_addr(v_a_472_);
v___x_475_ = lean_usize_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_inc(v_data_469_);
v___x_476_ = l_Lean_Expr_mdata___override(v_data_469_, v_a_472_);
v___x_477_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_476_, v_a_350_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; 
lean_dec(v_a_472_);
lean_inc_ref(v_e_349_);
v___x_478_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v_e_349_, v_a_350_);
return v___x_478_;
}
}
else
{
lean_dec_ref_known(v_e_349_, 2);
return v___x_471_;
}
}
case 11:
{
lean_object* v_typeName_479_; lean_object* v_idx_480_; lean_object* v_struct_481_; lean_object* v___x_482_; 
v_typeName_479_ = lean_ctor_get(v_e_349_, 0);
v_idx_480_ = lean_ctor_get(v_e_349_, 1);
v_struct_481_ = lean_ctor_get(v_e_349_, 2);
lean_inc_ref(v_struct_481_);
v___x_482_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_481_, v_a_350_, v___x_372_, v_a_352_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_ptr_addr(v_struct_481_);
v___x_485_ = lean_ptr_addr(v_a_483_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_idx_480_);
lean_inc(v_typeName_479_);
v___x_487_ = l_Lean_Expr_proj___override(v_typeName_479_, v_idx_480_, v_a_483_);
v___x_488_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v___x_487_, v_a_350_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
lean_dec(v_a_483_);
lean_inc_ref(v_e_349_);
v___x_489_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_349_, v_e_349_, v_a_350_);
return v___x_489_;
}
}
else
{
lean_dec_ref_known(v_e_349_, 3);
return v___x_482_;
}
}
default: 
{
lean_object* v___x_490_; 
lean_dec_ref_known(v___x_372_, 3);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_e_349_);
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object* v_e_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object* v_00_u03b2_502_, lean_object* v_m_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_503_, v_a_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_506_, v_m_507_, v_a_508_);
lean_dec_ref(v_a_508_);
lean_dec_ref(v_m_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object* v_00_u03b2_510_, lean_object* v_a_511_, lean_object* v_x_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_511_, v_x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_514_, lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_514_, v_a_515_, v_x_516_);
lean_dec(v_x_516_);
lean_dec_ref(v_a_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object* v_e_518_, lean_object* v_c_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_st_mk_ref(v_c_519_);
v___x_524_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_518_, v___x_523_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_534_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_534_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_529_ = lean_st_ref_get(v___x_523_);
lean_dec(v___x_523_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_525_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_530_);
v___x_532_ = v___x_527_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v___x_523_);
v_a_535_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_524_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_524_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object* v_e_543_, lean_object* v_c_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_543_, v_c_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
return v_res_548_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__1(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
v___x_551_ = lean_unsigned_to_nat(16u);
v___x_552_ = lean_mk_array(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__2(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__1, &l_Lean_Meta_Sym_etaReduceAll___closed__1_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__1);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_Meta_Sym_etaReduceAll___closed__0));
v___x_561_ = lean_find_expr(v___x_560_, v_e_556_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_e_556_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__2, &l_Lean_Meta_Sym_etaReduceAll___closed__2_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__2);
v___x_564_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_556_, v___x_563_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_fst_569_; lean_object* v___x_571_; 
v_fst_569_ = lean_ctor_get(v_a_565_, 0);
lean_inc(v_fst_569_);
lean_dec(v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_fst_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_a_574_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_564_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object* v_e_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_Sym_etaReduceAll(v_e_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
return v_res_586_;
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
