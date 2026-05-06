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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = l_Lean_Meta_Sym_etaReduce(v_e_74_);
v___x_76_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_74_, v___x_75_);
lean_dec_ref(v___x_75_);
if (v___x_76_ == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isEtaReducible___boxed(lean_object* v_e_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Meta_Sym_isEtaReducible(v_e_79_);
lean_dec_ref(v_e_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(lean_object* v_a_82_, lean_object* v_b_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_dec(v_b_83_);
lean_dec_ref(v_a_82_);
return v_x_84_;
}
else
{
lean_object* v_key_85_; lean_object* v_value_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_99_; 
v_key_85_ = lean_ctor_get(v_x_84_, 0);
v_value_86_ = lean_ctor_get(v_x_84_, 1);
v_tail_87_ = lean_ctor_get(v_x_84_, 2);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_99_ == 0)
{
v___x_89_ = v_x_84_;
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_value_86_);
lean_inc(v_key_85_);
lean_dec(v_x_84_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___x_91_; 
v___x_91_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_85_, v_a_82_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_82_, v_b_83_, v_tail_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 2, v___x_92_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_key_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_value_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_value_86_);
lean_dec(v_key_85_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_b_83_);
lean_ctor_set(v___x_89_, 0, v_a_82_);
v___x_97_ = v___x_89_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_82_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_b_83_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_tail_87_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
return v_x_100_;
}
else
{
lean_object* v_key_102_; lean_object* v_value_103_; lean_object* v_tail_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_127_; 
v_key_102_ = lean_ctor_get(v_x_101_, 0);
v_value_103_ = lean_ctor_get(v_x_101_, 1);
v_tail_104_ = lean_ctor_get(v_x_101_, 2);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_101_);
if (v_isSharedCheck_127_ == 0)
{
v___x_106_ = v_x_101_;
v_isShared_107_ = v_isSharedCheck_127_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_tail_104_);
lean_inc(v_value_103_);
lean_inc(v_key_102_);
lean_dec(v_x_101_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_127_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v_fold_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; size_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_108_ = lean_array_get_size(v_x_100_);
v___x_109_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_102_);
v___x_110_ = 32ULL;
v___x_111_ = lean_uint64_shift_right(v___x_109_, v___x_110_);
v_fold_112_ = lean_uint64_xor(v___x_109_, v___x_111_);
v___x_113_ = 16ULL;
v___x_114_ = lean_uint64_shift_right(v_fold_112_, v___x_113_);
v___x_115_ = lean_uint64_xor(v_fold_112_, v___x_114_);
v___x_116_ = lean_uint64_to_usize(v___x_115_);
v___x_117_ = lean_usize_of_nat(v___x_108_);
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_sub(v___x_117_, v___x_118_);
v___x_120_ = lean_usize_land(v___x_116_, v___x_119_);
v___x_121_ = lean_array_uget_borrowed(v_x_100_, v___x_120_);
lean_inc(v___x_121_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 2, v___x_121_);
v___x_123_ = v___x_106_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_key_102_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_value_103_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v___x_121_);
v___x_123_ = v_reuseFailAlloc_126_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; 
v___x_124_ = lean_array_uset(v_x_100_, v___x_120_, v___x_123_);
v_x_100_ = v___x_124_;
v_x_101_ = v_tail_104_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(lean_object* v_i_128_, lean_object* v_source_129_, lean_object* v_target_130_){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_array_get_size(v_source_129_);
v___x_132_ = lean_nat_dec_lt(v_i_128_, v___x_131_);
if (v___x_132_ == 0)
{
lean_dec_ref(v_source_129_);
lean_dec(v_i_128_);
return v_target_130_;
}
else
{
lean_object* v_es_133_; lean_object* v___x_134_; lean_object* v_source_135_; lean_object* v_target_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_es_133_ = lean_array_fget(v_source_129_, v_i_128_);
v___x_134_ = lean_box(0);
v_source_135_ = lean_array_fset(v_source_129_, v_i_128_, v___x_134_);
v_target_136_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_130_, v_es_133_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_i_128_, v___x_137_);
lean_dec(v_i_128_);
v_i_128_ = v___x_138_;
v_source_129_ = v_source_135_;
v_target_130_ = v_target_136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(lean_object* v_data_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_nbuckets_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_141_ = lean_array_get_size(v_data_140_);
v___x_142_ = lean_unsigned_to_nat(2u);
v_nbuckets_143_ = lean_nat_mul(v___x_141_, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_box(0);
v___x_146_ = lean_mk_array(v_nbuckets_143_, v___x_145_);
v___x_147_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v___x_144_, v_data_140_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object* v_a_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
else
{
lean_object* v_key_151_; lean_object* v_tail_152_; uint8_t v___x_153_; 
v_key_151_ = lean_ctor_get(v_x_149_, 0);
v_tail_152_ = lean_ctor_get(v_x_149_, 2);
v___x_153_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_151_, v_a_148_);
if (v___x_153_ == 0)
{
v_x_149_ = v_tail_152_;
goto _start;
}
else
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_155_, v_x_156_);
lean_dec(v_x_156_);
lean_dec_ref(v_a_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object* v_m_159_, lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
lean_object* v_size_162_; lean_object* v_buckets_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_206_; 
v_size_162_ = lean_ctor_get(v_m_159_, 0);
v_buckets_163_ = lean_ctor_get(v_m_159_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_m_159_);
if (v_isSharedCheck_206_ == 0)
{
v___x_165_ = v_m_159_;
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_buckets_163_);
lean_inc(v_size_162_);
lean_dec(v_m_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v_fold_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v_bkt_180_; uint8_t v___x_181_; 
v___x_167_ = lean_array_get_size(v_buckets_163_);
v___x_168_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_160_);
v___x_169_ = 32ULL;
v___x_170_ = lean_uint64_shift_right(v___x_168_, v___x_169_);
v_fold_171_ = lean_uint64_xor(v___x_168_, v___x_170_);
v___x_172_ = 16ULL;
v___x_173_ = lean_uint64_shift_right(v_fold_171_, v___x_172_);
v___x_174_ = lean_uint64_xor(v_fold_171_, v___x_173_);
v___x_175_ = lean_uint64_to_usize(v___x_174_);
v___x_176_ = lean_usize_of_nat(v___x_167_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_sub(v___x_176_, v___x_177_);
v___x_179_ = lean_usize_land(v___x_175_, v___x_178_);
v_bkt_180_ = lean_array_uget_borrowed(v_buckets_163_, v___x_179_);
v___x_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_160_, v_bkt_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v_size_x27_183_; lean_object* v___x_184_; lean_object* v_buckets_x27_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v_size_x27_183_ = lean_nat_add(v_size_162_, v___x_182_);
lean_dec(v_size_162_);
lean_inc(v_bkt_180_);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v_a_160_);
lean_ctor_set(v___x_184_, 1, v_b_161_);
lean_ctor_set(v___x_184_, 2, v_bkt_180_);
v_buckets_x27_185_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(4u);
v___x_187_ = lean_nat_mul(v_size_x27_183_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(3u);
v___x_189_ = lean_nat_div(v___x_187_, v___x_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_array_get_size(v_buckets_x27_185_);
v___x_191_ = lean_nat_dec_le(v___x_189_, v___x_190_);
lean_dec(v___x_189_);
if (v___x_191_ == 0)
{
lean_object* v_val_192_; lean_object* v___x_194_; 
v_val_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_buckets_x27_185_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_val_192_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_194_ = v___x_165_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_val_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v___x_197_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_buckets_x27_185_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_197_ = v___x_165_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_buckets_x27_185_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v___x_199_; lean_object* v_buckets_x27_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
lean_inc(v_bkt_180_);
v___x_199_ = lean_box(0);
v_buckets_x27_200_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_199_);
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_160_, v_b_161_, v_bkt_180_);
v___x_202_ = lean_array_uset(v_buckets_x27_200_, v___x_179_, v___x_201_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_202_);
v___x_204_ = v___x_165_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_size_162_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object* v_e_207_, lean_object* v_e_x27_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_st_ref_take(v_a_209_);
lean_inc_ref(v_e_x27_208_);
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_211_, v_e_207_, v_e_x27_208_);
v___x_213_ = lean_st_ref_set(v_a_209_, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v_e_x27_208_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object* v_e_215_, lean_object* v_e_x27_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_215_, v_e_x27_216_, v_a_217_);
lean_dec(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object* v_e_220_, lean_object* v_e_x27_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_220_, v_e_x27_221_, v_a_222_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object* v_e_227_, lean_object* v_e_x27_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_227_, v_e_x27_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object* v_00_u03b2_234_, lean_object* v_m_235_, lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_235_, v_a_236_, v_b_237_);
return v___x_238_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object* v_00_u03b2_239_, lean_object* v_a_240_, lean_object* v_x_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_243_, lean_object* v_a_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_243_, v_a_244_, v_x_245_);
lean_dec(v_x_245_);
lean_dec_ref(v_a_244_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(lean_object* v_00_u03b2_248_, lean_object* v_data_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_data_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(lean_object* v_00_u03b2_251_, lean_object* v_a_252_, lean_object* v_b_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_252_, v_b_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_256_, lean_object* v_i_257_, lean_object* v_source_258_, lean_object* v_target_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v_i_257_, v_source_258_, v_target_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_262_, v_x_263_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = l_Lean_maxRecDepthErrorMessage;
v___x_271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
v___x_273_ = l_Lean_MessageData_ofFormat(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
v___x_275_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2));
v___x_276_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object* v_ref_277_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_ref_277_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object* v_ref_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object* v_00_u03b1_285_, lean_object* v_ref_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_286_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object* v_00_u03b1_292_, lean_object* v_ref_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_292_, v_ref_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object* v_a_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v_key_302_; lean_object* v_value_303_; lean_object* v_tail_304_; uint8_t v___x_305_; 
v_key_302_ = lean_ctor_get(v_x_300_, 0);
v_value_303_ = lean_ctor_get(v_x_300_, 1);
v_tail_304_ = lean_ctor_get(v_x_300_, 2);
v___x_305_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_302_, v_a_299_);
if (v___x_305_ == 0)
{
v_x_300_ = v_tail_304_;
goto _start;
}
else
{
lean_object* v___x_307_; 
lean_inc(v_value_303_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v_value_303_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec_ref(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object* v_m_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_buckets_313_; lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_buckets_313_ = lean_ctor_get(v_m_311_, 1);
v___x_314_ = lean_array_get_size(v_buckets_313_);
v___x_315_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_312_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_314_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v___x_327_ = lean_array_uget_borrowed(v_buckets_313_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_312_, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_329_, v_a_330_);
lean_dec_ref(v_a_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object* v_e_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___y_338_; uint8_t v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; uint8_t v___y_353_; uint8_t v___y_354_; uint8_t v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; uint8_t v___y_368_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v_fileName_384_; lean_object* v_fileMap_385_; lean_object* v_options_386_; lean_object* v_currRecDepth_387_; lean_object* v_maxRecDepth_388_; lean_object* v_ref_389_; lean_object* v_currNamespace_390_; lean_object* v_openDecls_391_; lean_object* v_initHeartbeats_392_; lean_object* v_maxHeartbeats_393_; lean_object* v_quotContext_394_; lean_object* v_currMacroScope_395_; uint8_t v_diag_396_; lean_object* v_cancelTk_x3f_397_; uint8_t v_suppressElabErrors_398_; lean_object* v_inheritedTraceOptions_399_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_fileName_384_ = lean_ctor_get(v_a_334_, 0);
v_fileMap_385_ = lean_ctor_get(v_a_334_, 1);
v_options_386_ = lean_ctor_get(v_a_334_, 2);
v_currRecDepth_387_ = lean_ctor_get(v_a_334_, 3);
v_maxRecDepth_388_ = lean_ctor_get(v_a_334_, 4);
v_ref_389_ = lean_ctor_get(v_a_334_, 5);
v_currNamespace_390_ = lean_ctor_get(v_a_334_, 6);
v_openDecls_391_ = lean_ctor_get(v_a_334_, 7);
v_initHeartbeats_392_ = lean_ctor_get(v_a_334_, 8);
v_maxHeartbeats_393_ = lean_ctor_get(v_a_334_, 9);
v_quotContext_394_ = lean_ctor_get(v_a_334_, 10);
v_currMacroScope_395_ = lean_ctor_get(v_a_334_, 11);
v_diag_396_ = lean_ctor_get_uint8(v_a_334_, sizeof(void*)*14);
v_cancelTk_x3f_397_ = lean_ctor_get(v_a_334_, 12);
v_suppressElabErrors_398_ = lean_ctor_get_uint8(v_a_334_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_399_ = lean_ctor_get(v_a_334_, 13);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_nat_dec_eq(v_maxRecDepth_388_, v___x_499_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = lean_nat_dec_eq(v_currRecDepth_387_, v_maxRecDepth_388_);
if (v___x_501_ == 0)
{
goto v___jp_400_;
}
else
{
lean_object* v___x_502_; 
lean_dec_ref(v_e_332_);
lean_inc(v_ref_389_);
v___x_502_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_389_);
return v___x_502_;
}
}
else
{
goto v___jp_400_;
}
v___jp_337_:
{
if (v___y_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = l_Lean_Expr_forallE___override(v___y_338_, v___y_340_, v___y_341_, v___y_339_);
v___x_344_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_343_, v_a_333_);
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = l_Lean_instBEqBinderInfo_beq(v___y_339_, v___y_339_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = l_Lean_Expr_forallE___override(v___y_338_, v___y_340_, v___y_341_, v___y_339_);
v___x_347_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_346_, v_a_333_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
lean_dec_ref(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_338_);
lean_inc_ref(v_e_332_);
v___x_348_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v_e_332_, v_a_333_);
return v___x_348_;
}
}
}
v___jp_349_:
{
if (v___y_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = l_Lean_Expr_lam___override(v___y_350_, v___y_352_, v___y_351_, v___y_353_);
v___x_356_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_355_, v_a_333_);
return v___x_356_;
}
else
{
uint8_t v___x_357_; 
v___x_357_ = l_Lean_instBEqBinderInfo_beq(v___y_353_, v___y_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_Expr_lam___override(v___y_350_, v___y_352_, v___y_351_, v___y_353_);
v___x_359_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_358_, v_a_333_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
lean_dec_ref(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_inc_ref(v_e_332_);
v___x_360_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v_e_332_, v_a_333_);
return v___x_360_;
}
}
}
v___jp_361_:
{
if (v___y_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec_ref(v___y_367_);
v___x_369_ = l_Lean_Expr_letE___override(v___y_364_, v___y_366_, v___y_363_, v___y_365_, v___y_362_);
v___x_370_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_369_, v_a_333_);
return v___x_370_;
}
else
{
size_t v___x_371_; size_t v___x_372_; uint8_t v___x_373_; 
v___x_371_ = lean_ptr_addr(v___y_367_);
lean_dec_ref(v___y_367_);
v___x_372_ = lean_ptr_addr(v___y_365_);
v___x_373_ = lean_usize_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l_Lean_Expr_letE___override(v___y_364_, v___y_366_, v___y_363_, v___y_365_, v___y_362_);
v___x_375_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_374_, v_a_333_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
lean_dec_ref(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_inc_ref(v_e_332_);
v___x_376_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v_e_332_, v_a_333_);
return v___x_376_;
}
}
}
v___jp_377_:
{
if (v___y_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = l_Lean_Expr_app___override(v___y_379_, v___y_378_);
v___x_382_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_381_, v_a_333_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; 
lean_dec_ref(v___y_379_);
lean_dec_ref(v___y_378_);
lean_inc_ref(v_e_332_);
v___x_383_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v_e_332_, v_a_333_);
return v___x_383_;
}
}
v___jp_400_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_st_ref_get(v_a_333_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_401_, v_e_332_);
lean_dec(v___x_401_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_e_332_);
v_val_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_val_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 0);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_val_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v___x_402_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_add(v_currRecDepth_387_, v___x_411_);
lean_inc_ref(v_inheritedTraceOptions_399_);
lean_inc(v_cancelTk_x3f_397_);
lean_inc(v_currMacroScope_395_);
lean_inc(v_quotContext_394_);
lean_inc(v_maxHeartbeats_393_);
lean_inc(v_initHeartbeats_392_);
lean_inc(v_openDecls_391_);
lean_inc(v_currNamespace_390_);
lean_inc(v_ref_389_);
lean_inc(v_maxRecDepth_388_);
lean_inc_ref(v_options_386_);
lean_inc_ref(v_fileMap_385_);
lean_inc_ref(v_fileName_384_);
v___x_413_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_413_, 0, v_fileName_384_);
lean_ctor_set(v___x_413_, 1, v_fileMap_385_);
lean_ctor_set(v___x_413_, 2, v_options_386_);
lean_ctor_set(v___x_413_, 3, v___x_412_);
lean_ctor_set(v___x_413_, 4, v_maxRecDepth_388_);
lean_ctor_set(v___x_413_, 5, v_ref_389_);
lean_ctor_set(v___x_413_, 6, v_currNamespace_390_);
lean_ctor_set(v___x_413_, 7, v_openDecls_391_);
lean_ctor_set(v___x_413_, 8, v_initHeartbeats_392_);
lean_ctor_set(v___x_413_, 9, v_maxHeartbeats_393_);
lean_ctor_set(v___x_413_, 10, v_quotContext_394_);
lean_ctor_set(v___x_413_, 11, v_currMacroScope_395_);
lean_ctor_set(v___x_413_, 12, v_cancelTk_x3f_397_);
lean_ctor_set(v___x_413_, 13, v_inheritedTraceOptions_399_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*14, v_diag_396_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*14 + 1, v_suppressElabErrors_398_);
switch(lean_obj_tag(v_e_332_))
{
case 7:
{
lean_object* v_binderName_414_; lean_object* v_binderType_415_; lean_object* v_body_416_; uint8_t v_binderInfo_417_; lean_object* v___x_418_; 
v_binderName_414_ = lean_ctor_get(v_e_332_, 0);
v_binderType_415_ = lean_ctor_get(v_e_332_, 1);
v_body_416_ = lean_ctor_get(v_e_332_, 2);
v_binderInfo_417_ = lean_ctor_get_uint8(v_e_332_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_415_);
v___x_418_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_415_, v_a_333_, v___x_413_, v_a_335_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
lean_inc_ref(v_body_416_);
v___x_420_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_416_, v_a_333_, v___x_413_, v_a_335_);
lean_dec_ref(v___x_413_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; size_t v___x_422_; size_t v___x_423_; uint8_t v___x_424_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref(v___x_420_);
v___x_422_ = lean_ptr_addr(v_binderType_415_);
v___x_423_ = lean_ptr_addr(v_a_419_);
v___x_424_ = lean_usize_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_inc(v_binderName_414_);
v___y_338_ = v_binderName_414_;
v___y_339_ = v_binderInfo_417_;
v___y_340_ = v_a_419_;
v___y_341_ = v_a_421_;
v___y_342_ = v___x_424_;
goto v___jp_337_;
}
else
{
size_t v___x_425_; size_t v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_ptr_addr(v_body_416_);
v___x_426_ = lean_ptr_addr(v_a_421_);
v___x_427_ = lean_usize_dec_eq(v___x_425_, v___x_426_);
lean_inc(v_binderName_414_);
v___y_338_ = v_binderName_414_;
v___y_339_ = v_binderInfo_417_;
v___y_340_ = v_a_419_;
v___y_341_ = v_a_421_;
v___y_342_ = v___x_427_;
goto v___jp_337_;
}
}
else
{
lean_dec(v_a_419_);
lean_dec_ref(v_e_332_);
return v___x_420_;
}
}
else
{
lean_dec_ref(v_e_332_);
lean_dec_ref(v___x_413_);
return v___x_418_;
}
}
case 6:
{
lean_object* v_binderName_428_; lean_object* v_binderType_429_; lean_object* v_body_430_; uint8_t v_binderInfo_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_binderName_428_ = lean_ctor_get(v_e_332_, 0);
v_binderType_429_ = lean_ctor_get(v_e_332_, 1);
v_body_430_ = lean_ctor_get(v_e_332_, 2);
v_binderInfo_431_ = lean_ctor_get_uint8(v_e_332_, sizeof(void*)*3 + 8);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_332_, v_e_332_, v___x_432_);
v___x_434_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_332_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_433_, v_a_333_, v___x_413_, v_a_335_);
lean_dec_ref(v___x_413_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v___x_435_);
v___x_437_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v_a_436_, v_a_333_);
return v___x_437_;
}
else
{
lean_dec_ref(v_e_332_);
return v___x_435_;
}
}
else
{
lean_object* v___x_438_; 
lean_dec_ref(v___x_433_);
lean_inc_ref(v_binderType_429_);
v___x_438_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_429_, v_a_333_, v___x_413_, v_a_335_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
lean_inc_ref(v_body_430_);
v___x_440_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_430_, v_a_333_, v___x_413_, v_a_335_);
lean_dec_ref(v___x_413_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
v___x_442_ = lean_ptr_addr(v_binderType_429_);
v___x_443_ = lean_ptr_addr(v_a_439_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_inc(v_binderName_428_);
v___y_350_ = v_binderName_428_;
v___y_351_ = v_a_441_;
v___y_352_ = v_a_439_;
v___y_353_ = v_binderInfo_431_;
v___y_354_ = v___x_444_;
goto v___jp_349_;
}
else
{
size_t v___x_445_; size_t v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_ptr_addr(v_body_430_);
v___x_446_ = lean_ptr_addr(v_a_441_);
v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
lean_inc(v_binderName_428_);
v___y_350_ = v_binderName_428_;
v___y_351_ = v_a_441_;
v___y_352_ = v_a_439_;
v___y_353_ = v_binderInfo_431_;
v___y_354_ = v___x_447_;
goto v___jp_349_;
}
}
else
{
lean_dec(v_a_439_);
lean_dec_ref(v_e_332_);
return v___x_440_;
}
}
else
{
lean_dec_ref(v_e_332_);
lean_dec_ref(v___x_413_);
return v___x_438_;
}
}
}
case 8:
{
lean_object* v_declName_448_; lean_object* v_type_449_; lean_object* v_value_450_; lean_object* v_body_451_; uint8_t v_nondep_452_; lean_object* v___x_453_; 
v_declName_448_ = lean_ctor_get(v_e_332_, 0);
v_type_449_ = lean_ctor_get(v_e_332_, 1);
v_value_450_ = lean_ctor_get(v_e_332_, 2);
v_body_451_ = lean_ctor_get(v_e_332_, 3);
v_nondep_452_ = lean_ctor_get_uint8(v_e_332_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_449_);
v___x_453_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_449_, v_a_333_, v___x_413_, v_a_335_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref(v___x_453_);
lean_inc_ref(v_value_450_);
v___x_455_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_450_, v_a_333_, v___x_413_, v_a_335_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref(v___x_455_);
lean_inc_ref(v_body_451_);
v___x_457_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_451_, v_a_333_, v___x_413_, v_a_335_);
lean_dec_ref(v___x_413_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_ptr_addr(v_type_449_);
v___x_460_ = lean_ptr_addr(v_a_454_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_inc_ref(v_body_451_);
lean_inc(v_declName_448_);
v___y_362_ = v_nondep_452_;
v___y_363_ = v_a_456_;
v___y_364_ = v_declName_448_;
v___y_365_ = v_a_458_;
v___y_366_ = v_a_454_;
v___y_367_ = v_body_451_;
v___y_368_ = v___x_461_;
goto v___jp_361_;
}
else
{
size_t v___x_462_; size_t v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_ptr_addr(v_value_450_);
v___x_463_ = lean_ptr_addr(v_a_456_);
v___x_464_ = lean_usize_dec_eq(v___x_462_, v___x_463_);
lean_inc_ref(v_body_451_);
lean_inc(v_declName_448_);
v___y_362_ = v_nondep_452_;
v___y_363_ = v_a_456_;
v___y_364_ = v_declName_448_;
v___y_365_ = v_a_458_;
v___y_366_ = v_a_454_;
v___y_367_ = v_body_451_;
v___y_368_ = v___x_464_;
goto v___jp_361_;
}
}
else
{
lean_dec(v_a_456_);
lean_dec(v_a_454_);
lean_dec_ref(v_e_332_);
return v___x_457_;
}
}
else
{
lean_dec(v_a_454_);
lean_dec_ref(v_e_332_);
lean_dec_ref(v___x_413_);
return v___x_455_;
}
}
else
{
lean_dec_ref(v_e_332_);
lean_dec_ref(v___x_413_);
return v___x_453_;
}
}
case 5:
{
lean_object* v_fn_465_; lean_object* v_arg_466_; lean_object* v___x_467_; 
v_fn_465_ = lean_ctor_get(v_e_332_, 0);
v_arg_466_ = lean_ctor_get(v_e_332_, 1);
lean_inc_ref(v_fn_465_);
v___x_467_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_465_, v_a_333_, v___x_413_, v_a_335_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
lean_inc_ref(v_arg_466_);
v___x_469_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_466_, v_a_333_, v___x_413_, v_a_335_);
lean_dec_ref(v___x_413_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; size_t v___x_471_; size_t v___x_472_; uint8_t v___x_473_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
v___x_471_ = lean_ptr_addr(v_fn_465_);
v___x_472_ = lean_ptr_addr(v_a_468_);
v___x_473_ = lean_usize_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
v___y_378_ = v_a_470_;
v___y_379_ = v_a_468_;
v___y_380_ = v___x_473_;
goto v___jp_377_;
}
else
{
size_t v___x_474_; size_t v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_ptr_addr(v_arg_466_);
v___x_475_ = lean_ptr_addr(v_a_470_);
v___x_476_ = lean_usize_dec_eq(v___x_474_, v___x_475_);
v___y_378_ = v_a_470_;
v___y_379_ = v_a_468_;
v___y_380_ = v___x_476_;
goto v___jp_377_;
}
}
else
{
lean_dec(v_a_468_);
lean_dec_ref(v_e_332_);
return v___x_469_;
}
}
else
{
lean_dec_ref(v_e_332_);
lean_dec_ref(v___x_413_);
return v___x_467_;
}
}
case 10:
{
lean_object* v_data_477_; lean_object* v_expr_478_; lean_object* v___x_479_; 
v_data_477_ = lean_ctor_get(v_e_332_, 0);
v_expr_478_ = lean_ctor_get(v_e_332_, 1);
lean_inc_ref(v_expr_478_);
v___x_479_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_478_, v_a_333_, v___x_413_, v_a_335_);
lean_dec_ref(v___x_413_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v___x_479_);
v___x_481_ = lean_ptr_addr(v_expr_478_);
v___x_482_ = lean_ptr_addr(v_a_480_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v_data_477_);
v___x_484_ = l_Lean_Expr_mdata___override(v_data_477_, v_a_480_);
v___x_485_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_484_, v_a_333_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
lean_dec(v_a_480_);
lean_inc_ref(v_e_332_);
v___x_486_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v_e_332_, v_a_333_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_e_332_);
return v___x_479_;
}
}
case 11:
{
lean_object* v_typeName_487_; lean_object* v_idx_488_; lean_object* v_struct_489_; lean_object* v___x_490_; 
v_typeName_487_ = lean_ctor_get(v_e_332_, 0);
v_idx_488_ = lean_ctor_get(v_e_332_, 1);
v_struct_489_ = lean_ctor_get(v_e_332_, 2);
lean_inc_ref(v_struct_489_);
v___x_490_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_489_, v_a_333_, v___x_413_, v_a_335_);
lean_dec_ref(v___x_413_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_ptr_addr(v_struct_489_);
v___x_493_ = lean_ptr_addr(v_a_491_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc(v_idx_488_);
lean_inc(v_typeName_487_);
v___x_495_ = l_Lean_Expr_proj___override(v_typeName_487_, v_idx_488_, v_a_491_);
v___x_496_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v___x_495_, v_a_333_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; 
lean_dec(v_a_491_);
lean_inc_ref(v_e_332_);
v___x_497_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_332_, v_e_332_, v_a_333_);
return v___x_497_;
}
}
else
{
lean_dec_ref(v_e_332_);
return v___x_490_;
}
}
default: 
{
lean_object* v___x_498_; 
lean_dec_ref(v___x_413_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_e_332_);
return v___x_498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object* v_e_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_510_, v_a_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object* v_00_u03b2_513_, lean_object* v_m_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_513_, v_m_514_, v_a_515_);
lean_dec_ref(v_a_515_);
lean_dec_ref(v_m_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_518_, v_x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_521_, v_a_522_, v_x_523_);
lean_dec(v_x_523_);
lean_dec_ref(v_a_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object* v_e_525_, lean_object* v_c_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_st_mk_ref(v_c_526_);
v___x_531_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_525_, v___x_530_, v_a_527_, v_a_528_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_541_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_541_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_536_ = lean_st_ref_get(v___x_530_);
lean_dec(v___x_530_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_a_532_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_537_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v___x_530_);
v_a_542_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_531_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_531_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object* v_e_550_, lean_object* v_c_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_550_, v_c_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
return v_res_555_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__1(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_unsigned_to_nat(16u);
v___x_559_ = lean_mk_array(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__2(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__1, &l_Lean_Meta_Sym_etaReduceAll___closed__1_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__1);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_Meta_Sym_etaReduceAll___closed__0));
v___x_568_ = lean_find_expr(v___x_567_, v_e_563_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v_e_563_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v___x_568_);
v___x_570_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__2, &l_Lean_Meta_Sym_etaReduceAll___closed__2_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__2);
v___x_571_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_563_, v___x_570_, v_a_564_, v_a_565_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_fst_576_; lean_object* v___x_578_; 
v_fst_576_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_fst_576_);
lean_dec(v_a_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v_fst_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_fst_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_571_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_571_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Meta_Sym_etaReduceAll(v_e_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_593_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Eta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
