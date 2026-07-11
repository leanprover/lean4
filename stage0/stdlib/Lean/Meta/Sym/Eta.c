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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_75_; uint8_t v___x_76_; uint8_t v___x_77_; 
v___x_75_ = l_Lean_Meta_Sym_etaReduce(v_e_74_);
v___x_76_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_74_, v___x_75_);
lean_dec_ref(v___x_75_);
v___x_77_ = lean_bool_not(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isEtaReducible___boxed(lean_object* v_e_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Meta_Sym_isEtaReducible(v_e_78_);
lean_dec_ref(v_e_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(lean_object* v_a_81_, lean_object* v_b_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_dec(v_b_82_);
lean_dec_ref(v_a_81_);
return v_x_83_;
}
else
{
lean_object* v_key_84_; lean_object* v_value_85_; lean_object* v_tail_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_98_; 
v_key_84_ = lean_ctor_get(v_x_83_, 0);
v_value_85_ = lean_ctor_get(v_x_83_, 1);
v_tail_86_ = lean_ctor_get(v_x_83_, 2);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_98_ == 0)
{
v___x_88_ = v_x_83_;
v_isShared_89_ = v_isSharedCheck_98_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_tail_86_);
lean_inc(v_value_85_);
lean_inc(v_key_84_);
lean_dec(v_x_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_98_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
uint8_t v___x_90_; 
v___x_90_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_84_, v_a_81_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_81_, v_b_82_, v_tail_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v___x_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_key_84_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_value_85_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_value_85_);
lean_dec(v_key_84_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v_b_82_);
lean_ctor_set(v___x_88_, 0, v_a_81_);
v___x_96_ = v___x_88_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_81_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_b_82_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v_tail_86_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
return v_x_99_;
}
else
{
lean_object* v_key_101_; lean_object* v_value_102_; lean_object* v_tail_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_126_; 
v_key_101_ = lean_ctor_get(v_x_100_, 0);
v_value_102_ = lean_ctor_get(v_x_100_, 1);
v_tail_103_ = lean_ctor_get(v_x_100_, 2);
v_isSharedCheck_126_ = !lean_is_exclusive(v_x_100_);
if (v_isSharedCheck_126_ == 0)
{
v___x_105_ = v_x_100_;
v_isShared_106_ = v_isSharedCheck_126_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_tail_103_);
lean_inc(v_value_102_);
lean_inc(v_key_101_);
lean_dec(v_x_100_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_126_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v_fold_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_107_ = lean_array_get_size(v_x_99_);
v___x_108_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_101_);
v___x_109_ = 32ULL;
v___x_110_ = lean_uint64_shift_right(v___x_108_, v___x_109_);
v_fold_111_ = lean_uint64_xor(v___x_108_, v___x_110_);
v___x_112_ = 16ULL;
v___x_113_ = lean_uint64_shift_right(v_fold_111_, v___x_112_);
v___x_114_ = lean_uint64_xor(v_fold_111_, v___x_113_);
v___x_115_ = lean_uint64_to_usize(v___x_114_);
v___x_116_ = lean_usize_of_nat(v___x_107_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_sub(v___x_116_, v___x_117_);
v___x_119_ = lean_usize_land(v___x_115_, v___x_118_);
v___x_120_ = lean_array_uget_borrowed(v_x_99_, v___x_119_);
lean_inc(v___x_120_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 2, v___x_120_);
v___x_122_ = v___x_105_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_key_101_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_value_102_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v___x_120_);
v___x_122_ = v_reuseFailAlloc_125_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; 
v___x_123_ = lean_array_uset(v_x_99_, v___x_119_, v___x_122_);
v_x_99_ = v___x_123_;
v_x_100_ = v_tail_103_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(lean_object* v_i_127_, lean_object* v_source_128_, lean_object* v_target_129_){
_start:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_array_get_size(v_source_128_);
v___x_131_ = lean_nat_dec_lt(v_i_127_, v___x_130_);
if (v___x_131_ == 0)
{
lean_dec_ref(v_source_128_);
lean_dec(v_i_127_);
return v_target_129_;
}
else
{
lean_object* v_es_132_; lean_object* v___x_133_; lean_object* v_source_134_; lean_object* v_target_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_es_132_ = lean_array_fget(v_source_128_, v_i_127_);
v___x_133_ = lean_box(0);
v_source_134_ = lean_array_fset(v_source_128_, v_i_127_, v___x_133_);
v_target_135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_129_, v_es_132_);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_i_127_, v___x_136_);
lean_dec(v_i_127_);
v_i_127_ = v___x_137_;
v_source_128_ = v_source_134_;
v_target_129_ = v_target_135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(lean_object* v_data_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_nbuckets_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_140_ = lean_array_get_size(v_data_139_);
v___x_141_ = lean_unsigned_to_nat(2u);
v_nbuckets_142_ = lean_nat_mul(v___x_140_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_box(0);
v___x_145_ = lean_mk_array(v_nbuckets_142_, v___x_144_);
v___x_146_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v___x_143_, v_data_139_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object* v_a_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
else
{
lean_object* v_key_150_; lean_object* v_tail_151_; uint8_t v___x_152_; 
v_key_150_ = lean_ctor_get(v_x_148_, 0);
v_tail_151_ = lean_ctor_get(v_x_148_, 2);
v___x_152_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_150_, v_a_147_);
if (v___x_152_ == 0)
{
v_x_148_ = v_tail_151_;
goto _start;
}
else
{
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_154_, v_x_155_);
lean_dec(v_x_155_);
lean_dec_ref(v_a_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object* v_m_158_, lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v_size_161_; lean_object* v_buckets_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_205_; 
v_size_161_ = lean_ctor_get(v_m_158_, 0);
v_buckets_162_ = lean_ctor_get(v_m_158_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_m_158_);
if (v_isSharedCheck_205_ == 0)
{
v___x_164_ = v_m_158_;
v_isShared_165_ = v_isSharedCheck_205_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_buckets_162_);
lean_inc(v_size_161_);
lean_dec(v_m_158_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_205_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v_fold_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v_bkt_179_; uint8_t v___x_180_; 
v___x_166_ = lean_array_get_size(v_buckets_162_);
v___x_167_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_159_);
v___x_168_ = 32ULL;
v___x_169_ = lean_uint64_shift_right(v___x_167_, v___x_168_);
v_fold_170_ = lean_uint64_xor(v___x_167_, v___x_169_);
v___x_171_ = 16ULL;
v___x_172_ = lean_uint64_shift_right(v_fold_170_, v___x_171_);
v___x_173_ = lean_uint64_xor(v_fold_170_, v___x_172_);
v___x_174_ = lean_uint64_to_usize(v___x_173_);
v___x_175_ = lean_usize_of_nat(v___x_166_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_sub(v___x_175_, v___x_176_);
v___x_178_ = lean_usize_land(v___x_174_, v___x_177_);
v_bkt_179_ = lean_array_uget_borrowed(v_buckets_162_, v___x_178_);
v___x_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_159_, v_bkt_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v_size_x27_182_; lean_object* v___x_183_; lean_object* v_buckets_x27_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v_size_x27_182_ = lean_nat_add(v_size_161_, v___x_181_);
lean_dec(v_size_161_);
lean_inc(v_bkt_179_);
v___x_183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_183_, 0, v_a_159_);
lean_ctor_set(v___x_183_, 1, v_b_160_);
lean_ctor_set(v___x_183_, 2, v_bkt_179_);
v_buckets_x27_184_ = lean_array_uset(v_buckets_162_, v___x_178_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(4u);
v___x_186_ = lean_nat_mul(v_size_x27_182_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(3u);
v___x_188_ = lean_nat_div(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_array_get_size(v_buckets_x27_184_);
v___x_190_ = lean_nat_dec_le(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
if (v___x_190_ == 0)
{
lean_object* v_val_191_; lean_object* v___x_193_; 
v_val_191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_buckets_x27_184_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_val_191_);
lean_ctor_set(v___x_164_, 0, v_size_x27_182_);
v___x_193_ = v___x_164_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_size_x27_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_val_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_196_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_buckets_x27_184_);
lean_ctor_set(v___x_164_, 0, v_size_x27_182_);
v___x_196_ = v___x_164_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_size_x27_182_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_buckets_x27_184_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_object* v___x_198_; lean_object* v_buckets_x27_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
lean_inc(v_bkt_179_);
v___x_198_ = lean_box(0);
v_buckets_x27_199_ = lean_array_uset(v_buckets_162_, v___x_178_, v___x_198_);
v___x_200_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_159_, v_b_160_, v_bkt_179_);
v___x_201_ = lean_array_uset(v_buckets_x27_199_, v___x_178_, v___x_200_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v___x_201_);
v___x_203_ = v___x_164_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_size_161_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object* v_e_206_, lean_object* v_e_x27_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = lean_st_ref_take(v_a_208_);
lean_inc_ref(v_e_x27_207_);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_210_, v_e_206_, v_e_x27_207_);
v___x_212_ = lean_st_ref_set(v_a_208_, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_e_x27_207_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object* v_e_214_, lean_object* v_e_x27_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_214_, v_e_x27_215_, v_a_216_);
lean_dec(v_a_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object* v_e_219_, lean_object* v_e_x27_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_219_, v_e_x27_220_, v_a_221_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object* v_e_226_, lean_object* v_e_x27_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_226_, v_e_x27_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object* v_00_u03b2_233_, lean_object* v_m_234_, lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_234_, v_a_235_, v_b_236_);
return v___x_237_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object* v_00_u03b2_238_, lean_object* v_a_239_, lean_object* v_x_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_239_, v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_242_, lean_object* v_a_243_, lean_object* v_x_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_242_, v_a_243_, v_x_244_);
lean_dec(v_x_244_);
lean_dec_ref(v_a_243_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(lean_object* v_00_u03b2_247_, lean_object* v_data_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_data_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(lean_object* v_00_u03b2_250_, lean_object* v_a_251_, lean_object* v_b_252_, lean_object* v_x_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_251_, v_b_252_, v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_255_, lean_object* v_i_256_, lean_object* v_source_257_, lean_object* v_target_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v_i_256_, v_source_257_, v_target_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_261_, v_x_262_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = l_Lean_maxRecDepthErrorMessage;
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
v___x_272_ = l_Lean_MessageData_ofFormat(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
v___x_274_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2));
v___x_275_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object* v_ref_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_ref_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object* v_ref_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object* v_00_u03b1_284_, lean_object* v_ref_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_285_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object* v_00_u03b1_291_, lean_object* v_ref_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_291_, v_ref_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object* v_a_298_, lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v_key_301_; lean_object* v_value_302_; lean_object* v_tail_303_; uint8_t v___x_304_; 
v_key_301_ = lean_ctor_get(v_x_299_, 0);
v_value_302_ = lean_ctor_get(v_x_299_, 1);
v_tail_303_ = lean_ctor_get(v_x_299_, 2);
v___x_304_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_301_, v_a_298_);
if (v___x_304_ == 0)
{
v_x_299_ = v_tail_303_;
goto _start;
}
else
{
lean_object* v___x_306_; 
lean_inc(v_value_302_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v_value_302_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_307_, lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_307_, v_x_308_);
lean_dec(v_x_308_);
lean_dec_ref(v_a_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object* v_m_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_buckets_312_; lean_object* v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v_fold_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_buckets_312_ = lean_ctor_get(v_m_310_, 1);
v___x_313_ = lean_array_get_size(v_buckets_312_);
v___x_314_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_311_);
v___x_315_ = 32ULL;
v___x_316_ = lean_uint64_shift_right(v___x_314_, v___x_315_);
v_fold_317_ = lean_uint64_xor(v___x_314_, v___x_316_);
v___x_318_ = 16ULL;
v___x_319_ = lean_uint64_shift_right(v_fold_317_, v___x_318_);
v___x_320_ = lean_uint64_xor(v_fold_317_, v___x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = lean_usize_of_nat(v___x_313_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_sub(v___x_322_, v___x_323_);
v___x_325_ = lean_usize_land(v___x_321_, v___x_324_);
v___x_326_ = lean_array_uget_borrowed(v_buckets_312_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_311_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object* v_m_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_328_, v_a_329_);
lean_dec_ref(v_a_329_);
lean_dec_ref(v_m_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object* v_e_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
uint8_t v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; uint8_t v___y_341_; lean_object* v___y_349_; lean_object* v___y_350_; uint8_t v___y_351_; lean_object* v___y_352_; uint8_t v___y_353_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; uint8_t v___y_366_; uint8_t v___y_367_; lean_object* v___y_377_; lean_object* v___y_378_; uint8_t v___y_379_; lean_object* v_fileName_383_; lean_object* v_fileMap_384_; lean_object* v_options_385_; lean_object* v_currRecDepth_386_; lean_object* v_maxRecDepth_387_; lean_object* v_ref_388_; lean_object* v_currNamespace_389_; lean_object* v_openDecls_390_; lean_object* v_initHeartbeats_391_; lean_object* v_maxHeartbeats_392_; lean_object* v_quotContext_393_; lean_object* v_currMacroScope_394_; uint8_t v_diag_395_; lean_object* v_cancelTk_x3f_396_; uint8_t v_suppressElabErrors_397_; lean_object* v_inheritedTraceOptions_398_; uint8_t v___y_400_; lean_object* v___x_500_; uint8_t v___x_501_; uint8_t v___x_502_; 
v_fileName_383_ = lean_ctor_get(v_a_333_, 0);
v_fileMap_384_ = lean_ctor_get(v_a_333_, 1);
v_options_385_ = lean_ctor_get(v_a_333_, 2);
v_currRecDepth_386_ = lean_ctor_get(v_a_333_, 3);
v_maxRecDepth_387_ = lean_ctor_get(v_a_333_, 4);
v_ref_388_ = lean_ctor_get(v_a_333_, 5);
v_currNamespace_389_ = lean_ctor_get(v_a_333_, 6);
v_openDecls_390_ = lean_ctor_get(v_a_333_, 7);
v_initHeartbeats_391_ = lean_ctor_get(v_a_333_, 8);
v_maxHeartbeats_392_ = lean_ctor_get(v_a_333_, 9);
v_quotContext_393_ = lean_ctor_get(v_a_333_, 10);
v_currMacroScope_394_ = lean_ctor_get(v_a_333_, 11);
v_diag_395_ = lean_ctor_get_uint8(v_a_333_, sizeof(void*)*14);
v_cancelTk_x3f_396_ = lean_ctor_get(v_a_333_, 12);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v_a_333_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_398_ = lean_ctor_get(v_a_333_, 13);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_nat_dec_eq(v_maxRecDepth_387_, v___x_500_);
v___x_502_ = lean_bool_not(v___x_501_);
if (v___x_502_ == 0)
{
v___y_400_ = v___x_502_;
goto v___jp_399_;
}
else
{
uint8_t v___x_503_; 
v___x_503_ = lean_nat_dec_eq(v_currRecDepth_386_, v_maxRecDepth_387_);
v___y_400_ = v___x_503_;
goto v___jp_399_;
}
v___jp_336_:
{
if (v___y_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = l_Lean_Expr_forallE___override(v___y_340_, v___y_338_, v___y_339_, v___y_337_);
v___x_343_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_342_, v_a_332_);
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_instBEqBinderInfo_beq(v___y_337_, v___y_337_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = l_Lean_Expr_forallE___override(v___y_340_, v___y_338_, v___y_339_, v___y_337_);
v___x_346_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_345_, v_a_332_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; 
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
lean_inc_ref(v_e_331_);
v___x_347_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v_e_331_, v_a_332_);
return v___x_347_;
}
}
}
v___jp_348_:
{
if (v___y_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = l_Lean_Expr_lam___override(v___y_352_, v___y_349_, v___y_350_, v___y_351_);
v___x_355_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_354_, v_a_332_);
return v___x_355_;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = l_Lean_instBEqBinderInfo_beq(v___y_351_, v___y_351_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_Lean_Expr_lam___override(v___y_352_, v___y_349_, v___y_350_, v___y_351_);
v___x_358_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_357_, v_a_332_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; 
lean_dec(v___y_352_);
lean_dec_ref(v___y_350_);
lean_dec_ref(v___y_349_);
lean_inc_ref(v_e_331_);
v___x_359_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v_e_331_, v_a_332_);
return v___x_359_;
}
}
}
v___jp_360_:
{
if (v___y_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec_ref(v___y_364_);
v___x_368_ = l_Lean_Expr_letE___override(v___y_361_, v___y_363_, v___y_365_, v___y_362_, v___y_366_);
v___x_369_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_368_, v_a_332_);
return v___x_369_;
}
else
{
size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v___x_370_ = lean_ptr_addr(v___y_364_);
lean_dec_ref(v___y_364_);
v___x_371_ = lean_ptr_addr(v___y_362_);
v___x_372_ = lean_usize_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l_Lean_Expr_letE___override(v___y_361_, v___y_363_, v___y_365_, v___y_362_, v___y_366_);
v___x_374_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_373_, v_a_332_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
lean_dec_ref(v___y_365_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_inc_ref(v_e_331_);
v___x_375_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v_e_331_, v_a_332_);
return v___x_375_;
}
}
}
v___jp_376_:
{
if (v___y_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = l_Lean_Expr_app___override(v___y_378_, v___y_377_);
v___x_381_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_380_, v_a_332_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
lean_dec_ref(v___y_378_);
lean_dec_ref(v___y_377_);
lean_inc_ref(v_e_331_);
v___x_382_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v_e_331_, v_a_332_);
return v___x_382_;
}
}
v___jp_399_:
{
if (v___y_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_st_ref_get(v_a_332_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_401_, v_e_331_);
lean_dec(v___x_401_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_e_331_);
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
v___x_412_ = lean_nat_add(v_currRecDepth_386_, v___x_411_);
lean_inc_ref(v_inheritedTraceOptions_398_);
lean_inc(v_cancelTk_x3f_396_);
lean_inc(v_currMacroScope_394_);
lean_inc(v_quotContext_393_);
lean_inc(v_maxHeartbeats_392_);
lean_inc(v_initHeartbeats_391_);
lean_inc(v_openDecls_390_);
lean_inc(v_currNamespace_389_);
lean_inc(v_ref_388_);
lean_inc(v_maxRecDepth_387_);
lean_inc_ref(v_options_385_);
lean_inc_ref(v_fileMap_384_);
lean_inc_ref(v_fileName_383_);
v___x_413_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_413_, 0, v_fileName_383_);
lean_ctor_set(v___x_413_, 1, v_fileMap_384_);
lean_ctor_set(v___x_413_, 2, v_options_385_);
lean_ctor_set(v___x_413_, 3, v___x_412_);
lean_ctor_set(v___x_413_, 4, v_maxRecDepth_387_);
lean_ctor_set(v___x_413_, 5, v_ref_388_);
lean_ctor_set(v___x_413_, 6, v_currNamespace_389_);
lean_ctor_set(v___x_413_, 7, v_openDecls_390_);
lean_ctor_set(v___x_413_, 8, v_initHeartbeats_391_);
lean_ctor_set(v___x_413_, 9, v_maxHeartbeats_392_);
lean_ctor_set(v___x_413_, 10, v_quotContext_393_);
lean_ctor_set(v___x_413_, 11, v_currMacroScope_394_);
lean_ctor_set(v___x_413_, 12, v_cancelTk_x3f_396_);
lean_ctor_set(v___x_413_, 13, v_inheritedTraceOptions_398_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*14, v_diag_395_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*14 + 1, v_suppressElabErrors_397_);
switch(lean_obj_tag(v_e_331_))
{
case 7:
{
lean_object* v_binderName_414_; lean_object* v_binderType_415_; lean_object* v_body_416_; uint8_t v_binderInfo_417_; lean_object* v___x_418_; 
v_binderName_414_ = lean_ctor_get(v_e_331_, 0);
v_binderType_415_ = lean_ctor_get(v_e_331_, 1);
v_body_416_ = lean_ctor_get(v_e_331_, 2);
v_binderInfo_417_ = lean_ctor_get_uint8(v_e_331_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_415_);
v___x_418_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_415_, v_a_332_, v___x_413_, v_a_334_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
lean_inc_ref(v_body_416_);
v___x_420_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_416_, v_a_332_, v___x_413_, v_a_334_);
lean_dec_ref_known(v___x_413_, 14);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; size_t v___x_422_; size_t v___x_423_; uint8_t v___x_424_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = lean_ptr_addr(v_binderType_415_);
v___x_423_ = lean_ptr_addr(v_a_419_);
v___x_424_ = lean_usize_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_inc(v_binderName_414_);
v___y_337_ = v_binderInfo_417_;
v___y_338_ = v_a_419_;
v___y_339_ = v_a_421_;
v___y_340_ = v_binderName_414_;
v___y_341_ = v___x_424_;
goto v___jp_336_;
}
else
{
size_t v___x_425_; size_t v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_ptr_addr(v_body_416_);
v___x_426_ = lean_ptr_addr(v_a_421_);
v___x_427_ = lean_usize_dec_eq(v___x_425_, v___x_426_);
lean_inc(v_binderName_414_);
v___y_337_ = v_binderInfo_417_;
v___y_338_ = v_a_419_;
v___y_339_ = v_a_421_;
v___y_340_ = v_binderName_414_;
v___y_341_ = v___x_427_;
goto v___jp_336_;
}
}
else
{
lean_dec(v_a_419_);
lean_dec_ref_known(v_e_331_, 3);
return v___x_420_;
}
}
else
{
lean_dec_ref_known(v_e_331_, 3);
lean_dec_ref_known(v___x_413_, 14);
return v___x_418_;
}
}
case 6:
{
lean_object* v_binderName_428_; lean_object* v_binderType_429_; lean_object* v_body_430_; uint8_t v_binderInfo_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_binderName_428_ = lean_ctor_get(v_e_331_, 0);
v_binderType_429_ = lean_ctor_get(v_e_331_, 1);
v_body_430_ = lean_ctor_get(v_e_331_, 2);
v_binderInfo_431_ = lean_ctor_get_uint8(v_e_331_, sizeof(void*)*3 + 8);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_331_, v_e_331_, v___x_432_);
v___x_434_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_331_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_433_, v_a_332_, v___x_413_, v_a_334_);
lean_dec_ref_known(v___x_413_, 14);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v_a_436_, v_a_332_);
return v___x_437_;
}
else
{
lean_dec_ref_known(v_e_331_, 3);
return v___x_435_;
}
}
else
{
lean_object* v___x_438_; 
lean_dec_ref(v___x_433_);
lean_inc_ref(v_binderType_429_);
v___x_438_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_429_, v_a_332_, v___x_413_, v_a_334_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
lean_inc_ref(v_body_430_);
v___x_440_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_430_, v_a_332_, v___x_413_, v_a_334_);
lean_dec_ref_known(v___x_413_, 14);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = lean_ptr_addr(v_binderType_429_);
v___x_443_ = lean_ptr_addr(v_a_439_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_inc(v_binderName_428_);
v___y_349_ = v_a_439_;
v___y_350_ = v_a_441_;
v___y_351_ = v_binderInfo_431_;
v___y_352_ = v_binderName_428_;
v___y_353_ = v___x_444_;
goto v___jp_348_;
}
else
{
size_t v___x_445_; size_t v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_ptr_addr(v_body_430_);
v___x_446_ = lean_ptr_addr(v_a_441_);
v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
lean_inc(v_binderName_428_);
v___y_349_ = v_a_439_;
v___y_350_ = v_a_441_;
v___y_351_ = v_binderInfo_431_;
v___y_352_ = v_binderName_428_;
v___y_353_ = v___x_447_;
goto v___jp_348_;
}
}
else
{
lean_dec(v_a_439_);
lean_dec_ref_known(v_e_331_, 3);
return v___x_440_;
}
}
else
{
lean_dec_ref_known(v_e_331_, 3);
lean_dec_ref_known(v___x_413_, 14);
return v___x_438_;
}
}
}
case 8:
{
lean_object* v_declName_448_; lean_object* v_type_449_; lean_object* v_value_450_; lean_object* v_body_451_; uint8_t v_nondep_452_; lean_object* v___x_453_; 
v_declName_448_ = lean_ctor_get(v_e_331_, 0);
v_type_449_ = lean_ctor_get(v_e_331_, 1);
v_value_450_ = lean_ctor_get(v_e_331_, 2);
v_body_451_ = lean_ctor_get(v_e_331_, 3);
v_nondep_452_ = lean_ctor_get_uint8(v_e_331_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_449_);
v___x_453_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_449_, v_a_332_, v___x_413_, v_a_334_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
lean_inc_ref(v_value_450_);
v___x_455_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_450_, v_a_332_, v___x_413_, v_a_334_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
lean_inc_ref(v_body_451_);
v___x_457_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_451_, v_a_332_, v___x_413_, v_a_334_);
lean_dec_ref_known(v___x_413_, 14);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = lean_ptr_addr(v_type_449_);
v___x_460_ = lean_ptr_addr(v_a_454_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_inc_ref(v_body_451_);
lean_inc(v_declName_448_);
v___y_361_ = v_declName_448_;
v___y_362_ = v_a_458_;
v___y_363_ = v_a_454_;
v___y_364_ = v_body_451_;
v___y_365_ = v_a_456_;
v___y_366_ = v_nondep_452_;
v___y_367_ = v___x_461_;
goto v___jp_360_;
}
else
{
size_t v___x_462_; size_t v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_ptr_addr(v_value_450_);
v___x_463_ = lean_ptr_addr(v_a_456_);
v___x_464_ = lean_usize_dec_eq(v___x_462_, v___x_463_);
lean_inc_ref(v_body_451_);
lean_inc(v_declName_448_);
v___y_361_ = v_declName_448_;
v___y_362_ = v_a_458_;
v___y_363_ = v_a_454_;
v___y_364_ = v_body_451_;
v___y_365_ = v_a_456_;
v___y_366_ = v_nondep_452_;
v___y_367_ = v___x_464_;
goto v___jp_360_;
}
}
else
{
lean_dec(v_a_456_);
lean_dec(v_a_454_);
lean_dec_ref_known(v_e_331_, 4);
return v___x_457_;
}
}
else
{
lean_dec(v_a_454_);
lean_dec_ref_known(v_e_331_, 4);
lean_dec_ref_known(v___x_413_, 14);
return v___x_455_;
}
}
else
{
lean_dec_ref_known(v_e_331_, 4);
lean_dec_ref_known(v___x_413_, 14);
return v___x_453_;
}
}
case 5:
{
lean_object* v_fn_465_; lean_object* v_arg_466_; lean_object* v___x_467_; 
v_fn_465_ = lean_ctor_get(v_e_331_, 0);
v_arg_466_ = lean_ctor_get(v_e_331_, 1);
lean_inc_ref(v_fn_465_);
v___x_467_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_465_, v_a_332_, v___x_413_, v_a_334_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
lean_inc_ref(v_arg_466_);
v___x_469_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_466_, v_a_332_, v___x_413_, v_a_334_);
lean_dec_ref_known(v___x_413_, 14);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; size_t v___x_471_; size_t v___x_472_; uint8_t v___x_473_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_ptr_addr(v_fn_465_);
v___x_472_ = lean_ptr_addr(v_a_468_);
v___x_473_ = lean_usize_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
v___y_377_ = v_a_470_;
v___y_378_ = v_a_468_;
v___y_379_ = v___x_473_;
goto v___jp_376_;
}
else
{
size_t v___x_474_; size_t v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_ptr_addr(v_arg_466_);
v___x_475_ = lean_ptr_addr(v_a_470_);
v___x_476_ = lean_usize_dec_eq(v___x_474_, v___x_475_);
v___y_377_ = v_a_470_;
v___y_378_ = v_a_468_;
v___y_379_ = v___x_476_;
goto v___jp_376_;
}
}
else
{
lean_dec(v_a_468_);
lean_dec_ref_known(v_e_331_, 2);
return v___x_469_;
}
}
else
{
lean_dec_ref_known(v_e_331_, 2);
lean_dec_ref_known(v___x_413_, 14);
return v___x_467_;
}
}
case 10:
{
lean_object* v_data_477_; lean_object* v_expr_478_; lean_object* v___x_479_; 
v_data_477_ = lean_ctor_get(v_e_331_, 0);
v_expr_478_ = lean_ctor_get(v_e_331_, 1);
lean_inc_ref(v_expr_478_);
v___x_479_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_478_, v_a_332_, v___x_413_, v_a_334_);
lean_dec_ref_known(v___x_413_, 14);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v___x_481_ = lean_ptr_addr(v_expr_478_);
v___x_482_ = lean_ptr_addr(v_a_480_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v_data_477_);
v___x_484_ = l_Lean_Expr_mdata___override(v_data_477_, v_a_480_);
v___x_485_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_484_, v_a_332_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
lean_dec(v_a_480_);
lean_inc_ref(v_e_331_);
v___x_486_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v_e_331_, v_a_332_);
return v___x_486_;
}
}
else
{
lean_dec_ref_known(v_e_331_, 2);
return v___x_479_;
}
}
case 11:
{
lean_object* v_typeName_487_; lean_object* v_idx_488_; lean_object* v_struct_489_; lean_object* v___x_490_; 
v_typeName_487_ = lean_ctor_get(v_e_331_, 0);
v_idx_488_ = lean_ctor_get(v_e_331_, 1);
v_struct_489_ = lean_ctor_get(v_e_331_, 2);
lean_inc_ref(v_struct_489_);
v___x_490_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_489_, v_a_332_, v___x_413_, v_a_334_);
lean_dec_ref_known(v___x_413_, 14);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_ptr_addr(v_struct_489_);
v___x_493_ = lean_ptr_addr(v_a_491_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc(v_idx_488_);
lean_inc(v_typeName_487_);
v___x_495_ = l_Lean_Expr_proj___override(v_typeName_487_, v_idx_488_, v_a_491_);
v___x_496_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v___x_495_, v_a_332_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; 
lean_dec(v_a_491_);
lean_inc_ref(v_e_331_);
v___x_497_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_331_, v_e_331_, v_a_332_);
return v___x_497_;
}
}
else
{
lean_dec_ref_known(v_e_331_, 3);
return v___x_490_;
}
}
default: 
{
lean_object* v___x_498_; 
lean_dec_ref_known(v___x_413_, 14);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_e_331_);
return v___x_498_;
}
}
}
}
else
{
lean_object* v___x_499_; 
lean_dec_ref(v_e_331_);
lean_inc(v_ref_388_);
v___x_499_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_388_);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object* v_e_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object* v_00_u03b2_510_, lean_object* v_m_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_511_, v_a_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_514_, v_m_515_, v_a_516_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_m_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object* v_00_u03b2_518_, lean_object* v_a_519_, lean_object* v_x_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_519_, v_x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_522_, lean_object* v_a_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_522_, v_a_523_, v_x_524_);
lean_dec(v_x_524_);
lean_dec_ref(v_a_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object* v_e_526_, lean_object* v_c_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_st_mk_ref(v_c_527_);
v___x_532_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_526_, v___x_531_, v_a_528_, v_a_529_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_542_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_st_ref_get(v___x_531_);
lean_dec(v___x_531_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_a_533_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v___x_531_);
v_a_543_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_532_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_532_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object* v_e_551_, lean_object* v_c_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_551_, v_c_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_556_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__1(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_box(0);
v___x_559_ = lean_unsigned_to_nat(16u);
v___x_560_ = lean_mk_array(v___x_559_, v___x_558_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__2(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__1, &l_Lean_Meta_Sym_etaReduceAll___closed__1_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__1);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Meta_Sym_etaReduceAll___closed__0));
v___x_569_ = lean_find_expr(v___x_568_, v_e_564_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v_e_564_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__2, &l_Lean_Meta_Sym_etaReduceAll___closed__2_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__2);
v___x_572_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_564_, v___x_571_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_581_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_581_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_fst_577_; lean_object* v___x_579_; 
v_fst_577_ = lean_ctor_get(v_a_573_, 0);
lean_inc(v_fst_577_);
lean_dec(v_a_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_fst_577_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_fst_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_572_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_572_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Meta_Sym_etaReduceAll(v_e_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_594_;
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
