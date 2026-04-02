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
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(lean_object* v_body_1_, lean_object* v_n_2_, lean_object* v_i_3_, lean_object* v_default_4_){
_start:
{
lean_object* v_zero_5_; uint8_t v_isZero_6_; 
v_zero_5_ = lean_unsigned_to_nat(0u);
v_isZero_6_ = lean_nat_dec_eq(v_n_2_, v_zero_5_);
if (v_isZero_6_ == 1)
{
uint8_t v___x_7_; 
lean_dec(v_i_3_);
lean_dec(v_n_2_);
v___x_7_ = l_Lean_Expr_hasLooseBVars(v_body_1_);
if (v___x_7_ == 0)
{
lean_inc_ref(v_body_1_);
return v_body_1_;
}
else
{
lean_inc_ref(v_default_4_);
return v_default_4_;
}
}
else
{
if (lean_obj_tag(v_body_1_) == 5)
{
lean_object* v_arg_8_; 
v_arg_8_ = lean_ctor_get(v_body_1_, 1);
if (lean_obj_tag(v_arg_8_) == 0)
{
lean_object* v_fn_9_; lean_object* v_deBruijnIndex_10_; uint8_t v___x_11_; 
v_fn_9_ = lean_ctor_get(v_body_1_, 0);
v_deBruijnIndex_10_ = lean_ctor_get(v_arg_8_, 0);
v___x_11_ = lean_nat_dec_eq(v_deBruijnIndex_10_, v_i_3_);
if (v___x_11_ == 0)
{
lean_dec(v_i_3_);
lean_dec(v_n_2_);
lean_inc_ref(v_default_4_);
return v_default_4_;
}
else
{
lean_object* v_one_12_; lean_object* v_n_13_; lean_object* v___x_14_; 
v_one_12_ = lean_unsigned_to_nat(1u);
v_n_13_ = lean_nat_sub(v_n_2_, v_one_12_);
lean_dec(v_n_2_);
v___x_14_ = lean_nat_add(v_i_3_, v_one_12_);
lean_dec(v_i_3_);
v_body_1_ = v_fn_9_;
v_n_2_ = v_n_13_;
v_i_3_ = v___x_14_;
goto _start;
}
}
else
{
lean_dec(v_i_3_);
lean_dec(v_n_2_);
lean_inc_ref(v_default_4_);
return v_default_4_;
}
}
else
{
lean_dec(v_i_3_);
lean_dec(v_n_2_);
lean_inc_ref(v_default_4_);
return v_default_4_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux___boxed(lean_object* v_body_16_, lean_object* v_n_17_, lean_object* v_i_18_, lean_object* v_default_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(v_body_16_, v_n_17_, v_i_18_, v_default_19_);
lean_dec_ref(v_default_19_);
lean_dec_ref(v_body_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(lean_object* v_e_21_, lean_object* v_body_22_, lean_object* v_n_23_){
_start:
{
if (lean_obj_tag(v_body_22_) == 6)
{
lean_object* v_body_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_body_24_ = lean_ctor_get(v_body_22_, 2);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v_n_23_, v___x_25_);
lean_dec(v_n_23_);
v_body_22_ = v_body_24_;
v_n_23_ = v___x_26_;
goto _start;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(v_body_22_, v_n_23_, v___x_28_, v_e_21_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go___boxed(lean_object* v_e_30_, lean_object* v_body_31_, lean_object* v_n_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_30_, v_body_31_, v_n_32_);
lean_dec_ref(v_body_31_);
lean_dec_ref(v_e_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce(lean_object* v_e_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = l_Lean_Expr_isLambda(v_e_34_);
if (v___x_35_ == 0)
{
lean_inc_ref(v_e_34_);
return v_e_34_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_34_, v_e_34_, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce___boxed(lean_object* v_e_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_Sym_etaReduce(v_e_38_);
lean_dec_ref(v_e_38_);
return v_res_39_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isEtaReducible(lean_object* v_e_40_){
_start:
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = l_Lean_Meta_Sym_etaReduce(v_e_40_);
v___x_42_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_40_, v___x_41_);
lean_dec_ref(v___x_41_);
if (v___x_42_ == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 1;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isEtaReducible___boxed(lean_object* v_e_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Meta_Sym_isEtaReducible(v_e_45_);
lean_dec_ref(v_e_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(lean_object* v_a_48_, lean_object* v_b_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_dec(v_b_49_);
lean_dec_ref(v_a_48_);
return v_x_50_;
}
else
{
lean_object* v_key_51_; lean_object* v_value_52_; lean_object* v_tail_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_65_; 
v_key_51_ = lean_ctor_get(v_x_50_, 0);
v_value_52_ = lean_ctor_get(v_x_50_, 1);
v_tail_53_ = lean_ctor_get(v_x_50_, 2);
v_isSharedCheck_65_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_65_ == 0)
{
v___x_55_ = v_x_50_;
v_isShared_56_ = v_isSharedCheck_65_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_tail_53_);
lean_inc(v_value_52_);
lean_inc(v_key_51_);
lean_dec(v_x_50_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_65_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; 
v___x_57_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_51_, v_a_48_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_48_, v_b_49_, v_tail_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 2, v___x_58_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_key_51_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_value_52_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
else
{
lean_object* v___x_63_; 
lean_dec(v_value_52_);
lean_dec(v_key_51_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v_b_49_);
lean_ctor_set(v___x_55_, 0, v_a_48_);
v___x_63_ = v___x_55_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_48_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_b_49_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_tail_53_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
return v_x_66_;
}
else
{
lean_object* v_key_68_; lean_object* v_value_69_; lean_object* v_tail_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_93_; 
v_key_68_ = lean_ctor_get(v_x_67_, 0);
v_value_69_ = lean_ctor_get(v_x_67_, 1);
v_tail_70_ = lean_ctor_get(v_x_67_, 2);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_93_ == 0)
{
v___x_72_ = v_x_67_;
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_tail_70_);
lean_inc(v_value_69_);
lean_inc(v_key_68_);
lean_dec(v_x_67_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v_fold_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_74_ = lean_array_get_size(v_x_66_);
v___x_75_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_68_);
v___x_76_ = 32ULL;
v___x_77_ = lean_uint64_shift_right(v___x_75_, v___x_76_);
v_fold_78_ = lean_uint64_xor(v___x_75_, v___x_77_);
v___x_79_ = 16ULL;
v___x_80_ = lean_uint64_shift_right(v_fold_78_, v___x_79_);
v___x_81_ = lean_uint64_xor(v_fold_78_, v___x_80_);
v___x_82_ = lean_uint64_to_usize(v___x_81_);
v___x_83_ = lean_usize_of_nat(v___x_74_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_sub(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_land(v___x_82_, v___x_85_);
v___x_87_ = lean_array_uget_borrowed(v_x_66_, v___x_86_);
lean_inc(v___x_87_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 2, v___x_87_);
v___x_89_ = v___x_72_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_key_68_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_value_69_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v___x_87_);
v___x_89_ = v_reuseFailAlloc_92_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; 
v___x_90_ = lean_array_uset(v_x_66_, v___x_86_, v___x_89_);
v_x_66_ = v___x_90_;
v_x_67_ = v_tail_70_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(lean_object* v_i_94_, lean_object* v_source_95_, lean_object* v_target_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_array_get_size(v_source_95_);
v___x_98_ = lean_nat_dec_lt(v_i_94_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec_ref(v_source_95_);
lean_dec(v_i_94_);
return v_target_96_;
}
else
{
lean_object* v_es_99_; lean_object* v___x_100_; lean_object* v_source_101_; lean_object* v_target_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_es_99_ = lean_array_fget(v_source_95_, v_i_94_);
v___x_100_ = lean_box(0);
v_source_101_ = lean_array_fset(v_source_95_, v_i_94_, v___x_100_);
v_target_102_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_96_, v_es_99_);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_94_, v___x_103_);
lean_dec(v_i_94_);
v_i_94_ = v___x_104_;
v_source_95_ = v_source_101_;
v_target_96_ = v_target_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(lean_object* v_data_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_nbuckets_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_107_ = lean_array_get_size(v_data_106_);
v___x_108_ = lean_unsigned_to_nat(2u);
v_nbuckets_109_ = lean_nat_mul(v___x_107_, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_box(0);
v___x_112_ = lean_mk_array(v_nbuckets_109_, v___x_111_);
v___x_113_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v___x_110_, v_data_106_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object* v_a_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
else
{
lean_object* v_key_117_; lean_object* v_tail_118_; uint8_t v___x_119_; 
v_key_117_ = lean_ctor_get(v_x_115_, 0);
v_tail_118_ = lean_ctor_get(v_x_115_, 2);
v___x_119_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_117_, v_a_114_);
if (v___x_119_ == 0)
{
v_x_115_ = v_tail_118_;
goto _start;
}
else
{
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_121_, v_x_122_);
lean_dec(v_x_122_);
lean_dec_ref(v_a_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object* v_m_125_, lean_object* v_a_126_, lean_object* v_b_127_){
_start:
{
lean_object* v_size_128_; lean_object* v_buckets_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_172_; 
v_size_128_ = lean_ctor_get(v_m_125_, 0);
v_buckets_129_ = lean_ctor_get(v_m_125_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_m_125_);
if (v_isSharedCheck_172_ == 0)
{
v___x_131_ = v_m_125_;
v_isShared_132_ = v_isSharedCheck_172_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_buckets_129_);
lean_inc(v_size_128_);
lean_dec(v_m_125_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_172_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v_fold_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v_bkt_146_; uint8_t v___x_147_; 
v___x_133_ = lean_array_get_size(v_buckets_129_);
v___x_134_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_126_);
v___x_135_ = 32ULL;
v___x_136_ = lean_uint64_shift_right(v___x_134_, v___x_135_);
v_fold_137_ = lean_uint64_xor(v___x_134_, v___x_136_);
v___x_138_ = 16ULL;
v___x_139_ = lean_uint64_shift_right(v_fold_137_, v___x_138_);
v___x_140_ = lean_uint64_xor(v_fold_137_, v___x_139_);
v___x_141_ = lean_uint64_to_usize(v___x_140_);
v___x_142_ = lean_usize_of_nat(v___x_133_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_sub(v___x_142_, v___x_143_);
v___x_145_ = lean_usize_land(v___x_141_, v___x_144_);
v_bkt_146_ = lean_array_uget_borrowed(v_buckets_129_, v___x_145_);
v___x_147_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_126_, v_bkt_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v_size_x27_149_; lean_object* v___x_150_; lean_object* v_buckets_x27_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v_size_x27_149_ = lean_nat_add(v_size_128_, v___x_148_);
lean_dec(v_size_128_);
lean_inc(v_bkt_146_);
v___x_150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_150_, 0, v_a_126_);
lean_ctor_set(v___x_150_, 1, v_b_127_);
lean_ctor_set(v___x_150_, 2, v_bkt_146_);
v_buckets_x27_151_ = lean_array_uset(v_buckets_129_, v___x_145_, v___x_150_);
v___x_152_ = lean_unsigned_to_nat(4u);
v___x_153_ = lean_nat_mul(v_size_x27_149_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(3u);
v___x_155_ = lean_nat_div(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_array_get_size(v_buckets_x27_151_);
v___x_157_ = lean_nat_dec_le(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v_val_158_; lean_object* v___x_160_; 
v_val_158_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_buckets_x27_151_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_val_158_);
lean_ctor_set(v___x_131_, 0, v_size_x27_149_);
v___x_160_ = v___x_131_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_size_x27_149_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_val_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
else
{
lean_object* v___x_163_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_buckets_x27_151_);
lean_ctor_set(v___x_131_, 0, v_size_x27_149_);
v___x_163_ = v___x_131_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_size_x27_149_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_buckets_x27_151_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
else
{
lean_object* v___x_165_; lean_object* v_buckets_x27_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
lean_inc(v_bkt_146_);
v___x_165_ = lean_box(0);
v_buckets_x27_166_ = lean_array_uset(v_buckets_129_, v___x_145_, v___x_165_);
v___x_167_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_126_, v_b_127_, v_bkt_146_);
v___x_168_ = lean_array_uset(v_buckets_x27_166_, v___x_145_, v___x_167_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_168_);
v___x_170_ = v___x_131_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_128_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object* v_e_173_, lean_object* v_e_x27_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = lean_st_ref_take(v_a_175_);
lean_inc_ref(v_e_x27_174_);
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_177_, v_e_173_, v_e_x27_174_);
v___x_179_ = lean_st_ref_set(v_a_175_, v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v_e_x27_174_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object* v_e_181_, lean_object* v_e_x27_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_181_, v_e_x27_182_, v_a_183_);
lean_dec(v_a_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object* v_e_186_, lean_object* v_e_x27_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_186_, v_e_x27_187_, v_a_188_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object* v_e_193_, lean_object* v_e_x27_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_193_, v_e_x27_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object* v_00_u03b2_200_, lean_object* v_m_201_, lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_201_, v_a_202_, v_b_203_);
return v___x_204_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object* v_00_u03b2_205_, lean_object* v_a_206_, lean_object* v_x_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_206_, v_x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_209_, lean_object* v_a_210_, lean_object* v_x_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_209_, v_a_210_, v_x_211_);
lean_dec(v_x_211_);
lean_dec_ref(v_a_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(lean_object* v_00_u03b2_214_, lean_object* v_data_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_data_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(lean_object* v_00_u03b2_217_, lean_object* v_a_218_, lean_object* v_b_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_218_, v_b_219_, v_x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_222_, lean_object* v_i_223_, lean_object* v_source_224_, lean_object* v_target_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v_i_223_, v_source_224_, v_target_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_228_, v_x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = l_Lean_maxRecDepthErrorMessage;
v___x_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
v___x_239_ = l_Lean_MessageData_ofFormat(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
v___x_241_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2));
v___x_242_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object* v_ref_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_ref_243_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object* v_ref_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object* v_00_u03b1_251_, lean_object* v_ref_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_252_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object* v_00_u03b1_258_, lean_object* v_ref_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_258_, v_ref_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object* v_a_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
else
{
lean_object* v_key_268_; lean_object* v_value_269_; lean_object* v_tail_270_; uint8_t v___x_271_; 
v_key_268_ = lean_ctor_get(v_x_266_, 0);
v_value_269_ = lean_ctor_get(v_x_266_, 1);
v_tail_270_ = lean_ctor_get(v_x_266_, 2);
v___x_271_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_268_, v_a_265_);
if (v___x_271_ == 0)
{
v_x_266_ = v_tail_270_;
goto _start;
}
else
{
lean_object* v___x_273_; 
lean_inc(v_value_269_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v_value_269_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_274_, v_x_275_);
lean_dec(v_x_275_);
lean_dec_ref(v_a_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object* v_m_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_buckets_279_; lean_object* v___x_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v_fold_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_buckets_279_ = lean_ctor_get(v_m_277_, 1);
v___x_280_ = lean_array_get_size(v_buckets_279_);
v___x_281_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_278_);
v___x_282_ = 32ULL;
v___x_283_ = lean_uint64_shift_right(v___x_281_, v___x_282_);
v_fold_284_ = lean_uint64_xor(v___x_281_, v___x_283_);
v___x_285_ = 16ULL;
v___x_286_ = lean_uint64_shift_right(v_fold_284_, v___x_285_);
v___x_287_ = lean_uint64_xor(v_fold_284_, v___x_286_);
v___x_288_ = lean_uint64_to_usize(v___x_287_);
v___x_289_ = lean_usize_of_nat(v___x_280_);
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_sub(v___x_289_, v___x_290_);
v___x_292_ = lean_usize_land(v___x_288_, v___x_291_);
v___x_293_ = lean_array_uget_borrowed(v_buckets_279_, v___x_292_);
v___x_294_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_278_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object* v_m_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_295_, v_a_296_);
lean_dec_ref(v_a_296_);
lean_dec_ref(v_m_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
uint8_t v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; uint8_t v___y_308_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; uint8_t v___y_320_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; uint8_t v___y_333_; uint8_t v___y_334_; lean_object* v___y_344_; lean_object* v___y_345_; uint8_t v___y_346_; lean_object* v_fileName_350_; lean_object* v_fileMap_351_; lean_object* v_options_352_; lean_object* v_currRecDepth_353_; lean_object* v_maxRecDepth_354_; lean_object* v_ref_355_; lean_object* v_currNamespace_356_; lean_object* v_openDecls_357_; lean_object* v_initHeartbeats_358_; lean_object* v_maxHeartbeats_359_; lean_object* v_quotContext_360_; lean_object* v_currMacroScope_361_; uint8_t v_diag_362_; lean_object* v_cancelTk_x3f_363_; uint8_t v_suppressElabErrors_364_; lean_object* v_inheritedTraceOptions_365_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_fileName_350_ = lean_ctor_get(v_a_300_, 0);
v_fileMap_351_ = lean_ctor_get(v_a_300_, 1);
v_options_352_ = lean_ctor_get(v_a_300_, 2);
v_currRecDepth_353_ = lean_ctor_get(v_a_300_, 3);
v_maxRecDepth_354_ = lean_ctor_get(v_a_300_, 4);
v_ref_355_ = lean_ctor_get(v_a_300_, 5);
v_currNamespace_356_ = lean_ctor_get(v_a_300_, 6);
v_openDecls_357_ = lean_ctor_get(v_a_300_, 7);
v_initHeartbeats_358_ = lean_ctor_get(v_a_300_, 8);
v_maxHeartbeats_359_ = lean_ctor_get(v_a_300_, 9);
v_quotContext_360_ = lean_ctor_get(v_a_300_, 10);
v_currMacroScope_361_ = lean_ctor_get(v_a_300_, 11);
v_diag_362_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*14);
v_cancelTk_x3f_363_ = lean_ctor_get(v_a_300_, 12);
v_suppressElabErrors_364_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_365_ = lean_ctor_get(v_a_300_, 13);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_nat_dec_eq(v_maxRecDepth_354_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = lean_nat_dec_eq(v_currRecDepth_353_, v_maxRecDepth_354_);
if (v___x_467_ == 0)
{
goto v___jp_366_;
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v_e_298_);
lean_inc(v_ref_355_);
v___x_468_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_355_);
return v___x_468_;
}
}
else
{
goto v___jp_366_;
}
v___jp_303_:
{
if (v___y_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = l_Lean_Expr_forallE___override(v___y_307_, v___y_305_, v___y_306_, v___y_304_);
v___x_310_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_309_, v_a_299_);
return v___x_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = l_Lean_instBEqBinderInfo_beq(v___y_304_, v___y_304_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = l_Lean_Expr_forallE___override(v___y_307_, v___y_305_, v___y_306_, v___y_304_);
v___x_313_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_312_, v_a_299_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v___y_305_);
lean_inc_ref(v_e_298_);
v___x_314_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v_e_298_, v_a_299_);
return v___x_314_;
}
}
}
v___jp_315_:
{
if (v___y_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l_Lean_Expr_lam___override(v___y_319_, v___y_318_, v___y_316_, v___y_317_);
v___x_322_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_321_, v_a_299_);
return v___x_322_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_instBEqBinderInfo_beq(v___y_317_, v___y_317_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = l_Lean_Expr_lam___override(v___y_319_, v___y_318_, v___y_316_, v___y_317_);
v___x_325_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_324_, v_a_299_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; 
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v___y_316_);
lean_inc_ref(v_e_298_);
v___x_326_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v_e_298_, v_a_299_);
return v___x_326_;
}
}
}
v___jp_327_:
{
if (v___y_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v___y_332_);
v___x_335_ = l_Lean_Expr_letE___override(v___y_329_, v___y_328_, v___y_331_, v___y_330_, v___y_333_);
v___x_336_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_335_, v_a_299_);
return v___x_336_;
}
else
{
size_t v___x_337_; size_t v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_ptr_addr(v___y_332_);
lean_dec_ref(v___y_332_);
v___x_338_ = lean_ptr_addr(v___y_330_);
v___x_339_ = lean_usize_dec_eq(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_Lean_Expr_letE___override(v___y_329_, v___y_328_, v___y_331_, v___y_330_, v___y_333_);
v___x_341_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_340_, v_a_299_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
lean_dec_ref(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_inc_ref(v_e_298_);
v___x_342_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v_e_298_, v_a_299_);
return v___x_342_;
}
}
}
v___jp_343_:
{
if (v___y_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = l_Lean_Expr_app___override(v___y_344_, v___y_345_);
v___x_348_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_347_, v_a_299_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
lean_dec_ref(v___y_345_);
lean_dec_ref(v___y_344_);
lean_inc_ref(v_e_298_);
v___x_349_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v_e_298_, v_a_299_);
return v___x_349_;
}
}
v___jp_366_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_st_ref_get(v_a_299_);
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_367_, v_e_298_);
lean_dec(v___x_367_);
if (lean_obj_tag(v___x_368_) == 1)
{
lean_object* v_val_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v_e_298_);
v_val_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_val_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 0);
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_val_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v___x_368_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_currRecDepth_353_, v___x_377_);
lean_inc_ref(v_inheritedTraceOptions_365_);
lean_inc(v_cancelTk_x3f_363_);
lean_inc(v_currMacroScope_361_);
lean_inc(v_quotContext_360_);
lean_inc(v_maxHeartbeats_359_);
lean_inc(v_initHeartbeats_358_);
lean_inc(v_openDecls_357_);
lean_inc(v_currNamespace_356_);
lean_inc(v_ref_355_);
lean_inc(v_maxRecDepth_354_);
lean_inc_ref(v_options_352_);
lean_inc_ref(v_fileMap_351_);
lean_inc_ref(v_fileName_350_);
v___x_379_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_379_, 0, v_fileName_350_);
lean_ctor_set(v___x_379_, 1, v_fileMap_351_);
lean_ctor_set(v___x_379_, 2, v_options_352_);
lean_ctor_set(v___x_379_, 3, v___x_378_);
lean_ctor_set(v___x_379_, 4, v_maxRecDepth_354_);
lean_ctor_set(v___x_379_, 5, v_ref_355_);
lean_ctor_set(v___x_379_, 6, v_currNamespace_356_);
lean_ctor_set(v___x_379_, 7, v_openDecls_357_);
lean_ctor_set(v___x_379_, 8, v_initHeartbeats_358_);
lean_ctor_set(v___x_379_, 9, v_maxHeartbeats_359_);
lean_ctor_set(v___x_379_, 10, v_quotContext_360_);
lean_ctor_set(v___x_379_, 11, v_currMacroScope_361_);
lean_ctor_set(v___x_379_, 12, v_cancelTk_x3f_363_);
lean_ctor_set(v___x_379_, 13, v_inheritedTraceOptions_365_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*14, v_diag_362_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*14 + 1, v_suppressElabErrors_364_);
switch(lean_obj_tag(v_e_298_))
{
case 7:
{
lean_object* v_binderName_380_; lean_object* v_binderType_381_; lean_object* v_body_382_; uint8_t v_binderInfo_383_; lean_object* v___x_384_; 
v_binderName_380_ = lean_ctor_get(v_e_298_, 0);
v_binderType_381_ = lean_ctor_get(v_e_298_, 1);
v_body_382_ = lean_ctor_get(v_e_298_, 2);
v_binderInfo_383_ = lean_ctor_get_uint8(v_e_298_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_381_);
v___x_384_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_381_, v_a_299_, v___x_379_, v_a_301_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_384_);
lean_inc_ref(v_body_382_);
v___x_386_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_382_, v_a_299_, v___x_379_, v_a_301_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; size_t v___x_388_; size_t v___x_389_; uint8_t v___x_390_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_386_);
v___x_388_ = lean_ptr_addr(v_binderType_381_);
v___x_389_ = lean_ptr_addr(v_a_385_);
v___x_390_ = lean_usize_dec_eq(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_inc(v_binderName_380_);
v___y_304_ = v_binderInfo_383_;
v___y_305_ = v_a_385_;
v___y_306_ = v_a_387_;
v___y_307_ = v_binderName_380_;
v___y_308_ = v___x_390_;
goto v___jp_303_;
}
else
{
size_t v___x_391_; size_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_ptr_addr(v_body_382_);
v___x_392_ = lean_ptr_addr(v_a_387_);
v___x_393_ = lean_usize_dec_eq(v___x_391_, v___x_392_);
lean_inc(v_binderName_380_);
v___y_304_ = v_binderInfo_383_;
v___y_305_ = v_a_385_;
v___y_306_ = v_a_387_;
v___y_307_ = v_binderName_380_;
v___y_308_ = v___x_393_;
goto v___jp_303_;
}
}
else
{
lean_dec(v_a_385_);
lean_dec_ref(v_e_298_);
return v___x_386_;
}
}
else
{
lean_dec_ref(v_e_298_);
lean_dec_ref(v___x_379_);
return v___x_384_;
}
}
case 6:
{
lean_object* v_binderName_394_; lean_object* v_binderType_395_; lean_object* v_body_396_; uint8_t v_binderInfo_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_binderName_394_ = lean_ctor_get(v_e_298_, 0);
v_binderType_395_ = lean_ctor_get(v_e_298_, 1);
v_body_396_ = lean_ctor_get(v_e_298_, 2);
v_binderInfo_397_ = lean_ctor_get_uint8(v_e_298_, sizeof(void*)*3 + 8);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_298_, v_e_298_, v___x_398_);
v___x_400_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_298_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_399_, v_a_299_, v___x_379_, v_a_301_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref(v___x_401_);
v___x_403_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v_a_402_, v_a_299_);
return v___x_403_;
}
else
{
lean_dec_ref(v_e_298_);
return v___x_401_;
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v___x_399_);
lean_inc_ref(v_binderType_395_);
v___x_404_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_395_, v_a_299_, v___x_379_, v_a_301_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref(v___x_404_);
lean_inc_ref(v_body_396_);
v___x_406_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_396_, v_a_299_, v___x_379_, v_a_301_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref(v___x_406_);
v___x_408_ = lean_ptr_addr(v_binderType_395_);
v___x_409_ = lean_ptr_addr(v_a_405_);
v___x_410_ = lean_usize_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_inc(v_binderName_394_);
v___y_316_ = v_a_407_;
v___y_317_ = v_binderInfo_397_;
v___y_318_ = v_a_405_;
v___y_319_ = v_binderName_394_;
v___y_320_ = v___x_410_;
goto v___jp_315_;
}
else
{
size_t v___x_411_; size_t v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_ptr_addr(v_body_396_);
v___x_412_ = lean_ptr_addr(v_a_407_);
v___x_413_ = lean_usize_dec_eq(v___x_411_, v___x_412_);
lean_inc(v_binderName_394_);
v___y_316_ = v_a_407_;
v___y_317_ = v_binderInfo_397_;
v___y_318_ = v_a_405_;
v___y_319_ = v_binderName_394_;
v___y_320_ = v___x_413_;
goto v___jp_315_;
}
}
else
{
lean_dec(v_a_405_);
lean_dec_ref(v_e_298_);
return v___x_406_;
}
}
else
{
lean_dec_ref(v_e_298_);
lean_dec_ref(v___x_379_);
return v___x_404_;
}
}
}
case 8:
{
lean_object* v_declName_414_; lean_object* v_type_415_; lean_object* v_value_416_; lean_object* v_body_417_; uint8_t v_nondep_418_; lean_object* v___x_419_; 
v_declName_414_ = lean_ctor_get(v_e_298_, 0);
v_type_415_ = lean_ctor_get(v_e_298_, 1);
v_value_416_ = lean_ctor_get(v_e_298_, 2);
v_body_417_ = lean_ctor_get(v_e_298_, 3);
v_nondep_418_ = lean_ctor_get_uint8(v_e_298_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_415_);
v___x_419_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_415_, v_a_299_, v___x_379_, v_a_301_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref(v___x_419_);
lean_inc_ref(v_value_416_);
v___x_421_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_416_, v_a_299_, v___x_379_, v_a_301_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref(v___x_421_);
lean_inc_ref(v_body_417_);
v___x_423_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_417_, v_a_299_, v___x_379_, v_a_301_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; size_t v___x_425_; size_t v___x_426_; uint8_t v___x_427_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v___x_423_);
v___x_425_ = lean_ptr_addr(v_type_415_);
v___x_426_ = lean_ptr_addr(v_a_420_);
v___x_427_ = lean_usize_dec_eq(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_inc_ref(v_body_417_);
lean_inc(v_declName_414_);
v___y_328_ = v_a_420_;
v___y_329_ = v_declName_414_;
v___y_330_ = v_a_424_;
v___y_331_ = v_a_422_;
v___y_332_ = v_body_417_;
v___y_333_ = v_nondep_418_;
v___y_334_ = v___x_427_;
goto v___jp_327_;
}
else
{
size_t v___x_428_; size_t v___x_429_; uint8_t v___x_430_; 
v___x_428_ = lean_ptr_addr(v_value_416_);
v___x_429_ = lean_ptr_addr(v_a_422_);
v___x_430_ = lean_usize_dec_eq(v___x_428_, v___x_429_);
lean_inc_ref(v_body_417_);
lean_inc(v_declName_414_);
v___y_328_ = v_a_420_;
v___y_329_ = v_declName_414_;
v___y_330_ = v_a_424_;
v___y_331_ = v_a_422_;
v___y_332_ = v_body_417_;
v___y_333_ = v_nondep_418_;
v___y_334_ = v___x_430_;
goto v___jp_327_;
}
}
else
{
lean_dec(v_a_422_);
lean_dec(v_a_420_);
lean_dec_ref(v_e_298_);
return v___x_423_;
}
}
else
{
lean_dec(v_a_420_);
lean_dec_ref(v_e_298_);
lean_dec_ref(v___x_379_);
return v___x_421_;
}
}
else
{
lean_dec_ref(v_e_298_);
lean_dec_ref(v___x_379_);
return v___x_419_;
}
}
case 5:
{
lean_object* v_fn_431_; lean_object* v_arg_432_; lean_object* v___x_433_; 
v_fn_431_ = lean_ctor_get(v_e_298_, 0);
v_arg_432_ = lean_ctor_get(v_e_298_, 1);
lean_inc_ref(v_fn_431_);
v___x_433_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_431_, v_a_299_, v___x_379_, v_a_301_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref(v___x_433_);
lean_inc_ref(v_arg_432_);
v___x_435_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_432_, v_a_299_, v___x_379_, v_a_301_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; size_t v___x_437_; size_t v___x_438_; uint8_t v___x_439_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v___x_435_);
v___x_437_ = lean_ptr_addr(v_fn_431_);
v___x_438_ = lean_ptr_addr(v_a_434_);
v___x_439_ = lean_usize_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
v___y_344_ = v_a_434_;
v___y_345_ = v_a_436_;
v___y_346_ = v___x_439_;
goto v___jp_343_;
}
else
{
size_t v___x_440_; size_t v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_ptr_addr(v_arg_432_);
v___x_441_ = lean_ptr_addr(v_a_436_);
v___x_442_ = lean_usize_dec_eq(v___x_440_, v___x_441_);
v___y_344_ = v_a_434_;
v___y_345_ = v_a_436_;
v___y_346_ = v___x_442_;
goto v___jp_343_;
}
}
else
{
lean_dec(v_a_434_);
lean_dec_ref(v_e_298_);
return v___x_435_;
}
}
else
{
lean_dec_ref(v_e_298_);
lean_dec_ref(v___x_379_);
return v___x_433_;
}
}
case 10:
{
lean_object* v_data_443_; lean_object* v_expr_444_; lean_object* v___x_445_; 
v_data_443_ = lean_ctor_get(v_e_298_, 0);
v_expr_444_ = lean_ctor_get(v_e_298_, 1);
lean_inc_ref(v_expr_444_);
v___x_445_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_444_, v_a_299_, v___x_379_, v_a_301_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; size_t v___x_447_; size_t v___x_448_; uint8_t v___x_449_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
v___x_447_ = lean_ptr_addr(v_expr_444_);
v___x_448_ = lean_ptr_addr(v_a_446_);
v___x_449_ = lean_usize_dec_eq(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc(v_data_443_);
v___x_450_ = l_Lean_Expr_mdata___override(v_data_443_, v_a_446_);
v___x_451_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_450_, v_a_299_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; 
lean_dec(v_a_446_);
lean_inc_ref(v_e_298_);
v___x_452_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v_e_298_, v_a_299_);
return v___x_452_;
}
}
else
{
lean_dec_ref(v_e_298_);
return v___x_445_;
}
}
case 11:
{
lean_object* v_typeName_453_; lean_object* v_idx_454_; lean_object* v_struct_455_; lean_object* v___x_456_; 
v_typeName_453_ = lean_ctor_get(v_e_298_, 0);
v_idx_454_ = lean_ctor_get(v_e_298_, 1);
v_struct_455_ = lean_ctor_get(v_e_298_, 2);
lean_inc_ref(v_struct_455_);
v___x_456_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_455_, v_a_299_, v___x_379_, v_a_301_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; size_t v___x_458_; size_t v___x_459_; uint8_t v___x_460_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___x_458_ = lean_ptr_addr(v_struct_455_);
v___x_459_ = lean_ptr_addr(v_a_457_);
v___x_460_ = lean_usize_dec_eq(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_inc(v_idx_454_);
lean_inc(v_typeName_453_);
v___x_461_ = l_Lean_Expr_proj___override(v_typeName_453_, v_idx_454_, v_a_457_);
v___x_462_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v___x_461_, v_a_299_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v_a_457_);
lean_inc_ref(v_e_298_);
v___x_463_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_298_, v_e_298_, v_a_299_);
return v___x_463_;
}
}
else
{
lean_dec_ref(v_e_298_);
return v___x_456_;
}
}
default: 
{
lean_object* v___x_464_; 
lean_dec_ref(v___x_379_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_e_298_);
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object* v_e_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object* v_00_u03b2_475_, lean_object* v_m_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_476_, v_a_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object* v_00_u03b2_479_, lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_479_, v_m_480_, v_a_481_);
lean_dec_ref(v_a_481_);
lean_dec_ref(v_m_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object* v_00_u03b2_483_, lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_a_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_487_, v_a_488_, v_x_489_);
lean_dec(v_x_489_);
lean_dec_ref(v_a_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object* v_e_491_, lean_object* v_c_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_st_mk_ref(v_c_492_);
v___x_497_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_491_, v___x_496_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_507_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = lean_st_ref_get(v___x_496_);
lean_dec(v___x_496_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_a_498_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_503_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v___x_496_);
v_a_508_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_497_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_497_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object* v_e_516_, lean_object* v_c_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_516_, v_c_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
return v_res_521_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__1(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_unsigned_to_nat(16u);
v___x_525_ = lean_mk_array(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__2(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__1, &l_Lean_Meta_Sym_etaReduceAll___closed__1_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__1);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object* v_e_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Meta_Sym_etaReduceAll___closed__0));
v___x_534_ = lean_find_expr(v___x_533_, v_e_529_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v_e_529_);
return v___x_535_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__2, &l_Lean_Meta_Sym_etaReduceAll___closed__2_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__2);
v___x_537_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_529_, v___x_536_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_fst_542_; lean_object* v___x_544_; 
v_fst_542_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_fst_542_);
lean_dec(v_a_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v_fst_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_fst_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_537_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_537_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object* v_e_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_Sym_etaReduceAll(v_e_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_559_;
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
