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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_etaReduceAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_isEtaReducible___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_etaReduceAll___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_etaReduceAll___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_etaReduceAll___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_etaReduceAll___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_etaReduceAll___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_etaReduceAll___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_etaReduceAll___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_etaReduceAll___closed__3;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object* v_m_84_, lean_object* v_query_85_, lean_object* v_x_86_, lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_zero_89_; uint8_t v_isZero_90_; 
v_zero_89_ = lean_unsigned_to_nat(0u);
v_isZero_90_ = lean_nat_dec_eq(v_x_87_, v_zero_89_);
if (v_isZero_90_ == 1)
{
lean_dec(v_x_88_);
lean_dec(v_x_87_);
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(2);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_val_92_ = lean_ctor_get(v_x_86_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v_x_86_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_val_92_);
lean_dec(v_x_86_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_val_92_);
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
else
{
lean_object* v_keyArray_100_; lean_object* v_valueArray_101_; lean_object* v___x_102_; uint8_t v_isSome_103_; 
v_keyArray_100_ = lean_ctor_get(v_m_84_, 1);
v_valueArray_101_ = lean_ctor_get(v_m_84_, 2);
v___x_102_ = lean_array_fget_borrowed(v_keyArray_100_, v_x_88_);
v_isSome_103_ = lean_noption_is_some(v___x_102_);
if (v_isSome_103_ == 0)
{
lean_dec(v_x_87_);
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_x_88_);
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec(v_x_88_);
v_val_105_ = lean_ctor_get(v_x_86_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v_x_86_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_val_105_);
lean_dec(v_x_86_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_val_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v_one_113_; lean_object* v_n_114_; lean_object* v___y_116_; 
v_one_113_ = lean_unsigned_to_nat(1u);
v_n_114_ = lean_nat_sub(v_x_87_, v_one_113_);
lean_dec(v_x_87_);
if (v_isSome_103_ == 0)
{
goto v___jp_122_;
}
else
{
lean_object* v___x_124_; uint8_t v_isSome_125_; 
v___x_124_ = lean_array_fget_borrowed(v_valueArray_101_, v_x_88_);
v_isSome_125_ = lean_noption_is_some(v___x_124_);
if (v_isSome_125_ == 0)
{
goto v___jp_122_;
}
else
{
lean_object* v_val_126_; size_t v___x_127_; size_t v___x_128_; uint8_t v___x_129_; 
lean_inc(v___x_102_);
v_val_126_ = lean_noption_get(v___x_102_);
v___x_127_ = lean_ptr_addr(v_val_126_);
v___x_128_ = lean_ptr_addr(v_query_85_);
v___x_129_ = lean_usize_dec_eq(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
lean_dec(v_val_126_);
v___x_130_ = lean_array_get_size(v_keyArray_100_);
v___x_131_ = lean_nat_add(v_x_88_, v_one_113_);
lean_dec(v_x_88_);
v___x_132_ = lean_nat_dec_lt(v___x_131_, v___x_130_);
if (v___x_132_ == 0)
{
lean_dec(v___x_131_);
v_x_87_ = v_n_114_;
v_x_88_ = v_zero_89_;
goto _start;
}
else
{
v_x_87_ = v_n_114_;
v_x_88_ = v___x_131_;
goto _start;
}
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; 
lean_dec(v_n_114_);
lean_dec(v_x_86_);
lean_inc(v___x_124_);
v_val_135_ = lean_noption_get(v___x_124_);
v___x_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_136_, 0, v_x_88_);
lean_ctor_set(v___x_136_, 1, v_val_126_);
lean_ctor_set(v___x_136_, 2, v_val_135_);
return v___x_136_;
}
}
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_array_get_size(v_keyArray_100_);
v___x_118_ = lean_nat_add(v_x_88_, v_one_113_);
lean_dec(v_x_88_);
v___x_119_ = lean_nat_dec_lt(v___x_118_, v___x_117_);
if (v___x_119_ == 0)
{
lean_dec(v___x_118_);
v_x_86_ = v___y_116_;
v_x_87_ = v_n_114_;
v_x_88_ = v_zero_89_;
goto _start;
}
else
{
v_x_86_ = v___y_116_;
v_x_87_ = v_n_114_;
v_x_88_ = v___x_118_;
goto _start;
}
}
v___jp_122_:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_123_; 
lean_inc(v_x_88_);
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_x_88_);
v___y_116_ = v___x_123_;
goto v___jp_115_;
}
else
{
v___y_116_ = v_x_86_;
goto v___jp_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object* v_m_137_, lean_object* v_query_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_m_137_, v_query_138_, v_x_139_, v_x_140_, v_x_141_);
lean_dec_ref(v_query_138_);
lean_dec_ref(v_m_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object* v_m_143_, lean_object* v_query_144_){
_start:
{
lean_object* v_keyArray_145_; lean_object* v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v_fold_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_keyArray_145_ = lean_ctor_get(v_m_143_, 1);
v___x_146_ = lean_array_get_size(v_keyArray_145_);
v___x_147_ = lean_ptr_addr(v_query_144_);
v___x_148_ = ((size_t)3ULL);
v___x_149_ = lean_usize_shift_right(v___x_147_, v___x_148_);
v___x_150_ = lean_usize_to_uint64(v___x_149_);
v___x_151_ = 32ULL;
v___x_152_ = lean_uint64_shift_right(v___x_150_, v___x_151_);
v_fold_153_ = lean_uint64_xor(v___x_150_, v___x_152_);
v___x_154_ = 16ULL;
v___x_155_ = lean_uint64_shift_right(v_fold_153_, v___x_154_);
v___x_156_ = lean_uint64_xor(v_fold_153_, v___x_155_);
v___x_157_ = lean_uint64_to_usize(v___x_156_);
v___x_158_ = lean_usize_of_nat(v___x_146_);
v___x_159_ = ((size_t)1ULL);
v___x_160_ = lean_usize_sub(v___x_158_, v___x_159_);
v___x_161_ = lean_usize_land(v___x_157_, v___x_160_);
v___x_162_ = lean_usize_to_nat(v___x_161_);
v___x_163_ = lean_box(0);
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_m_143_, v_query_144_, v___x_163_, v___x_146_, v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg___boxed(lean_object* v_m_165_, lean_object* v_query_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_165_, v_query_166_);
lean_dec_ref(v_query_166_);
lean_dec_ref(v_m_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___redArg(lean_object* v_b_168_, lean_object* v_acc_169_, lean_object* v_i_170_){
_start:
{
lean_object* v___y_172_; lean_object* v_keyArray_180_; lean_object* v_valueArray_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_keyArray_180_ = lean_ctor_get(v_b_168_, 1);
v_valueArray_181_ = lean_ctor_get(v_b_168_, 2);
v___x_182_ = lean_array_get_size(v_keyArray_180_);
v___x_183_ = lean_nat_dec_lt(v_i_170_, v___x_182_);
if (v___x_183_ == 0)
{
lean_dec(v_i_170_);
return v_acc_169_;
}
else
{
lean_object* v___x_184_; uint8_t v_isSome_185_; 
v___x_184_ = lean_array_fget_borrowed(v_keyArray_180_, v_i_170_);
v_isSome_185_ = lean_noption_is_some(v___x_184_);
if (v_isSome_185_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_186_; uint8_t v_isSome_187_; 
v___x_186_ = lean_array_fget_borrowed(v_valueArray_181_, v_i_170_);
v_isSome_187_ = lean_noption_is_some(v___x_186_);
if (v_isSome_187_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v_val_188_; lean_object* v_val_189_; lean_object* v_i_191_; lean_object* v___x_196_; 
lean_inc(v___x_184_);
v_val_188_ = lean_noption_get(v___x_184_);
lean_inc(v___x_186_);
v_val_189_ = lean_noption_get(v___x_186_);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_acc_169_, v_val_188_);
switch(lean_obj_tag(v___x_196_))
{
case 0:
{
lean_object* v_index_197_; lean_object* v_size_198_; lean_object* v___x_199_; 
v_index_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_197_);
lean_dec_ref_known(v___x_196_, 3);
v_size_198_ = lean_ctor_get(v_acc_169_, 0);
lean_inc(v_size_198_);
v___x_199_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_169_, v_size_198_, v_index_197_, v_val_188_, v_val_189_);
lean_dec(v_index_197_);
v___y_172_ = v___x_199_;
goto v___jp_171_;
}
case 1:
{
lean_object* v_index_200_; 
v_index_200_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_196_, 1);
v_i_191_ = v_index_200_;
goto v___jp_190_;
}
default: 
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_169_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_index_203_; 
v_index_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_index_203_);
lean_dec_ref_known(v___x_202_, 1);
v_i_191_ = v_index_203_;
goto v___jp_190_;
}
else
{
lean_dec(v_val_189_);
lean_dec(v_val_188_);
v___y_172_ = v_acc_169_;
goto v___jp_171_;
}
}
}
v___jp_190_:
{
lean_object* v_size_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_size_192_ = lean_ctor_get(v_acc_169_, 0);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_size_192_, v___x_193_);
v___x_195_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_169_, v___x_194_, v_i_191_, v_val_188_, v_val_189_);
lean_dec(v_i_191_);
v___y_172_ = v___x_195_;
goto v___jp_171_;
}
}
}
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_i_170_, v___x_173_);
lean_dec(v_i_170_);
v_acc_169_ = v___y_172_;
v_i_170_ = v___x_174_;
goto _start;
}
v___jp_176_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_i_170_, v___x_177_);
lean_dec(v_i_170_);
v_i_170_ = v___x_178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_204_, lean_object* v_acc_205_, lean_object* v_i_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___redArg(v_b_204_, v_acc_205_, v_i_206_);
lean_dec_ref(v_b_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___redArg(lean_object* v_init_208_, lean_object* v_b_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___redArg(v_b_209_, v_init_208_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___redArg___boxed(lean_object* v_init_212_, lean_object* v_b_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___redArg(v_init_212_, v_b_213_);
lean_dec_ref(v_b_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg(lean_object* v_m_215_){
_start:
{
lean_object* v_keyArray_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_cellCount_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_target_223_; lean_object* v___x_224_; 
v_keyArray_216_ = lean_ctor_get(v_m_215_, 1);
v___x_217_ = lean_array_get_size(v_keyArray_216_);
v___x_218_ = lean_unsigned_to_nat(2u);
v_cellCount_219_ = lean_nat_mul(v___x_217_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_219_);
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_219_);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_219_);
v_target_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_223_, 0, v___x_220_);
lean_ctor_set(v_target_223_, 1, v___x_221_);
lean_ctor_set(v_target_223_, 2, v___x_222_);
v___x_224_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___redArg(v_target_223_, v_m_215_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg___boxed(lean_object* v_m_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg(v_m_225_);
lean_dec_ref(v_m_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object* v_e_227_, lean_object* v_e_x27_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; lean_object* v___y_233_; lean_object* v___y_237_; lean_object* v_i_238_; lean_object* v___y_244_; lean_object* v___y_254_; lean_object* v_i_255_; lean_object* v___x_270_; 
v___x_231_ = lean_st_ref_take(v_a_229_);
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_231_, v_e_227_);
switch(lean_obj_tag(v___x_270_))
{
case 0:
{
lean_object* v_index_271_; lean_object* v_size_272_; lean_object* v___x_273_; 
v_index_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_index_271_);
lean_dec_ref_known(v___x_270_, 3);
v_size_272_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_size_272_);
lean_inc_ref(v_e_x27_228_);
v___x_273_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_231_, v_size_272_, v_index_271_, v_e_227_, v_e_x27_228_);
lean_dec(v_index_271_);
v___y_233_ = v___x_273_;
goto v___jp_232_;
}
case 1:
{
lean_object* v_index_274_; lean_object* v_size_275_; lean_object* v_keyArray_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_index_274_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_index_274_);
lean_dec_ref_known(v___x_270_, 1);
v_size_275_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_size_275_);
v_keyArray_276_ = lean_ctor_get(v___x_231_, 1);
lean_inc_ref(v_keyArray_276_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_size_275_, v___x_277_);
lean_dec(v_size_275_);
v___x_279_ = lean_array_get_size(v_keyArray_276_);
lean_dec_ref(v_keyArray_276_);
v___x_280_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_dec(v___x_278_);
lean_dec(v_index_274_);
goto v___jp_260_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_281_ = lean_unsigned_to_nat(4u);
v___x_282_ = lean_nat_mul(v___x_278_, v___x_281_);
v___x_283_ = lean_unsigned_to_nat(3u);
v___x_284_ = lean_nat_mul(v___x_279_, v___x_283_);
v___x_285_ = lean_nat_dec_le(v___x_282_, v___x_284_);
lean_dec(v___x_284_);
lean_dec(v___x_282_);
if (v___x_285_ == 0)
{
lean_dec(v___x_278_);
lean_dec(v_index_274_);
goto v___jp_260_;
}
else
{
lean_object* v___x_286_; 
lean_inc_ref(v_e_x27_228_);
v___x_286_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_231_, v___x_278_, v_index_274_, v_e_227_, v_e_x27_228_);
lean_dec(v_index_274_);
v___y_233_ = v___x_286_;
goto v___jp_232_;
}
}
}
default: 
{
lean_object* v_size_287_; lean_object* v_keyArray_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_size_287_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_size_287_);
v_keyArray_288_ = lean_ctor_get(v___x_231_, 1);
lean_inc_ref(v_keyArray_288_);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_size_287_, v___x_289_);
lean_dec(v_size_287_);
v___x_291_ = lean_array_get_size(v_keyArray_288_);
lean_dec_ref(v_keyArray_288_);
v___x_292_ = lean_nat_dec_lt(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v___x_290_);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg(v___x_231_);
lean_dec(v___x_231_);
v___y_244_ = v___x_293_;
goto v___jp_243_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_294_ = lean_unsigned_to_nat(4u);
v___x_295_ = lean_nat_mul(v___x_290_, v___x_294_);
lean_dec(v___x_290_);
v___x_296_ = lean_unsigned_to_nat(3u);
v___x_297_ = lean_nat_mul(v___x_291_, v___x_296_);
v___x_298_ = lean_nat_dec_le(v___x_295_, v___x_297_);
lean_dec(v___x_297_);
lean_dec(v___x_295_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg(v___x_231_);
lean_dec(v___x_231_);
v___y_244_ = v___x_299_;
goto v___jp_243_;
}
else
{
v___y_244_ = v___x_231_;
goto v___jp_243_;
}
}
}
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_st_ref_put(v_a_229_, v___y_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v_e_x27_228_);
return v___x_235_;
}
v___jp_236_:
{
lean_object* v_size_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_size_239_ = lean_ctor_get(v___y_237_, 0);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_size_239_, v___x_240_);
lean_inc_ref(v_e_x27_228_);
v___x_242_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_237_, v___x_241_, v_i_238_, v_e_227_, v_e_x27_228_);
lean_dec(v_i_238_);
v___y_233_ = v___x_242_;
goto v___jp_232_;
}
v___jp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___y_244_, v_e_227_);
switch(lean_obj_tag(v___x_245_))
{
case 0:
{
lean_object* v_index_246_; lean_object* v_size_247_; lean_object* v___x_248_; 
v_index_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_index_246_);
lean_dec_ref_known(v___x_245_, 3);
v_size_247_ = lean_ctor_get(v___y_244_, 0);
lean_inc(v_size_247_);
lean_inc_ref(v_e_x27_228_);
v___x_248_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_244_, v_size_247_, v_index_246_, v_e_227_, v_e_x27_228_);
lean_dec(v_index_246_);
v___y_233_ = v___x_248_;
goto v___jp_232_;
}
case 1:
{
lean_object* v_index_249_; 
v_index_249_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_index_249_);
lean_dec_ref_known(v___x_245_, 1);
v___y_237_ = v___y_244_;
v_i_238_ = v_index_249_;
goto v___jp_236_;
}
default: 
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_244_, v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_index_252_; 
v_index_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_index_252_);
lean_dec_ref_known(v___x_251_, 1);
v___y_237_ = v___y_244_;
v_i_238_ = v_index_252_;
goto v___jp_236_;
}
else
{
lean_dec_ref(v_e_227_);
v___y_233_ = v___y_244_;
goto v___jp_232_;
}
}
}
}
v___jp_253_:
{
lean_object* v_size_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_size_256_ = lean_ctor_get(v___y_254_, 0);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_size_256_, v___x_257_);
lean_inc_ref(v_e_x27_228_);
v___x_259_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_254_, v___x_258_, v_i_255_, v_e_227_, v_e_x27_228_);
lean_dec(v_i_255_);
v___y_233_ = v___x_259_;
goto v___jp_232_;
}
v___jp_260_:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg(v___x_231_);
lean_dec(v___x_231_);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_261_, v_e_227_);
switch(lean_obj_tag(v___x_262_))
{
case 0:
{
lean_object* v_index_263_; lean_object* v_size_264_; lean_object* v___x_265_; 
v_index_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_index_263_);
lean_dec_ref_known(v___x_262_, 3);
v_size_264_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_size_264_);
lean_inc_ref(v_e_x27_228_);
v___x_265_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_261_, v_size_264_, v_index_263_, v_e_227_, v_e_x27_228_);
lean_dec(v_index_263_);
v___y_233_ = v___x_265_;
goto v___jp_232_;
}
case 1:
{
lean_object* v_index_266_; 
v_index_266_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_index_266_);
lean_dec_ref_known(v___x_262_, 1);
v___y_254_ = v___x_261_;
v_i_255_ = v_index_266_;
goto v___jp_253_;
}
default: 
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_261_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_index_269_; 
v_index_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_index_269_);
lean_dec_ref_known(v___x_268_, 1);
v___y_254_ = v___x_261_;
v_i_255_ = v_index_269_;
goto v___jp_253_;
}
else
{
lean_dec_ref(v_e_227_);
v___y_233_ = v___x_261_;
goto v___jp_232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object* v_e_300_, lean_object* v_e_x27_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_300_, v_e_x27_301_, v_a_302_);
lean_dec(v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object* v_e_305_, lean_object* v_e_x27_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_305_, v_e_x27_306_, v_a_307_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object* v_e_312_, lean_object* v_e_x27_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_312_, v_e_x27_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_query_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_320_, v_query_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___boxed(lean_object* v_00_u03b2_323_, lean_object* v_m_324_, lean_object* v_query_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(v_00_u03b2_323_, v_m_324_, v_query_325_);
lean_dec_ref(v_query_325_);
lean_dec_ref(v_m_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1(lean_object* v_00_u03b2_327_, lean_object* v_m_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___redArg(v_m_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1___boxed(lean_object* v_00_u03b2_330_, lean_object* v_m_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1(v_00_u03b2_330_, v_m_331_);
lean_dec_ref(v_m_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object* v_00_u03b2_333_, lean_object* v_m_334_, lean_object* v_query_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_m_334_, v_query_335_, v_x_336_, v_x_337_, v_x_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_341_, lean_object* v_m_342_, lean_object* v_query_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_341_, v_m_342_, v_query_343_, v_x_344_, v_x_345_, v_x_346_, v_x_347_);
lean_dec_ref(v_query_343_);
lean_dec_ref(v_m_342_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2(lean_object* v_00_u03b2_349_, lean_object* v_init_350_, lean_object* v_b_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___redArg(v_init_350_, v_b_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2___boxed(lean_object* v_00_u03b2_353_, lean_object* v_init_354_, lean_object* v_b_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2(v_00_u03b2_353_, v_init_354_, v_b_355_);
lean_dec_ref(v_b_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_357_, lean_object* v_b_358_, lean_object* v_acc_359_, lean_object* v_i_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___redArg(v_b_358_, v_acc_359_, v_i_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_362_, lean_object* v_b_363_, lean_object* v_acc_364_, lean_object* v_i_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__1_spec__2_spec__3(v_00_u03b2_362_, v_b_363_, v_acc_364_, v_i_365_);
lean_dec_ref(v_b_363_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l_Lean_maxRecDepthErrorMessage;
v___x_373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
v___x_375_ = l_Lean_MessageData_ofFormat(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
v___x_377_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2));
v___x_378_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object* v_ref_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_ref_379_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object* v_ref_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object* v_00_u03b1_387_, lean_object* v_ref_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_388_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object* v_00_u03b1_394_, lean_object* v_ref_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_394_, v_ref_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object* v_m_401_, lean_object* v_query_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_401_, v_query_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_index_404_; lean_object* v_key_405_; lean_object* v_value_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_index_404_ = lean_ctor_get(v___x_403_, 0);
v_key_405_ = lean_ctor_get(v___x_403_, 1);
v_value_406_ = lean_ctor_get(v___x_403_, 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_403_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_value_406_);
lean_inc(v_key_405_);
lean_inc(v_index_404_);
lean_dec(v___x_403_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_index_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_key_405_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_value_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_object* v___x_414_; 
lean_dec(v___x_403_);
v___x_414_ = lean_box(1);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object* v_m_415_, lean_object* v_query_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_m_415_, v_query_416_);
lean_dec_ref(v_query_416_);
lean_dec_ref(v_m_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object* v_m_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_m_418_, v_a_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_value_421_; lean_object* v___x_422_; 
v_value_421_ = lean_ctor_get(v___x_420_, 2);
lean_inc(v_value_421_);
lean_dec_ref_known(v___x_420_, 3);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_value_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = lean_box(0);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object* v_m_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_424_, v_a_425_);
lean_dec_ref(v_a_425_);
lean_dec_ref(v_m_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object* v_e_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint8_t v___y_437_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; lean_object* v___y_448_; uint8_t v___y_449_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; uint8_t v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; uint8_t v___y_463_; lean_object* v___y_473_; lean_object* v___y_474_; uint8_t v___y_475_; lean_object* v_fileName_479_; lean_object* v_fileMap_480_; lean_object* v_options_481_; lean_object* v_currRecDepth_482_; lean_object* v_maxRecDepth_483_; lean_object* v_ref_484_; lean_object* v_currNamespace_485_; lean_object* v_openDecls_486_; lean_object* v_initHeartbeats_487_; lean_object* v_maxHeartbeats_488_; lean_object* v_quotContext_489_; lean_object* v_currMacroScope_490_; uint8_t v_diag_491_; lean_object* v_cancelTk_x3f_492_; uint8_t v_suppressElabErrors_493_; lean_object* v_inheritedTraceOptions_494_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_fileName_479_ = lean_ctor_get(v_a_429_, 0);
v_fileMap_480_ = lean_ctor_get(v_a_429_, 1);
v_options_481_ = lean_ctor_get(v_a_429_, 2);
v_currRecDepth_482_ = lean_ctor_get(v_a_429_, 3);
v_maxRecDepth_483_ = lean_ctor_get(v_a_429_, 4);
v_ref_484_ = lean_ctor_get(v_a_429_, 5);
v_currNamespace_485_ = lean_ctor_get(v_a_429_, 6);
v_openDecls_486_ = lean_ctor_get(v_a_429_, 7);
v_initHeartbeats_487_ = lean_ctor_get(v_a_429_, 8);
v_maxHeartbeats_488_ = lean_ctor_get(v_a_429_, 9);
v_quotContext_489_ = lean_ctor_get(v_a_429_, 10);
v_currMacroScope_490_ = lean_ctor_get(v_a_429_, 11);
v_diag_491_ = lean_ctor_get_uint8(v_a_429_, sizeof(void*)*14);
v_cancelTk_x3f_492_ = lean_ctor_get(v_a_429_, 12);
v_suppressElabErrors_493_ = lean_ctor_get_uint8(v_a_429_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_494_ = lean_ctor_get(v_a_429_, 13);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_nat_dec_eq(v_maxRecDepth_483_, v___x_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = lean_nat_dec_eq(v_currRecDepth_482_, v_maxRecDepth_483_);
if (v___x_598_ == 0)
{
goto v___jp_495_;
}
else
{
lean_object* v___x_599_; 
lean_dec_ref(v_e_427_);
lean_inc(v_ref_484_);
v___x_599_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_484_);
return v___x_599_;
}
}
else
{
goto v___jp_495_;
}
v___jp_432_:
{
if (v___y_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_434_, v___y_433_, v___y_436_);
v___x_439_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_438_, v_a_428_);
return v___x_439_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_instBEqBinderInfo_beq(v___y_436_, v___y_436_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_434_, v___y_433_, v___y_436_);
v___x_442_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_441_, v_a_428_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; 
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v___y_433_);
lean_inc_ref(v_e_427_);
v___x_443_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v_e_427_, v_a_428_);
return v___x_443_;
}
}
}
v___jp_444_:
{
if (v___y_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = l_Lean_Expr_lam___override(v___y_448_, v___y_445_, v___y_446_, v___y_447_);
v___x_451_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_450_, v_a_428_);
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_instBEqBinderInfo_beq(v___y_447_, v___y_447_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = l_Lean_Expr_lam___override(v___y_448_, v___y_445_, v___y_446_, v___y_447_);
v___x_454_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_453_, v_a_428_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
lean_dec(v___y_448_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_445_);
lean_inc_ref(v_e_427_);
v___x_455_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v_e_427_, v_a_428_);
return v___x_455_;
}
}
}
v___jp_456_:
{
if (v___y_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v___y_461_);
v___x_464_ = l_Lean_Expr_letE___override(v___y_459_, v___y_462_, v___y_457_, v___y_458_, v___y_460_);
v___x_465_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_464_, v_a_428_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_ptr_addr(v___y_461_);
lean_dec_ref(v___y_461_);
v___x_467_ = lean_ptr_addr(v___y_458_);
v___x_468_ = lean_usize_dec_eq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = l_Lean_Expr_letE___override(v___y_459_, v___y_462_, v___y_457_, v___y_458_, v___y_460_);
v___x_470_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_469_, v_a_428_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; 
lean_dec_ref(v___y_462_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v___y_457_);
lean_inc_ref(v_e_427_);
v___x_471_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v_e_427_, v_a_428_);
return v___x_471_;
}
}
}
v___jp_472_:
{
if (v___y_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = l_Lean_Expr_app___override(v___y_474_, v___y_473_);
v___x_477_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_476_, v_a_428_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; 
lean_dec_ref(v___y_474_);
lean_dec_ref(v___y_473_);
lean_inc_ref(v_e_427_);
v___x_478_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v_e_427_, v_a_428_);
return v___x_478_;
}
}
v___jp_495_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_st_ref_get(v_a_428_);
v___x_497_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_496_, v_e_427_);
lean_dec(v___x_496_);
if (lean_obj_tag(v___x_497_) == 1)
{
lean_object* v_val_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v_e_427_);
v_val_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_val_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 0);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_val_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v___x_497_);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_currRecDepth_482_, v___x_506_);
lean_inc_ref(v_inheritedTraceOptions_494_);
lean_inc(v_cancelTk_x3f_492_);
lean_inc(v_currMacroScope_490_);
lean_inc(v_quotContext_489_);
lean_inc(v_maxHeartbeats_488_);
lean_inc(v_initHeartbeats_487_);
lean_inc(v_openDecls_486_);
lean_inc(v_currNamespace_485_);
lean_inc(v_ref_484_);
lean_inc(v_maxRecDepth_483_);
lean_inc_ref(v_options_481_);
lean_inc_ref(v_fileMap_480_);
lean_inc_ref(v_fileName_479_);
v___x_508_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_508_, 0, v_fileName_479_);
lean_ctor_set(v___x_508_, 1, v_fileMap_480_);
lean_ctor_set(v___x_508_, 2, v_options_481_);
lean_ctor_set(v___x_508_, 3, v___x_507_);
lean_ctor_set(v___x_508_, 4, v_maxRecDepth_483_);
lean_ctor_set(v___x_508_, 5, v_ref_484_);
lean_ctor_set(v___x_508_, 6, v_currNamespace_485_);
lean_ctor_set(v___x_508_, 7, v_openDecls_486_);
lean_ctor_set(v___x_508_, 8, v_initHeartbeats_487_);
lean_ctor_set(v___x_508_, 9, v_maxHeartbeats_488_);
lean_ctor_set(v___x_508_, 10, v_quotContext_489_);
lean_ctor_set(v___x_508_, 11, v_currMacroScope_490_);
lean_ctor_set(v___x_508_, 12, v_cancelTk_x3f_492_);
lean_ctor_set(v___x_508_, 13, v_inheritedTraceOptions_494_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*14, v_diag_491_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*14 + 1, v_suppressElabErrors_493_);
switch(lean_obj_tag(v_e_427_))
{
case 7:
{
lean_object* v_binderName_509_; lean_object* v_binderType_510_; lean_object* v_body_511_; uint8_t v_binderInfo_512_; lean_object* v___x_513_; 
v_binderName_509_ = lean_ctor_get(v_e_427_, 0);
v_binderType_510_ = lean_ctor_get(v_e_427_, 1);
v_body_511_ = lean_ctor_get(v_e_427_, 2);
v_binderInfo_512_ = lean_ctor_get_uint8(v_e_427_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_510_);
v___x_513_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_510_, v_a_428_, v___x_508_, v_a_430_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
lean_inc_ref(v_body_511_);
v___x_515_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_511_, v_a_428_, v___x_508_, v_a_430_);
lean_dec_ref_known(v___x_508_, 14);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_ptr_addr(v_binderType_510_);
v___x_518_ = lean_ptr_addr(v_a_514_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_inc(v_binderName_509_);
v___y_433_ = v_a_516_;
v___y_434_ = v_a_514_;
v___y_435_ = v_binderName_509_;
v___y_436_ = v_binderInfo_512_;
v___y_437_ = v___x_519_;
goto v___jp_432_;
}
else
{
size_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_ptr_addr(v_body_511_);
v___x_521_ = lean_ptr_addr(v_a_516_);
v___x_522_ = lean_usize_dec_eq(v___x_520_, v___x_521_);
lean_inc(v_binderName_509_);
v___y_433_ = v_a_516_;
v___y_434_ = v_a_514_;
v___y_435_ = v_binderName_509_;
v___y_436_ = v_binderInfo_512_;
v___y_437_ = v___x_522_;
goto v___jp_432_;
}
}
else
{
lean_dec(v_a_514_);
lean_dec_ref_known(v_e_427_, 3);
return v___x_515_;
}
}
else
{
lean_dec_ref_known(v_e_427_, 3);
lean_dec_ref_known(v___x_508_, 14);
return v___x_513_;
}
}
case 6:
{
lean_object* v_binderName_523_; lean_object* v_binderType_524_; lean_object* v_body_525_; uint8_t v_binderInfo_526_; lean_object* v___x_527_; lean_object* v___x_528_; size_t v___x_529_; size_t v___x_530_; uint8_t v___x_531_; 
v_binderName_523_ = lean_ctor_get(v_e_427_, 0);
v_binderType_524_ = lean_ctor_get(v_e_427_, 1);
v_body_525_ = lean_ctor_get(v_e_427_, 2);
v_binderInfo_526_ = lean_ctor_get_uint8(v_e_427_, sizeof(void*)*3 + 8);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_427_, v_e_427_, v___x_527_);
v___x_529_ = lean_ptr_addr(v_e_427_);
v___x_530_ = lean_ptr_addr(v___x_528_);
v___x_531_ = lean_usize_dec_eq(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_528_, v_a_428_, v___x_508_, v_a_430_);
lean_dec_ref_known(v___x_508_, 14);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v_a_533_, v_a_428_);
return v___x_534_;
}
else
{
lean_dec_ref_known(v_e_427_, 3);
return v___x_532_;
}
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v___x_528_);
lean_inc_ref(v_binderType_524_);
v___x_535_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_524_, v_a_428_, v___x_508_, v_a_430_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
lean_inc_ref(v_body_525_);
v___x_537_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_525_, v_a_428_, v___x_508_, v_a_430_);
lean_dec_ref_known(v___x_508_, 14);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; size_t v___x_539_; size_t v___x_540_; uint8_t v___x_541_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = lean_ptr_addr(v_binderType_524_);
v___x_540_ = lean_ptr_addr(v_a_536_);
v___x_541_ = lean_usize_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_inc(v_binderName_523_);
v___y_445_ = v_a_536_;
v___y_446_ = v_a_538_;
v___y_447_ = v_binderInfo_526_;
v___y_448_ = v_binderName_523_;
v___y_449_ = v___x_541_;
goto v___jp_444_;
}
else
{
size_t v___x_542_; size_t v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_ptr_addr(v_body_525_);
v___x_543_ = lean_ptr_addr(v_a_538_);
v___x_544_ = lean_usize_dec_eq(v___x_542_, v___x_543_);
lean_inc(v_binderName_523_);
v___y_445_ = v_a_536_;
v___y_446_ = v_a_538_;
v___y_447_ = v_binderInfo_526_;
v___y_448_ = v_binderName_523_;
v___y_449_ = v___x_544_;
goto v___jp_444_;
}
}
else
{
lean_dec(v_a_536_);
lean_dec_ref_known(v_e_427_, 3);
return v___x_537_;
}
}
else
{
lean_dec_ref_known(v_e_427_, 3);
lean_dec_ref_known(v___x_508_, 14);
return v___x_535_;
}
}
}
case 8:
{
lean_object* v_declName_545_; lean_object* v_type_546_; lean_object* v_value_547_; lean_object* v_body_548_; uint8_t v_nondep_549_; lean_object* v___x_550_; 
v_declName_545_ = lean_ctor_get(v_e_427_, 0);
v_type_546_ = lean_ctor_get(v_e_427_, 1);
v_value_547_ = lean_ctor_get(v_e_427_, 2);
v_body_548_ = lean_ctor_get(v_e_427_, 3);
v_nondep_549_ = lean_ctor_get_uint8(v_e_427_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_546_);
v___x_550_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_546_, v_a_428_, v___x_508_, v_a_430_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
lean_inc_ref(v_value_547_);
v___x_552_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_547_, v_a_428_, v___x_508_, v_a_430_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
lean_inc_ref(v_body_548_);
v___x_554_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_548_, v_a_428_, v___x_508_, v_a_430_);
lean_dec_ref_known(v___x_508_, 14);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; size_t v___x_556_; size_t v___x_557_; uint8_t v___x_558_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = lean_ptr_addr(v_type_546_);
v___x_557_ = lean_ptr_addr(v_a_551_);
v___x_558_ = lean_usize_dec_eq(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_inc_ref(v_body_548_);
lean_inc(v_declName_545_);
v___y_457_ = v_a_553_;
v___y_458_ = v_a_555_;
v___y_459_ = v_declName_545_;
v___y_460_ = v_nondep_549_;
v___y_461_ = v_body_548_;
v___y_462_ = v_a_551_;
v___y_463_ = v___x_558_;
goto v___jp_456_;
}
else
{
size_t v___x_559_; size_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_ptr_addr(v_value_547_);
v___x_560_ = lean_ptr_addr(v_a_553_);
v___x_561_ = lean_usize_dec_eq(v___x_559_, v___x_560_);
lean_inc_ref(v_body_548_);
lean_inc(v_declName_545_);
v___y_457_ = v_a_553_;
v___y_458_ = v_a_555_;
v___y_459_ = v_declName_545_;
v___y_460_ = v_nondep_549_;
v___y_461_ = v_body_548_;
v___y_462_ = v_a_551_;
v___y_463_ = v___x_561_;
goto v___jp_456_;
}
}
else
{
lean_dec(v_a_553_);
lean_dec(v_a_551_);
lean_dec_ref_known(v_e_427_, 4);
return v___x_554_;
}
}
else
{
lean_dec(v_a_551_);
lean_dec_ref_known(v_e_427_, 4);
lean_dec_ref_known(v___x_508_, 14);
return v___x_552_;
}
}
else
{
lean_dec_ref_known(v_e_427_, 4);
lean_dec_ref_known(v___x_508_, 14);
return v___x_550_;
}
}
case 5:
{
lean_object* v_fn_562_; lean_object* v_arg_563_; lean_object* v___x_564_; 
v_fn_562_ = lean_ctor_get(v_e_427_, 0);
v_arg_563_ = lean_ctor_get(v_e_427_, 1);
lean_inc_ref(v_fn_562_);
v___x_564_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_562_, v_a_428_, v___x_508_, v_a_430_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
lean_inc_ref(v_arg_563_);
v___x_566_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_563_, v_a_428_, v___x_508_, v_a_430_);
lean_dec_ref_known(v___x_508_, 14);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; size_t v___x_568_; size_t v___x_569_; uint8_t v___x_570_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_568_ = lean_ptr_addr(v_fn_562_);
v___x_569_ = lean_ptr_addr(v_a_565_);
v___x_570_ = lean_usize_dec_eq(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
v___y_473_ = v_a_567_;
v___y_474_ = v_a_565_;
v___y_475_ = v___x_570_;
goto v___jp_472_;
}
else
{
size_t v___x_571_; size_t v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_ptr_addr(v_arg_563_);
v___x_572_ = lean_ptr_addr(v_a_567_);
v___x_573_ = lean_usize_dec_eq(v___x_571_, v___x_572_);
v___y_473_ = v_a_567_;
v___y_474_ = v_a_565_;
v___y_475_ = v___x_573_;
goto v___jp_472_;
}
}
else
{
lean_dec(v_a_565_);
lean_dec_ref_known(v_e_427_, 2);
return v___x_566_;
}
}
else
{
lean_dec_ref_known(v_e_427_, 2);
lean_dec_ref_known(v___x_508_, 14);
return v___x_564_;
}
}
case 10:
{
lean_object* v_data_574_; lean_object* v_expr_575_; lean_object* v___x_576_; 
v_data_574_ = lean_ctor_get(v_e_427_, 0);
v_expr_575_ = lean_ctor_get(v_e_427_, 1);
lean_inc_ref(v_expr_575_);
v___x_576_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_575_, v_a_428_, v___x_508_, v_a_430_);
lean_dec_ref_known(v___x_508_, 14);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; size_t v___x_578_; size_t v___x_579_; uint8_t v___x_580_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_578_ = lean_ptr_addr(v_expr_575_);
v___x_579_ = lean_ptr_addr(v_a_577_);
v___x_580_ = lean_usize_dec_eq(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_inc(v_data_574_);
v___x_581_ = l_Lean_Expr_mdata___override(v_data_574_, v_a_577_);
v___x_582_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_581_, v_a_428_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; 
lean_dec(v_a_577_);
lean_inc_ref(v_e_427_);
v___x_583_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v_e_427_, v_a_428_);
return v___x_583_;
}
}
else
{
lean_dec_ref_known(v_e_427_, 2);
return v___x_576_;
}
}
case 11:
{
lean_object* v_typeName_584_; lean_object* v_idx_585_; lean_object* v_struct_586_; lean_object* v___x_587_; 
v_typeName_584_ = lean_ctor_get(v_e_427_, 0);
v_idx_585_ = lean_ctor_get(v_e_427_, 1);
v_struct_586_ = lean_ctor_get(v_e_427_, 2);
lean_inc_ref(v_struct_586_);
v___x_587_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_586_, v_a_428_, v___x_508_, v_a_430_);
lean_dec_ref_known(v___x_508_, 14);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; size_t v___x_589_; size_t v___x_590_; uint8_t v___x_591_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = lean_ptr_addr(v_struct_586_);
v___x_590_ = lean_ptr_addr(v_a_588_);
v___x_591_ = lean_usize_dec_eq(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_inc(v_idx_585_);
lean_inc(v_typeName_584_);
v___x_592_ = l_Lean_Expr_proj___override(v_typeName_584_, v_idx_585_, v_a_588_);
v___x_593_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v___x_592_, v_a_428_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; 
lean_dec(v_a_588_);
lean_inc_ref(v_e_427_);
v___x_594_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_427_, v_e_427_, v_a_428_);
return v___x_594_;
}
}
else
{
lean_dec_ref_known(v_e_427_, 3);
return v___x_587_;
}
}
default: 
{
lean_object* v___x_595_; 
lean_dec_ref_known(v___x_508_, 14);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_e_427_);
return v___x_595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object* v_e_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object* v_00_u03b2_606_, lean_object* v_m_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_607_, v_a_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object* v_00_u03b2_610_, lean_object* v_m_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_610_, v_m_611_, v_a_612_);
lean_dec_ref(v_a_612_);
lean_dec_ref(v_m_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_query_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_m_615_, v_query_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_query_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_618_, v_m_619_, v_query_620_);
lean_dec_ref(v_query_620_);
lean_dec_ref(v_m_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object* v_e_622_, lean_object* v_c_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_st_mk_ref(v_c_623_);
v___x_628_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_622_, v___x_627_, v_a_624_, v_a_625_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_638_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = lean_st_ref_get(v___x_627_);
lean_dec(v___x_627_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_a_629_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___x_627_);
v_a_639_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_628_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_628_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object* v_e_647_, lean_object* v_c_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_647_, v_c_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_652_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__1(void){
_start:
{
lean_object* v_cellCount_654_; lean_object* v___x_655_; 
v_cellCount_654_ = lean_unsigned_to_nat(16u);
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__2(void){
_start:
{
lean_object* v_cellCount_656_; lean_object* v___x_657_; 
v_cellCount_656_ = lean_unsigned_to_nat(16u);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__3(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_658_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__2, &l_Lean_Meta_Sym_etaReduceAll___closed__2_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__2);
v___x_659_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__1, &l_Lean_Meta_Sym_etaReduceAll___closed__1_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__1);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
lean_ctor_set(v___x_661_, 2, v___x_658_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lean_Meta_Sym_etaReduceAll___closed__0));
v___x_667_ = lean_find_expr(v___x_666_, v_e_662_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_e_662_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__3, &l_Lean_Meta_Sym_etaReduceAll___closed__3_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__3);
v___x_670_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_662_, v___x_669_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_fst_675_; lean_object* v___x_677_; 
v_fst_675_ = lean_ctor_get(v_a_671_, 0);
lean_inc(v_fst_675_);
lean_dec(v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_fst_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_fst_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object* v_e_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Meta_Sym_etaReduceAll(v_e_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
return v_res_692_;
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
