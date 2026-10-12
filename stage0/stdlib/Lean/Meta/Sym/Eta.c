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
uint8_t l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(lean_object* v_e_1_, lean_object* v_a_2_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
uint8_t v_res_10_;
v_res_10_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(v_e_1_, v_a_2_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go___boxed(lean_object* v_e_11_, lean_object* v_a_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(v_e_11_, v_a_12_);
lean_dec_ref(v_e_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(lean_object* v_e_15_, lean_object* v_n_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_Lean_Expr_hasLooseBVars(v_e_15_);
if (v___x_17_ == 0)
{
lean_dec(v_n_16_);
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
v___x_18_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(v_e_15_, v_n_16_);
return v___x_18_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_15_ = stack[0].m_obj;
lean_object* v_n_16_ = stack[1].m_obj;
uint8_t v_res_19_;
v_res_19_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(v_e_15_, v_n_16_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange___boxed(lean_object* v_e_20_, lean_object* v_n_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(v_e_20_, v_n_21_);
lean_dec_ref(v_e_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(lean_object* v_n_24_, lean_object* v_default_25_, lean_object* v_body_26_, lean_object* v_m_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_zero_29_; uint8_t v_isZero_30_; 
v_zero_29_ = lean_unsigned_to_nat(0u);
v_isZero_30_ = lean_nat_dec_eq(v_m_27_, v_zero_29_);
if (v_isZero_30_ == 1)
{
uint8_t v___x_31_; 
lean_dec(v_i_28_);
lean_dec(v_m_27_);
lean_inc(v_n_24_);
v___x_31_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(v_body_26_, v_n_24_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
v___x_32_ = lean_expr_lower_loose_bvars(v_body_26_, v_n_24_, v_n_24_);
lean_dec(v_n_24_);
return v___x_32_;
}
else
{
lean_dec(v_n_24_);
lean_inc_ref(v_default_25_);
return v_default_25_;
}
}
else
{
if (lean_obj_tag(v_body_26_) == 5)
{
lean_object* v_arg_33_; 
v_arg_33_ = lean_ctor_get(v_body_26_, 1);
if (lean_obj_tag(v_arg_33_) == 0)
{
lean_object* v_fn_34_; lean_object* v_deBruijnIndex_35_; uint8_t v___x_36_; 
v_fn_34_ = lean_ctor_get(v_body_26_, 0);
v_deBruijnIndex_35_ = lean_ctor_get(v_arg_33_, 0);
v___x_36_ = lean_nat_dec_eq(v_deBruijnIndex_35_, v_i_28_);
if (v___x_36_ == 0)
{
lean_dec(v_i_28_);
lean_dec(v_m_27_);
lean_dec(v_n_24_);
lean_inc_ref(v_default_25_);
return v_default_25_;
}
else
{
lean_object* v_one_37_; lean_object* v_n_38_; lean_object* v___x_39_; 
v_one_37_ = lean_unsigned_to_nat(1u);
v_n_38_ = lean_nat_sub(v_m_27_, v_one_37_);
lean_dec(v_m_27_);
v___x_39_ = lean_nat_add(v_i_28_, v_one_37_);
lean_dec(v_i_28_);
v_body_26_ = v_fn_34_;
v_m_27_ = v_n_38_;
v_i_28_ = v___x_39_;
goto _start;
}
}
else
{
lean_dec(v_i_28_);
lean_dec(v_m_27_);
lean_dec(v_n_24_);
lean_inc_ref(v_default_25_);
return v_default_25_;
}
}
else
{
lean_dec(v_i_28_);
lean_dec(v_m_27_);
lean_dec(v_n_24_);
lean_inc_ref(v_default_25_);
return v_default_25_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go___boxed(lean_object* v_n_41_, lean_object* v_default_42_, lean_object* v_body_43_, lean_object* v_m_44_, lean_object* v_i_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(v_n_41_, v_default_42_, v_body_43_, v_m_44_, v_i_45_);
lean_dec_ref(v_body_43_);
lean_dec_ref(v_default_42_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(lean_object* v_body_47_, lean_object* v_n_48_, lean_object* v_i_49_, lean_object* v_default_50_){
_start:
{
lean_object* v___x_51_; 
lean_inc(v_n_48_);
v___x_51_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(v_n_48_, v_default_50_, v_body_47_, v_n_48_, v_i_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux___boxed(lean_object* v_body_52_, lean_object* v_n_53_, lean_object* v_i_54_, lean_object* v_default_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(v_body_52_, v_n_53_, v_i_54_, v_default_55_);
lean_dec_ref(v_default_55_);
lean_dec_ref(v_body_52_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(lean_object* v_e_57_, lean_object* v_body_58_, lean_object* v_n_59_){
_start:
{
if (lean_obj_tag(v_body_58_) == 6)
{
lean_object* v_body_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_body_60_ = lean_ctor_get(v_body_58_, 2);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_n_59_, v___x_61_);
lean_dec(v_n_59_);
v_body_58_ = v_body_60_;
v_n_59_ = v___x_62_;
goto _start;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_59_);
v___x_65_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(v_n_59_, v_e_57_, v_body_58_, v_n_59_, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go___boxed(lean_object* v_e_66_, lean_object* v_body_67_, lean_object* v_n_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_66_, v_body_67_, v_n_68_);
lean_dec_ref(v_body_67_);
lean_dec_ref(v_e_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce(lean_object* v_e_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = l_Lean_Expr_isLambda(v_e_70_);
if (v___x_71_ == 0)
{
lean_inc_ref(v_e_70_);
return v_e_70_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_70_, v_e_70_, v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduce___boxed(lean_object* v_e_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_Sym_etaReduce(v_e_74_);
lean_dec_ref(v_e_74_);
return v_res_75_;
}
}
uint8_t l_Lean_Meta_Sym_isEtaReducible(lean_object* v_e_76_){
_start:
{
lean_object* v___x_77_; size_t v___x_78_; size_t v___x_79_; uint8_t v___x_80_; 
v___x_77_ = l_Lean_Meta_Sym_etaReduce(v_e_76_);
v___x_78_ = lean_ptr_addr(v_e_76_);
v___x_79_ = lean_ptr_addr(v___x_77_);
lean_dec_ref(v___x_77_);
v___x_80_ = lean_usize_dec_eq(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 1;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isEtaReducible_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_76_ = stack[0].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Lean_Meta_Sym_isEtaReducible(v_e_76_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isEtaReducible___boxed(lean_object* v_e_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Lean_Meta_Sym_isEtaReducible(v_e_84_);
lean_dec_ref(v_e_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(lean_object* v_a_87_, lean_object* v_b_88_, lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_dec(v_b_88_);
lean_dec_ref(v_a_87_);
return v_x_89_;
}
else
{
lean_object* v_key_90_; lean_object* v_value_91_; lean_object* v_tail_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_106_; 
v_key_90_ = lean_ctor_get(v_x_89_, 0);
v_value_91_ = lean_ctor_get(v_x_89_, 1);
v_tail_92_ = lean_ctor_get(v_x_89_, 2);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_106_ == 0)
{
v___x_94_ = v_x_89_;
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_tail_92_);
lean_inc(v_value_91_);
lean_inc(v_key_90_);
lean_dec(v_x_89_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
size_t v___x_96_; size_t v___x_97_; uint8_t v___x_98_; 
v___x_96_ = lean_ptr_addr(v_key_90_);
v___x_97_ = lean_ptr_addr(v_a_87_);
v___x_98_ = lean_usize_dec_eq(v___x_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_87_, v_b_88_, v_tail_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 2, v___x_99_);
v___x_101_ = v___x_94_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_key_90_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_value_91_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v_value_91_);
lean_dec(v_key_90_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_b_88_);
lean_ctor_set(v___x_94_, 0, v_a_87_);
v___x_104_ = v___x_94_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_87_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_b_88_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_tail_92_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
return v_x_107_;
}
else
{
lean_object* v_key_109_; lean_object* v_value_110_; lean_object* v_tail_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_137_; 
v_key_109_ = lean_ctor_get(v_x_108_, 0);
v_value_110_ = lean_ctor_get(v_x_108_, 1);
v_tail_111_ = lean_ctor_get(v_x_108_, 2);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_137_ == 0)
{
v___x_113_ = v_x_108_;
v_isShared_114_ = v_isSharedCheck_137_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_tail_111_);
lean_inc(v_value_110_);
lean_inc(v_key_109_);
lean_dec(v_x_108_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_137_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_115_ = lean_array_get_size(v_x_107_);
v___x_116_ = lean_ptr_addr(v_key_109_);
v___x_117_ = ((size_t)3ULL);
v___x_118_ = lean_usize_shift_right(v___x_116_, v___x_117_);
v___x_119_ = lean_usize_to_uint64(v___x_118_);
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___x_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___x_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_115_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v___x_131_ = lean_array_uget_borrowed(v_x_107_, v___x_130_);
lean_inc(v___x_131_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 2, v___x_131_);
v___x_133_ = v___x_113_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_key_109_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_value_110_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v___x_131_);
v___x_133_ = v_reuseFailAlloc_136_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
v___x_134_ = lean_array_uset(v_x_107_, v___x_130_, v___x_133_);
v_x_107_ = v___x_134_;
v_x_108_ = v_tail_111_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(lean_object* v_i_138_, lean_object* v_source_139_, lean_object* v_target_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_array_get_size(v_source_139_);
v___x_142_ = lean_nat_dec_lt(v_i_138_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec_ref(v_source_139_);
lean_dec(v_i_138_);
return v_target_140_;
}
else
{
lean_object* v_es_143_; lean_object* v___x_144_; lean_object* v_source_145_; lean_object* v_target_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_es_143_ = lean_array_fget(v_source_139_, v_i_138_);
v___x_144_ = lean_box(0);
v_source_145_ = lean_array_fset(v_source_139_, v_i_138_, v___x_144_);
v_target_146_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_140_, v_es_143_);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_add(v_i_138_, v___x_147_);
lean_dec(v_i_138_);
v_i_138_ = v___x_148_;
v_source_139_ = v_source_145_;
v_target_140_ = v_target_146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(lean_object* v_data_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_nbuckets_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_151_ = lean_array_get_size(v_data_150_);
v___x_152_ = lean_unsigned_to_nat(2u);
v_nbuckets_153_ = lean_nat_mul(v___x_151_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_box(0);
v___x_156_ = lean_mk_array(v_nbuckets_153_, v___x_155_);
v___x_157_ = lean_array_propagate_mark(v_data_150_, v___x_156_);
v___x_158_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v___x_154_, v_data_150_, v___x_157_);
return v___x_158_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(lean_object* v_a_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
else
{
lean_object* v_key_162_; lean_object* v_tail_163_; size_t v___x_164_; size_t v___x_165_; uint8_t v___x_166_; 
v_key_162_ = lean_ctor_get(v_x_160_, 0);
v_tail_163_ = lean_ctor_get(v_x_160_, 2);
v___x_164_ = lean_ptr_addr(v_key_162_);
v___x_165_ = lean_ptr_addr(v_a_159_);
v___x_166_ = lean_usize_dec_eq(v___x_164_, v___x_165_);
if (v___x_166_ == 0)
{
v_x_160_ = v_tail_163_;
goto _start;
}
else
{
return v___x_166_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_159_ = stack[0].m_obj;
lean_object* v_x_160_ = stack[1].m_obj;
uint8_t v_res_168_;
v_res_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_159_, v_x_160_);
stack->m_num = v_res_168_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(lean_object* v_a_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_169_, v_x_170_);
lean_dec(v_x_170_);
lean_dec_ref(v_a_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(lean_object* v_m_173_, lean_object* v_a_174_, lean_object* v_b_175_){
_start:
{
lean_object* v_size_176_; lean_object* v_buckets_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_223_; 
v_size_176_ = lean_ctor_get(v_m_173_, 0);
v_buckets_177_ = lean_ctor_get(v_m_173_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_m_173_);
if (v_isSharedCheck_223_ == 0)
{
v___x_179_ = v_m_173_;
v_isShared_180_ = v_isSharedCheck_223_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_buckets_177_);
lean_inc(v_size_176_);
lean_dec(v_m_173_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_223_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v_fold_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v_bkt_197_; uint8_t v___x_198_; 
v___x_181_ = lean_array_get_size(v_buckets_177_);
v___x_182_ = lean_ptr_addr(v_a_174_);
v___x_183_ = ((size_t)3ULL);
v___x_184_ = lean_usize_shift_right(v___x_182_, v___x_183_);
v___x_185_ = lean_usize_to_uint64(v___x_184_);
v___x_186_ = 32ULL;
v___x_187_ = lean_uint64_shift_right(v___x_185_, v___x_186_);
v_fold_188_ = lean_uint64_xor(v___x_185_, v___x_187_);
v___x_189_ = 16ULL;
v___x_190_ = lean_uint64_shift_right(v_fold_188_, v___x_189_);
v___x_191_ = lean_uint64_xor(v_fold_188_, v___x_190_);
v___x_192_ = lean_uint64_to_usize(v___x_191_);
v___x_193_ = lean_usize_of_nat(v___x_181_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v___x_193_, v___x_194_);
v___x_196_ = lean_usize_land(v___x_192_, v___x_195_);
v_bkt_197_ = lean_array_uget_borrowed(v_buckets_177_, v___x_196_);
v___x_198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_174_, v_bkt_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v_size_x27_200_; lean_object* v___x_201_; lean_object* v_buckets_x27_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v_size_x27_200_ = lean_nat_add(v_size_176_, v___x_199_);
lean_dec(v_size_176_);
lean_inc(v_bkt_197_);
v___x_201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_201_, 0, v_a_174_);
lean_ctor_set(v___x_201_, 1, v_b_175_);
lean_ctor_set(v___x_201_, 2, v_bkt_197_);
v_buckets_x27_202_ = lean_array_uset(v_buckets_177_, v___x_196_, v___x_201_);
v___x_203_ = lean_unsigned_to_nat(4u);
v___x_204_ = lean_nat_mul(v_size_x27_200_, v___x_203_);
v___x_205_ = lean_unsigned_to_nat(3u);
v___x_206_ = lean_nat_div(v___x_204_, v___x_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_array_get_size(v_buckets_x27_202_);
v___x_208_ = lean_nat_dec_le(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
if (v___x_208_ == 0)
{
lean_object* v_val_209_; lean_object* v___x_211_; 
v_val_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_buckets_x27_202_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v_val_209_);
lean_ctor_set(v___x_179_, 0, v_size_x27_200_);
v___x_211_ = v___x_179_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_size_x27_200_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_val_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_object* v___x_214_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v_buckets_x27_202_);
lean_ctor_set(v___x_179_, 0, v_size_x27_200_);
v___x_214_ = v___x_179_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_size_x27_200_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_buckets_x27_202_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
else
{
lean_object* v___x_216_; lean_object* v_buckets_x27_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
lean_inc(v_bkt_197_);
v___x_216_ = lean_box(0);
v_buckets_x27_217_ = lean_array_uset(v_buckets_177_, v___x_196_, v___x_216_);
v___x_218_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_174_, v_b_175_, v_bkt_197_);
v___x_219_ = lean_array_uset(v_buckets_x27_217_, v___x_196_, v___x_218_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_219_);
v___x_221_ = v___x_179_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_size_176_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(lean_object* v_e_224_, lean_object* v_e_x27_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_st_ref_take(v_a_226_);
lean_inc_ref(v_e_x27_225_);
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_228_, v_e_224_, v_e_x27_225_);
v___x_230_ = lean_st_ref_put(v_a_226_, v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_e_x27_225_);
return v___x_231_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_224_ = stack[0].m_obj;
lean_object* v_e_x27_225_ = stack[1].m_obj;
lean_object* v_a_226_ = stack[2].m_obj;
lean_object* v_res_232_;
v_res_232_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_224_, v_e_x27_225_, v_a_226_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(lean_object* v_e_233_, lean_object* v_e_x27_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_233_, v_e_x27_234_, v_a_235_);
lean_dec(v_a_235_);
return v_res_237_;
}
}
lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(lean_object* v_e_238_, lean_object* v_e_x27_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_238_, v_e_x27_239_, v_a_240_);
return v___x_244_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_238_ = stack[0].m_obj;
lean_object* v_e_x27_239_ = stack[1].m_obj;
lean_object* v_a_240_ = stack[2].m_obj;
lean_object* v_a_241_ = stack[3].m_obj;
lean_object* v_a_242_ = stack[4].m_obj;
lean_object* v_res_245_;
v_res_245_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_238_, v_e_x27_239_, v_a_240_, v_a_241_, v_a_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(lean_object* v_e_246_, lean_object* v_e_x27_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(v_e_246_, v_e_x27_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(lean_object* v_00_u03b2_253_, lean_object* v_m_254_, lean_object* v_a_255_, lean_object* v_b_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_254_, v_a_255_, v_b_256_);
return v___x_257_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_object* v_00_u03b2_258_, lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_259_, v_x_260_);
return v___x_261_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_259_ = stack[1].m_obj;
lean_object* v_x_260_ = stack[2].m_obj;
uint8_t v_res_262_;
v_res_262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(lean_box(0), v_a_259_, v_x_260_);
stack->m_num = v_res_262_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_263_, lean_object* v_a_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_263_, v_a_264_, v_x_265_);
lean_dec(v_x_265_);
lean_dec_ref(v_a_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(lean_object* v_00_u03b2_268_, lean_object* v_data_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_data_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(lean_object* v_00_u03b2_271_, lean_object* v_a_272_, lean_object* v_b_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_272_, v_b_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_276_, lean_object* v_i_277_, lean_object* v_source_278_, lean_object* v_target_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v_i_277_, v_source_278_, v_target_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_282_, v_x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = l_Lean_maxRecDepthErrorMessage;
v___x_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
v___x_293_ = l_Lean_MessageData_ofFormat(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
v___x_295_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2));
v___x_296_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
return v___x_296_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(lean_object* v_ref_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_ref_297_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_297_ = stack[0].m_obj;
lean_object* v_res_302_;
v_res_302_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_297_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(lean_object* v_ref_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_303_);
return v_res_305_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_object* v_00_u03b1_306_, lean_object* v_ref_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_307_);
return v___x_312_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_307_ = stack[1].m_obj;
lean_object* v___y_308_ = stack[2].m_obj;
lean_object* v___y_309_ = stack[3].m_obj;
lean_object* v___y_310_ = stack[4].m_obj;
lean_object* v_res_313_;
v_res_313_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(lean_box(0), v_ref_307_, v___y_308_, v___y_309_, v___y_310_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(lean_object* v_00_u03b1_314_, lean_object* v_ref_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_314_, v_ref_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(lean_object* v_a_321_, lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
return v___x_323_;
}
else
{
lean_object* v_key_324_; lean_object* v_value_325_; lean_object* v_tail_326_; size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v_key_324_ = lean_ctor_get(v_x_322_, 0);
v_value_325_ = lean_ctor_get(v_x_322_, 1);
v_tail_326_ = lean_ctor_get(v_x_322_, 2);
v___x_327_ = lean_ptr_addr(v_key_324_);
v___x_328_ = lean_ptr_addr(v_a_321_);
v___x_329_ = lean_usize_dec_eq(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
v_x_322_ = v_tail_326_;
goto _start;
}
else
{
lean_object* v___x_331_; 
lean_inc(v_value_325_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v_value_325_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec_ref(v_a_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_buckets_337_; lean_object* v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v_fold_345_; uint64_t v___x_346_; uint64_t v___x_347_; uint64_t v___x_348_; size_t v___x_349_; size_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_buckets_337_ = lean_ctor_get(v_m_335_, 1);
v___x_338_ = lean_array_get_size(v_buckets_337_);
v___x_339_ = lean_ptr_addr(v_a_336_);
v___x_340_ = ((size_t)3ULL);
v___x_341_ = lean_usize_shift_right(v___x_339_, v___x_340_);
v___x_342_ = lean_usize_to_uint64(v___x_341_);
v___x_343_ = 32ULL;
v___x_344_ = lean_uint64_shift_right(v___x_342_, v___x_343_);
v_fold_345_ = lean_uint64_xor(v___x_342_, v___x_344_);
v___x_346_ = 16ULL;
v___x_347_ = lean_uint64_shift_right(v_fold_345_, v___x_346_);
v___x_348_ = lean_uint64_xor(v_fold_345_, v___x_347_);
v___x_349_ = lean_uint64_to_usize(v___x_348_);
v___x_350_ = lean_usize_of_nat(v___x_338_);
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_sub(v___x_350_, v___x_351_);
v___x_353_ = lean_usize_land(v___x_349_, v___x_352_);
v___x_354_ = lean_array_uget_borrowed(v_buckets_337_, v___x_353_);
v___x_355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_336_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(lean_object* v_m_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_356_, v_a_357_);
lean_dec_ref(v_a_357_);
lean_dec_ref(v_m_356_);
return v_res_358_;
}
}
lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_toCold_364_; lean_object* v_currRecDepth_365_; lean_object* v_ref_366_; uint16_t v_optionFlags_367_; uint8_t v_suppressElabErrors_368_; uint8_t v_isRecordingDeps_369_; lean_object* v_maxRecDepth_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_toCold_364_ = lean_ctor_get(v_a_361_, 0);
v_currRecDepth_365_ = lean_ctor_get(v_a_361_, 1);
v_ref_366_ = lean_ctor_get(v_a_361_, 2);
v_optionFlags_367_ = lean_ctor_get_uint16(v_a_361_, sizeof(void*)*3);
v_suppressElabErrors_368_ = lean_ctor_get_uint8(v_a_361_, sizeof(void*)*3 + 2);
v_isRecordingDeps_369_ = lean_ctor_get_uint8(v_a_361_, sizeof(void*)*3 + 3);
v_maxRecDepth_502_ = lean_ctor_get(v_toCold_364_, 3);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_nat_dec_eq(v_maxRecDepth_502_, v___x_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = lean_nat_dec_eq(v_currRecDepth_365_, v_maxRecDepth_502_);
if (v___x_505_ == 0)
{
goto v___jp_370_;
}
else
{
lean_object* v___x_506_; 
lean_dec_ref(v_e_359_);
lean_inc(v_ref_366_);
v___x_506_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_366_);
return v___x_506_;
}
}
else
{
goto v___jp_370_;
}
v___jp_370_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_currRecDepth_365_, v___x_371_);
lean_inc(v_ref_366_);
lean_inc_ref(v_toCold_364_);
v___x_373_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_373_, 0, v_toCold_364_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
lean_ctor_set(v___x_373_, 2, v_ref_366_);
lean_ctor_set_uint16(v___x_373_, sizeof(void*)*3, v_optionFlags_367_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*3 + 2, v_suppressElabErrors_368_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*3 + 3, v_isRecordingDeps_369_);
v___x_374_ = lean_st_ref_get(v_a_360_);
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_374_, v_e_359_);
lean_dec(v___x_374_);
if (lean_obj_tag(v___x_375_) == 1)
{
lean_object* v_val_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref_known(v___x_373_, 3);
lean_dec_ref(v_e_359_);
v_val_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_val_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 0);
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_val_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_dec(v___x_375_);
switch(lean_obj_tag(v_e_359_))
{
case 7:
{
lean_object* v_binderName_384_; lean_object* v_binderType_385_; lean_object* v_body_386_; uint8_t v_binderInfo_387_; lean_object* v___x_388_; 
v_binderName_384_ = lean_ctor_get(v_e_359_, 0);
v_binderType_385_ = lean_ctor_get(v_e_359_, 1);
v_body_386_ = lean_ctor_get(v_e_359_, 2);
v_binderInfo_387_ = lean_ctor_get_uint8(v_e_359_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_385_);
v___x_388_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_385_, v_a_360_, v___x_373_, v_a_362_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
lean_inc_ref(v_body_386_);
v___x_390_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_386_, v_a_360_, v___x_373_, v_a_362_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; size_t v___x_392_; size_t v___x_393_; uint8_t v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = lean_ptr_addr(v_binderType_385_);
v___x_393_ = lean_ptr_addr(v_a_389_);
v___x_394_ = lean_usize_dec_eq(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_inc(v_binderName_384_);
v___x_395_ = l_Lean_Expr_forallE___override(v_binderName_384_, v_a_389_, v_a_391_, v_binderInfo_387_);
v___x_396_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_395_, v_a_360_);
return v___x_396_;
}
else
{
size_t v___x_397_; size_t v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_ptr_addr(v_body_386_);
v___x_398_ = lean_ptr_addr(v_a_391_);
v___x_399_ = lean_usize_dec_eq(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
lean_inc(v_binderName_384_);
v___x_400_ = l_Lean_Expr_forallE___override(v_binderName_384_, v_a_389_, v_a_391_, v_binderInfo_387_);
v___x_401_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_400_, v_a_360_);
return v___x_401_;
}
else
{
uint8_t v___x_402_; 
v___x_402_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_387_, v_binderInfo_387_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_inc(v_binderName_384_);
v___x_403_ = l_Lean_Expr_forallE___override(v_binderName_384_, v_a_389_, v_a_391_, v_binderInfo_387_);
v___x_404_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_403_, v_a_360_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; 
lean_dec(v_a_391_);
lean_dec(v_a_389_);
lean_inc_ref(v_e_359_);
v___x_405_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v_e_359_, v_a_360_);
return v___x_405_;
}
}
}
}
else
{
lean_dec(v_a_389_);
lean_dec_ref_known(v_e_359_, 3);
return v___x_390_;
}
}
else
{
lean_dec_ref_known(v_e_359_, 3);
lean_dec_ref_known(v___x_373_, 3);
return v___x_388_;
}
}
case 6:
{
lean_object* v_binderName_406_; lean_object* v_binderType_407_; lean_object* v_body_408_; uint8_t v_binderInfo_409_; lean_object* v___x_410_; lean_object* v___x_411_; size_t v___x_412_; size_t v___x_413_; uint8_t v___x_414_; 
v_binderName_406_ = lean_ctor_get(v_e_359_, 0);
v_binderType_407_ = lean_ctor_get(v_e_359_, 1);
v_body_408_ = lean_ctor_get(v_e_359_, 2);
v_binderInfo_409_ = lean_ctor_get_uint8(v_e_359_, sizeof(void*)*3 + 8);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(v_e_359_, v_e_359_, v___x_410_);
v___x_412_ = lean_ptr_addr(v_e_359_);
v___x_413_ = lean_ptr_addr(v___x_411_);
v___x_414_ = lean_usize_dec_eq(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_411_, v_a_360_, v___x_373_, v_a_362_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_417_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 1);
v___x_417_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v_a_416_, v_a_360_);
return v___x_417_;
}
else
{
lean_dec_ref_known(v_e_359_, 3);
return v___x_415_;
}
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v___x_411_);
lean_inc_ref(v_binderType_407_);
v___x_418_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_407_, v_a_360_, v___x_373_, v_a_362_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
lean_inc_ref(v_body_408_);
v___x_420_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_408_, v_a_360_, v___x_373_, v_a_362_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; size_t v___x_422_; size_t v___x_423_; uint8_t v___x_424_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = lean_ptr_addr(v_binderType_407_);
v___x_423_ = lean_ptr_addr(v_a_419_);
v___x_424_ = lean_usize_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_inc(v_binderName_406_);
v___x_425_ = l_Lean_Expr_lam___override(v_binderName_406_, v_a_419_, v_a_421_, v_binderInfo_409_);
v___x_426_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_425_, v_a_360_);
return v___x_426_;
}
else
{
size_t v___x_427_; size_t v___x_428_; uint8_t v___x_429_; 
v___x_427_ = lean_ptr_addr(v_body_408_);
v___x_428_ = lean_ptr_addr(v_a_421_);
v___x_429_ = lean_usize_dec_eq(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_inc(v_binderName_406_);
v___x_430_ = l_Lean_Expr_lam___override(v_binderName_406_, v_a_419_, v_a_421_, v_binderInfo_409_);
v___x_431_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_430_, v_a_360_);
return v___x_431_;
}
else
{
uint8_t v___x_432_; 
v___x_432_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_409_, v_binderInfo_409_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_inc(v_binderName_406_);
v___x_433_ = l_Lean_Expr_lam___override(v_binderName_406_, v_a_419_, v_a_421_, v_binderInfo_409_);
v___x_434_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_433_, v_a_360_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
lean_dec(v_a_421_);
lean_dec(v_a_419_);
lean_inc_ref(v_e_359_);
v___x_435_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v_e_359_, v_a_360_);
return v___x_435_;
}
}
}
}
else
{
lean_dec(v_a_419_);
lean_dec_ref_known(v_e_359_, 3);
return v___x_420_;
}
}
else
{
lean_dec_ref_known(v_e_359_, 3);
lean_dec_ref_known(v___x_373_, 3);
return v___x_418_;
}
}
}
case 8:
{
lean_object* v_declName_436_; lean_object* v_type_437_; lean_object* v_value_438_; lean_object* v_body_439_; uint8_t v_nondep_440_; lean_object* v___x_441_; 
v_declName_436_ = lean_ctor_get(v_e_359_, 0);
v_type_437_ = lean_ctor_get(v_e_359_, 1);
v_value_438_ = lean_ctor_get(v_e_359_, 2);
v_body_439_ = lean_ctor_get(v_e_359_, 3);
v_nondep_440_ = lean_ctor_get_uint8(v_e_359_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_437_);
v___x_441_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_437_, v_a_360_, v___x_373_, v_a_362_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
lean_inc_ref(v_value_438_);
v___x_443_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_438_, v_a_360_, v___x_373_, v_a_362_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
lean_inc_ref(v_body_439_);
v___x_445_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_439_, v_a_360_, v___x_373_, v_a_362_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; size_t v___x_447_; size_t v___x_448_; uint8_t v___x_449_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v___x_447_ = lean_ptr_addr(v_type_437_);
v___x_448_ = lean_ptr_addr(v_a_442_);
v___x_449_ = lean_usize_dec_eq(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc(v_declName_436_);
v___x_450_ = l_Lean_Expr_letE___override(v_declName_436_, v_a_442_, v_a_444_, v_a_446_, v_nondep_440_);
v___x_451_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_450_, v_a_360_);
return v___x_451_;
}
else
{
size_t v___x_452_; size_t v___x_453_; uint8_t v___x_454_; 
v___x_452_ = lean_ptr_addr(v_value_438_);
v___x_453_ = lean_ptr_addr(v_a_444_);
v___x_454_ = lean_usize_dec_eq(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_inc(v_declName_436_);
v___x_455_ = l_Lean_Expr_letE___override(v_declName_436_, v_a_442_, v_a_444_, v_a_446_, v_nondep_440_);
v___x_456_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_455_, v_a_360_);
return v___x_456_;
}
else
{
size_t v___x_457_; size_t v___x_458_; uint8_t v___x_459_; 
v___x_457_ = lean_ptr_addr(v_body_439_);
v___x_458_ = lean_ptr_addr(v_a_446_);
v___x_459_ = lean_usize_dec_eq(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_declName_436_);
v___x_460_ = l_Lean_Expr_letE___override(v_declName_436_, v_a_442_, v_a_444_, v_a_446_, v_nondep_440_);
v___x_461_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_460_, v_a_360_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; 
lean_dec(v_a_446_);
lean_dec(v_a_444_);
lean_dec(v_a_442_);
lean_inc_ref(v_e_359_);
v___x_462_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v_e_359_, v_a_360_);
return v___x_462_;
}
}
}
}
else
{
lean_dec(v_a_444_);
lean_dec(v_a_442_);
lean_dec_ref_known(v_e_359_, 4);
return v___x_445_;
}
}
else
{
lean_dec(v_a_442_);
lean_dec_ref_known(v_e_359_, 4);
lean_dec_ref_known(v___x_373_, 3);
return v___x_443_;
}
}
else
{
lean_dec_ref_known(v_e_359_, 4);
lean_dec_ref_known(v___x_373_, 3);
return v___x_441_;
}
}
case 5:
{
lean_object* v_fn_463_; lean_object* v_arg_464_; lean_object* v___x_465_; 
v_fn_463_ = lean_ctor_get(v_e_359_, 0);
v_arg_464_ = lean_ctor_get(v_e_359_, 1);
lean_inc_ref(v_fn_463_);
v___x_465_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_463_, v_a_360_, v___x_373_, v_a_362_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
lean_inc_ref(v_arg_464_);
v___x_467_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_464_, v_a_360_, v___x_373_, v_a_362_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; size_t v___x_469_; size_t v___x_470_; uint8_t v___x_471_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_ptr_addr(v_fn_463_);
v___x_470_ = lean_ptr_addr(v_a_466_);
v___x_471_ = lean_usize_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = l_Lean_Expr_app___override(v_a_466_, v_a_468_);
v___x_473_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_472_, v_a_360_);
return v___x_473_;
}
else
{
size_t v___x_474_; size_t v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_ptr_addr(v_arg_464_);
v___x_475_ = lean_ptr_addr(v_a_468_);
v___x_476_ = lean_usize_dec_eq(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = l_Lean_Expr_app___override(v_a_466_, v_a_468_);
v___x_478_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_477_, v_a_360_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v_a_468_);
lean_dec(v_a_466_);
lean_inc_ref(v_e_359_);
v___x_479_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v_e_359_, v_a_360_);
return v___x_479_;
}
}
}
else
{
lean_dec(v_a_466_);
lean_dec_ref_known(v_e_359_, 2);
return v___x_467_;
}
}
else
{
lean_dec_ref_known(v_e_359_, 2);
lean_dec_ref_known(v___x_373_, 3);
return v___x_465_;
}
}
case 10:
{
lean_object* v_data_480_; lean_object* v_expr_481_; lean_object* v___x_482_; 
v_data_480_ = lean_ctor_get(v_e_359_, 0);
v_expr_481_ = lean_ctor_get(v_e_359_, 1);
lean_inc_ref(v_expr_481_);
v___x_482_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_481_, v_a_360_, v___x_373_, v_a_362_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_ptr_addr(v_expr_481_);
v___x_485_ = lean_ptr_addr(v_a_483_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_data_480_);
v___x_487_ = l_Lean_Expr_mdata___override(v_data_480_, v_a_483_);
v___x_488_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_487_, v_a_360_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
lean_dec(v_a_483_);
lean_inc_ref(v_e_359_);
v___x_489_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v_e_359_, v_a_360_);
return v___x_489_;
}
}
else
{
lean_dec_ref_known(v_e_359_, 2);
return v___x_482_;
}
}
case 11:
{
lean_object* v_typeName_490_; lean_object* v_idx_491_; lean_object* v_struct_492_; lean_object* v___x_493_; 
v_typeName_490_ = lean_ctor_get(v_e_359_, 0);
v_idx_491_ = lean_ctor_get(v_e_359_, 1);
v_struct_492_ = lean_ctor_get(v_e_359_, 2);
lean_inc_ref(v_struct_492_);
v___x_493_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_492_, v_a_360_, v___x_373_, v_a_362_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = lean_ptr_addr(v_struct_492_);
v___x_496_ = lean_ptr_addr(v_a_494_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_inc(v_idx_491_);
lean_inc(v_typeName_490_);
v___x_498_ = l_Lean_Expr_proj___override(v_typeName_490_, v_idx_491_, v_a_494_);
v___x_499_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v___x_498_, v_a_360_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
lean_dec(v_a_494_);
lean_inc_ref(v_e_359_);
v___x_500_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_359_, v_e_359_, v_a_360_);
return v___x_500_;
}
}
else
{
lean_dec_ref_known(v_e_359_, 3);
return v___x_493_;
}
}
default: 
{
lean_object* v___x_501_; 
lean_dec_ref_known(v___x_373_, 3);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v_e_359_);
return v___x_501_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_359_ = stack[0].m_obj;
lean_object* v_a_360_ = stack[1].m_obj;
lean_object* v_a_361_ = stack[2].m_obj;
lean_object* v_a_362_ = stack[3].m_obj;
lean_object* v_res_507_;
v_res_507_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_359_, v_a_360_, v_a_361_, v_a_362_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(lean_object* v_e_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_515_, v_a_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_518_, v_m_519_, v_a_520_);
lean_dec_ref(v_a_520_);
lean_dec_ref(v_m_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(lean_object* v_00_u03b2_522_, lean_object* v_a_523_, lean_object* v_x_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_523_, v_x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_526_, lean_object* v_a_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_526_, v_a_527_, v_x_528_);
lean_dec(v_x_528_);
lean_dec_ref(v_a_527_);
return v_res_529_;
}
}
lean_object* l_Lean_Meta_Sym_etaReduceWithCache(lean_object* v_e_530_, lean_object* v_c_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_st_mk_ref(v_c_531_);
v___x_536_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_e_530_, v___x_535_, v_a_532_, v_a_533_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_546_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_546_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_st_ref_get(v___x_535_);
lean_dec(v___x_535_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_a_537_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
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
lean_dec(v___x_535_);
v_a_547_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_536_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_536_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_etaReduceWithCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_530_ = stack[0].m_obj;
lean_object* v_c_531_ = stack[1].m_obj;
lean_object* v_a_532_ = stack[2].m_obj;
lean_object* v_a_533_ = stack[3].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_530_, v_c_531_, v_a_532_, v_a_533_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceWithCache___boxed(lean_object* v_e_556_, lean_object* v_c_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_556_, v_c_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
return v_res_561_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__1(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_box(0);
v___x_564_ = lean_unsigned_to_nat(16u);
v___x_565_ = lean_mk_array(v___x_564_, v___x_563_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_etaReduceAll___closed__2(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__1, &l_Lean_Meta_Sym_etaReduceAll___closed__1_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__1);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_566_);
return v___x_568_;
}
}
lean_object* l_Lean_Meta_Sym_etaReduceAll(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_Sym_etaReduceAll___closed__0));
v___x_574_ = lean_find_expr(v___x_573_, v_e_569_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_e_569_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_obj_once(&l_Lean_Meta_Sym_etaReduceAll___closed__2, &l_Lean_Meta_Sym_etaReduceAll___closed__2_once, _init_l_Lean_Meta_Sym_etaReduceAll___closed__2);
v___x_577_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_569_, v___x_576_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_fst_582_; lean_object* v___x_584_; 
v_fst_582_ = lean_ctor_get(v_a_578_, 0);
lean_inc(v_fst_582_);
lean_dec(v_a_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_fst_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_fst_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_a_587_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_577_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_577_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_etaReduceAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_569_ = stack[0].m_obj;
lean_object* v_a_570_ = stack[1].m_obj;
lean_object* v_a_571_ = stack[2].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_Lean_Meta_Sym_etaReduceAll(v_e_569_, v_a_570_, v_a_571_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_etaReduceAll___boxed(lean_object* v_e_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Meta_Sym_etaReduceAll(v_e_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
return v_res_600_;
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
