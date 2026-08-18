// Lean compiler output
// Module: Lean.Meta.Canonicalizer
// Imports: public import Lean.Util.ShareCommon public import Lean.Meta.FunInfo public import Std.Data.HashMap.Raw import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
lean_object* l_instDecidableEqUInt64___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0 = (const lean_object*)&l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1 = (const lean_object*)&l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited;
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0 = (const lean_object*)&l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited = (const lean_object*)&l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0 = (const lean_object*)&l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited = (const lean_object*)&l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1;
static lean_once_cell_t l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2;
static lean_once_cell_t l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object*);
static const lean_array_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value),((lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(187, 6, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg___boxed(lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2, &l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default___closed__2);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default;
return v___x_8_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
size_t v___x_11_; size_t v___x_12_; uint8_t v___x_13_; 
v___x_11_ = lean_ptr_addr(v_a_9_);
v___x_12_ = lean_ptr_addr(v_b_10_);
v___x_13_ = lean_usize_dec_eq(v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(v_a_14_, v_b_15_);
lean_dec_ref(v_b_15_);
lean_dec_ref(v_a_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(lean_object* v_a_20_){
_start:
{
size_t v___x_21_; uint64_t v___x_22_; 
v___x_21_ = lean_ptr_addr(v_a_20_);
v___x_22_ = lean_usize_to_uint64(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(lean_object* v_a_23_){
_start:
{
uint64_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(v_a_23_);
lean_dec_ref(v_a_23_);
v_r_25_ = lean_box_uint64(v_res_24_);
return v_r_25_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0(void){
_start:
{
lean_object* v_cellCount_28_; lean_object* v___x_29_; 
v_cellCount_28_ = lean_unsigned_to_nat(16u);
v___x_29_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1(void){
_start:
{
lean_object* v_cellCount_30_; lean_object* v___x_31_; 
v_cellCount_30_ = lean_unsigned_to_nat(16u);
v___x_31_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_32_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1);
v___x_33_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_32_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object* v_x_39_, uint8_t v_transparency_40_, lean_object* v_s_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_st_mk_ref(v_s_41_);
v___x_48_ = lean_box(v_transparency_40_);
lean_inc(v_a_45_);
lean_inc_ref(v_a_44_);
lean_inc(v_a_43_);
lean_inc_ref(v_a_42_);
lean_inc(v___x_47_);
v___x_49_ = lean_apply_7(v_x_39_, v___x_48_, v___x_47_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, lean_box(0));
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_58_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_58_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_58_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_58_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_54_ = lean_st_ref_get(v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_54_);
if (v_isShared_53_ == 0)
{
v___x_56_ = v___x_52_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_50_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
else
{
lean_dec(v___x_47_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object* v_x_59_, lean_object* v_transparency_60_, lean_object* v_s_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
uint8_t v_transparency_boxed_67_; lean_object* v_res_68_; 
v_transparency_boxed_67_ = lean_unbox(v_transparency_60_);
v_res_68_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v_x_59_, v_transparency_boxed_67_, v_s_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object* v_00_u03b1_69_, lean_object* v_x_70_, uint8_t v_transparency_71_, lean_object* v_s_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v_x_70_, v_transparency_71_, v_s_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object* v_00_u03b1_79_, lean_object* v_x_80_, lean_object* v_transparency_81_, lean_object* v_s_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
uint8_t v_transparency_boxed_88_; lean_object* v_res_89_; 
v_transparency_boxed_88_ = lean_unbox(v_transparency_81_);
v_res_89_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27(v_00_u03b1_79_, v_x_80_, v_transparency_boxed_88_, v_s_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object* v_x_90_, uint8_t v_transparency_91_, lean_object* v_s_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_st_mk_ref(v_s_92_);
v___x_99_ = lean_box(v_transparency_91_);
lean_inc(v_a_96_);
lean_inc_ref(v_a_95_);
lean_inc(v_a_94_);
lean_inc_ref(v_a_93_);
lean_inc(v___x_98_);
v___x_100_ = lean_apply_7(v_x_90_, v___x_99_, v___x_98_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, lean_box(0));
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_110_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_110_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_105_ = lean_st_ref_get(v___x_98_);
lean_dec(v___x_98_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_a_101_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_106_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
lean_dec(v___x_98_);
v_a_111_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_100_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_100_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object* v_x_119_, lean_object* v_transparency_120_, lean_object* v_s_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
uint8_t v_transparency_boxed_127_; lean_object* v_res_128_; 
v_transparency_boxed_127_ = lean_unbox(v_transparency_120_);
v_res_128_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(v_x_119_, v_transparency_boxed_127_, v_s_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object* v_00_u03b1_129_, lean_object* v_x_130_, uint8_t v_transparency_131_, lean_object* v_s_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(v_x_130_, v_transparency_131_, v_s_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object* v_00_u03b1_139_, lean_object* v_x_140_, lean_object* v_transparency_141_, lean_object* v_s_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
uint8_t v_transparency_boxed_148_; lean_object* v_res_149_; 
v_transparency_boxed_148_ = lean_unbox(v_transparency_141_);
v_res_149_ = l_Lean_Meta_Canonicalizer_CanonM_run(v_00_u03b1_139_, v_x_140_, v_transparency_boxed_148_, v_s_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object* v_e_150_, lean_object* v_____do__lift_151_){
_start:
{
lean_object* v_cache_152_; lean_object* v_keyArray_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_cache_152_ = lean_ctor_get(v_____do__lift_151_, 0);
v_keyArray_153_ = lean_ctor_get(v_cache_152_, 1);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_array_get_size(v_keyArray_153_);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v_e_150_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; 
v___f_158_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_159_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_158_, v___f_159_, v_cache_152_, v_e_150_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object* v_e_161_, lean_object* v_____do__lift_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(v_e_161_, v_____do__lift_162_);
lean_dec_ref(v_____do__lift_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object* v_e_164_, uint64_t v_key_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_168_; lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v_cache_174_; lean_object* v_keyToExprs_175_; lean_object* v_size_176_; lean_object* v_keyArray_177_; lean_object* v___x_178_; lean_object* v___y_180_; lean_object* v_i_181_; lean_object* v___y_189_; lean_object* v_i_190_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_168_ = lean_st_ref_take(v_a_166_);
v_cache_174_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_cache_174_);
v_keyToExprs_175_ = lean_ctor_get(v___x_168_, 1);
lean_inc_ref(v_keyToExprs_175_);
v_size_176_ = lean_ctor_get(v_cache_174_, 0);
v_keyArray_177_ = lean_ctor_get(v_cache_174_, 1);
v___x_178_ = lean_box(0);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_array_get_size(v_keyArray_177_);
v___x_199_ = lean_nat_dec_lt(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec_ref(v_keyToExprs_175_);
lean_dec_ref(v_cache_174_);
lean_dec_ref(v_e_164_);
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_168_;
goto v___jp_169_;
}
else
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_260_; 
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_261_ = lean_ctor_get(v___x_168_, 1);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v___x_168_, 0);
lean_dec(v_unused_262_);
v___x_201_ = v___x_168_;
v_isShared_202_ = v_isSharedCheck_260_;
goto v_resetjp_200_;
}
else
{
lean_dec(v___x_168_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_260_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___y_206_; lean_object* v___x_233_; 
v___f_203_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_204_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
lean_inc_ref(v_e_164_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_203_, v___f_204_, v_cache_174_, v_e_164_);
switch(lean_obj_tag(v___x_233_))
{
case 0:
{
lean_object* v_index_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_inc(v_size_176_);
lean_del_object(v___x_201_);
v_index_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_index_234_);
lean_dec_ref_known(v___x_233_, 3);
v___x_235_ = lean_box_uint64(v_key_165_);
v___x_236_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_174_, v_size_176_, v_index_234_, v_e_164_, v___x_235_);
lean_dec(v_index_234_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v_keyToExprs_175_);
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_237_;
goto v___jp_169_;
}
case 1:
{
lean_object* v_index_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
lean_del_object(v___x_201_);
v_index_238_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_index_238_);
lean_dec_ref_known(v___x_233_, 1);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_size_176_, v___x_239_);
v___x_241_ = lean_nat_dec_lt(v___x_240_, v___x_198_);
if (v___x_241_ == 0)
{
lean_dec(v___x_240_);
lean_dec(v_index_238_);
goto v___jp_221_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_242_ = lean_unsigned_to_nat(4u);
v___x_243_ = lean_nat_mul(v___x_240_, v___x_242_);
v___x_244_ = lean_unsigned_to_nat(3u);
v___x_245_ = lean_nat_mul(v___x_198_, v___x_244_);
v___x_246_ = lean_nat_dec_le(v___x_243_, v___x_245_);
lean_dec(v___x_245_);
lean_dec(v___x_243_);
if (v___x_246_ == 0)
{
lean_dec(v___x_240_);
lean_dec(v_index_238_);
goto v___jp_221_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_box_uint64(v_key_165_);
v___x_248_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_174_, v___x_240_, v_index_238_, v_e_164_, v___x_247_);
lean_dec(v_index_238_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_keyToExprs_175_);
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_249_;
goto v___jp_169_;
}
}
}
default: 
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_add(v_size_176_, v___x_250_);
v___x_252_ = lean_nat_dec_lt(v___x_251_, v___x_198_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v___x_251_);
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_203_, v___f_204_, v_cache_174_);
v___y_206_ = v___x_253_;
goto v___jp_205_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_254_ = lean_unsigned_to_nat(4u);
v___x_255_ = lean_nat_mul(v___x_251_, v___x_254_);
lean_dec(v___x_251_);
v___x_256_ = lean_unsigned_to_nat(3u);
v___x_257_ = lean_nat_mul(v___x_198_, v___x_256_);
v___x_258_ = lean_nat_dec_le(v___x_255_, v___x_257_);
lean_dec(v___x_257_);
lean_dec(v___x_255_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_203_, v___f_204_, v_cache_174_);
v___y_206_ = v___x_259_;
goto v___jp_205_;
}
else
{
v___y_206_ = v_cache_174_;
goto v___jp_205_;
}
}
}
}
v___jp_205_:
{
lean_object* v___x_207_; 
lean_inc_ref(v_e_164_);
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_203_, v___f_204_, v___y_206_, v_e_164_);
switch(lean_obj_tag(v___x_207_))
{
case 0:
{
lean_object* v_index_208_; lean_object* v_size_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v_index_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_index_208_);
lean_dec_ref_known(v___x_207_, 3);
v_size_209_ = lean_ctor_get(v___y_206_, 0);
lean_inc(v_size_209_);
v___x_210_ = lean_box_uint64(v_key_165_);
v___x_211_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_206_, v_size_209_, v_index_208_, v_e_164_, v___x_210_);
lean_dec(v_index_208_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_211_);
v___x_213_ = v___x_201_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_keyToExprs_175_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_213_;
goto v___jp_169_;
}
}
case 1:
{
lean_object* v_index_215_; 
lean_del_object(v___x_201_);
v_index_215_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_index_215_);
lean_dec_ref_known(v___x_207_, 1);
v___y_189_ = v___y_206_;
v_i_190_ = v_index_215_;
goto v___jp_188_;
}
default: 
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_206_, v___x_197_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_index_217_; 
lean_del_object(v___x_201_);
v_index_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_217_);
lean_dec_ref_known(v___x_216_, 1);
v___y_189_ = v___y_206_;
v_i_190_ = v_index_217_;
goto v___jp_188_;
}
else
{
lean_object* v___x_219_; 
lean_dec_ref(v_e_164_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___y_206_);
v___x_219_ = v___x_201_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___y_206_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_keyToExprs_175_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_219_;
goto v___jp_169_;
}
}
}
}
}
v___jp_221_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_203_, v___f_204_, v_cache_174_);
lean_inc_ref(v_e_164_);
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_203_, v___f_204_, v___x_222_, v_e_164_);
switch(lean_obj_tag(v___x_223_))
{
case 0:
{
lean_object* v_index_224_; lean_object* v_size_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_index_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_index_224_);
lean_dec_ref_known(v___x_223_, 3);
v_size_225_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_size_225_);
v___x_226_ = lean_box_uint64(v_key_165_);
v___x_227_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_222_, v_size_225_, v_index_224_, v_e_164_, v___x_226_);
lean_dec(v_index_224_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_keyToExprs_175_);
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_228_;
goto v___jp_169_;
}
case 1:
{
lean_object* v_index_229_; 
v_index_229_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_index_229_);
lean_dec_ref_known(v___x_223_, 1);
v___y_180_ = v___x_222_;
v_i_181_ = v_index_229_;
goto v___jp_179_;
}
default: 
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_222_, v___x_197_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_index_231_; 
v_index_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_231_);
lean_dec_ref_known(v___x_230_, 1);
v___y_180_ = v___x_222_;
v_i_181_ = v_index_231_;
goto v___jp_179_;
}
else
{
lean_object* v___x_232_; 
lean_dec_ref(v_e_164_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_222_);
lean_ctor_set(v___x_232_, 1, v_keyToExprs_175_);
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_232_;
goto v___jp_169_;
}
}
}
}
}
}
v___jp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_st_ref_put(v_a_166_, v_snd_171_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_fst_170_);
return v___x_173_;
}
v___jp_179_:
{
lean_object* v_size_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_size_182_ = lean_ctor_get(v___y_180_, 0);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_size_182_, v___x_183_);
v___x_185_ = lean_box_uint64(v_key_165_);
v___x_186_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_180_, v___x_184_, v_i_181_, v_e_164_, v___x_185_);
lean_dec(v_i_181_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_keyToExprs_175_);
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_187_;
goto v___jp_169_;
}
v___jp_188_:
{
lean_object* v_size_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_size_191_ = lean_ctor_get(v___y_189_, 0);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_add(v_size_191_, v___x_192_);
v___x_194_ = lean_box_uint64(v_key_165_);
v___x_195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_189_, v___x_193_, v_i_190_, v_e_164_, v___x_194_);
lean_dec(v_i_190_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_keyToExprs_175_);
v_fst_170_ = v___x_178_;
v_snd_171_ = v___x_196_;
goto v___jp_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object* v_e_263_, lean_object* v_key_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
uint64_t v_key_boxed_267_; lean_object* v_res_268_; 
v_key_boxed_267_ = lean_unbox_uint64(v_key_264_);
lean_dec_ref(v_key_264_);
v_res_268_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_263_, v_key_boxed_267_, v_a_265_);
lean_dec(v_a_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object* v_e_269_, uint64_t v_key_270_, uint8_t v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; lean_object* v_fst_280_; lean_object* v_snd_281_; lean_object* v_cache_284_; lean_object* v_keyToExprs_285_; lean_object* v_size_286_; lean_object* v_keyArray_287_; lean_object* v___x_288_; lean_object* v___y_290_; lean_object* v_i_291_; lean_object* v___y_299_; lean_object* v_i_300_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_278_ = lean_st_ref_take(v_a_272_);
v_cache_284_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_cache_284_);
v_keyToExprs_285_ = lean_ctor_get(v___x_278_, 1);
lean_inc_ref(v_keyToExprs_285_);
v_size_286_ = lean_ctor_get(v_cache_284_, 0);
v_keyArray_287_ = lean_ctor_get(v_cache_284_, 1);
v___x_288_ = lean_box(0);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_array_get_size(v_keyArray_287_);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec_ref(v_keyToExprs_285_);
lean_dec_ref(v_cache_284_);
lean_dec_ref(v_e_269_);
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_278_;
goto v___jp_279_;
}
else
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_370_; 
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; lean_object* v_unused_372_; 
v_unused_371_ = lean_ctor_get(v___x_278_, 1);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_372_);
v___x_311_ = v___x_278_;
v_isShared_312_ = v_isSharedCheck_370_;
goto v_resetjp_310_;
}
else
{
lean_dec(v___x_278_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_370_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___y_316_; lean_object* v___x_343_; 
v___f_313_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_314_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
lean_inc_ref(v_e_269_);
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_313_, v___f_314_, v_cache_284_, v_e_269_);
switch(lean_obj_tag(v___x_343_))
{
case 0:
{
lean_object* v_index_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc(v_size_286_);
lean_del_object(v___x_311_);
v_index_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_index_344_);
lean_dec_ref_known(v___x_343_, 3);
v___x_345_ = lean_box_uint64(v_key_270_);
v___x_346_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_284_, v_size_286_, v_index_344_, v_e_269_, v___x_345_);
lean_dec(v_index_344_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v_keyToExprs_285_);
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_347_;
goto v___jp_279_;
}
case 1:
{
lean_object* v_index_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
lean_del_object(v___x_311_);
v_index_348_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_index_348_);
lean_dec_ref_known(v___x_343_, 1);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_size_286_, v___x_349_);
v___x_351_ = lean_nat_dec_lt(v___x_350_, v___x_308_);
if (v___x_351_ == 0)
{
lean_dec(v___x_350_);
lean_dec(v_index_348_);
goto v___jp_331_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_352_ = lean_unsigned_to_nat(4u);
v___x_353_ = lean_nat_mul(v___x_350_, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(3u);
v___x_355_ = lean_nat_mul(v___x_308_, v___x_354_);
v___x_356_ = lean_nat_dec_le(v___x_353_, v___x_355_);
lean_dec(v___x_355_);
lean_dec(v___x_353_);
if (v___x_356_ == 0)
{
lean_dec(v___x_350_);
lean_dec(v_index_348_);
goto v___jp_331_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_box_uint64(v_key_270_);
v___x_358_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_284_, v___x_350_, v_index_348_, v_e_269_, v___x_357_);
lean_dec(v_index_348_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_keyToExprs_285_);
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_359_;
goto v___jp_279_;
}
}
}
default: 
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_size_286_, v___x_360_);
v___x_362_ = lean_nat_dec_lt(v___x_361_, v___x_308_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v___x_361_);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_313_, v___f_314_, v_cache_284_);
v___y_316_ = v___x_363_;
goto v___jp_315_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_364_ = lean_unsigned_to_nat(4u);
v___x_365_ = lean_nat_mul(v___x_361_, v___x_364_);
lean_dec(v___x_361_);
v___x_366_ = lean_unsigned_to_nat(3u);
v___x_367_ = lean_nat_mul(v___x_308_, v___x_366_);
v___x_368_ = lean_nat_dec_le(v___x_365_, v___x_367_);
lean_dec(v___x_367_);
lean_dec(v___x_365_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_313_, v___f_314_, v_cache_284_);
v___y_316_ = v___x_369_;
goto v___jp_315_;
}
else
{
v___y_316_ = v_cache_284_;
goto v___jp_315_;
}
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; 
lean_inc_ref(v_e_269_);
v___x_317_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_313_, v___f_314_, v___y_316_, v_e_269_);
switch(lean_obj_tag(v___x_317_))
{
case 0:
{
lean_object* v_index_318_; lean_object* v_size_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v_index_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_index_318_);
lean_dec_ref_known(v___x_317_, 3);
v_size_319_ = lean_ctor_get(v___y_316_, 0);
lean_inc(v_size_319_);
v___x_320_ = lean_box_uint64(v_key_270_);
v___x_321_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_316_, v_size_319_, v_index_318_, v_e_269_, v___x_320_);
lean_dec(v_index_318_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_321_);
v___x_323_ = v___x_311_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_keyToExprs_285_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_323_;
goto v___jp_279_;
}
}
case 1:
{
lean_object* v_index_325_; 
lean_del_object(v___x_311_);
v_index_325_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_index_325_);
lean_dec_ref_known(v___x_317_, 1);
v___y_299_ = v___y_316_;
v_i_300_ = v_index_325_;
goto v___jp_298_;
}
default: 
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_316_, v___x_307_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_index_327_; 
lean_del_object(v___x_311_);
v_index_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_index_327_);
lean_dec_ref_known(v___x_326_, 1);
v___y_299_ = v___y_316_;
v_i_300_ = v_index_327_;
goto v___jp_298_;
}
else
{
lean_object* v___x_329_; 
lean_dec_ref(v_e_269_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___y_316_);
v___x_329_ = v___x_311_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___y_316_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_keyToExprs_285_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_329_;
goto v___jp_279_;
}
}
}
}
}
v___jp_331_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_313_, v___f_314_, v_cache_284_);
lean_inc_ref(v_e_269_);
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_313_, v___f_314_, v___x_332_, v_e_269_);
switch(lean_obj_tag(v___x_333_))
{
case 0:
{
lean_object* v_index_334_; lean_object* v_size_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_index_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_index_334_);
lean_dec_ref_known(v___x_333_, 3);
v_size_335_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_size_335_);
v___x_336_ = lean_box_uint64(v_key_270_);
v___x_337_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_332_, v_size_335_, v_index_334_, v_e_269_, v___x_336_);
lean_dec(v_index_334_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_keyToExprs_285_);
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_338_;
goto v___jp_279_;
}
case 1:
{
lean_object* v_index_339_; 
v_index_339_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_index_339_);
lean_dec_ref_known(v___x_333_, 1);
v___y_290_ = v___x_332_;
v_i_291_ = v_index_339_;
goto v___jp_289_;
}
default: 
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_332_, v___x_307_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_index_341_; 
v_index_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_index_341_);
lean_dec_ref_known(v___x_340_, 1);
v___y_290_ = v___x_332_;
v_i_291_ = v_index_341_;
goto v___jp_289_;
}
else
{
lean_object* v___x_342_; 
lean_dec_ref(v_e_269_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_332_);
lean_ctor_set(v___x_342_, 1, v_keyToExprs_285_);
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_342_;
goto v___jp_279_;
}
}
}
}
}
}
v___jp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_st_ref_put(v_a_272_, v_snd_281_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v_fst_280_);
return v___x_283_;
}
v___jp_289_:
{
lean_object* v_size_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_size_292_ = lean_ctor_get(v___y_290_, 0);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_size_292_, v___x_293_);
v___x_295_ = lean_box_uint64(v_key_270_);
v___x_296_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_290_, v___x_294_, v_i_291_, v_e_269_, v___x_295_);
lean_dec(v_i_291_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_keyToExprs_285_);
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_297_;
goto v___jp_279_;
}
v___jp_298_:
{
lean_object* v_size_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_size_301_ = lean_ctor_get(v___y_299_, 0);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_size_301_, v___x_302_);
v___x_304_ = lean_box_uint64(v_key_270_);
v___x_305_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_299_, v___x_303_, v_i_300_, v_e_269_, v___x_304_);
lean_dec(v_i_300_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_keyToExprs_285_);
v_fst_280_ = v___x_288_;
v_snd_281_ = v___x_306_;
goto v___jp_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object* v_e_373_, lean_object* v_key_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
uint64_t v_key_boxed_382_; uint8_t v_a_boxed_383_; lean_object* v_res_384_; 
v_key_boxed_382_ = lean_unbox_uint64(v_key_374_);
lean_dec_ref(v_key_374_);
v_a_boxed_383_ = lean_unbox(v_a_375_);
v_res_384_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(v_e_373_, v_key_boxed_382_, v_a_boxed_383_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(lean_object* v_e_385_, lean_object* v___y_386_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_Expr_hasMVar(v_e_385_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v_e_385_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v_mctx_391_; lean_object* v___x_392_; lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v___x_395_; lean_object* v_cache_396_; lean_object* v_zetaDeltaFVarIds_397_; lean_object* v_postponed_398_; lean_object* v_diag_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_408_; 
v___x_390_ = lean_st_ref_get(v___y_386_);
v_mctx_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_mctx_391_);
lean_dec(v___x_390_);
v___x_392_ = l_Lean_instantiateMVarsCore(v_mctx_391_, v_e_385_);
v_fst_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_394_);
lean_dec_ref(v___x_392_);
v___x_395_ = lean_st_ref_take(v___y_386_);
v_cache_396_ = lean_ctor_get(v___x_395_, 1);
v_zetaDeltaFVarIds_397_ = lean_ctor_get(v___x_395_, 2);
v_postponed_398_ = lean_ctor_get(v___x_395_, 3);
v_diag_399_ = lean_ctor_get(v___x_395_, 4);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_395_, 0);
lean_dec(v_unused_409_);
v___x_401_ = v___x_395_;
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_diag_399_);
lean_inc(v_postponed_398_);
lean_inc(v_zetaDeltaFVarIds_397_);
lean_inc(v_cache_396_);
lean_dec(v___x_395_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_snd_394_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_snd_394_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_cache_396_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_zetaDeltaFVarIds_397_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_postponed_398_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_diag_399_);
v___x_404_ = v_reuseFailAlloc_407_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_st_ref_put(v___y_386_, v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_fst_393_);
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg___boxed(lean_object* v_e_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v_e_410_, v___y_411_);
lean_dec(v___y_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(lean_object* v_e_414_, uint8_t v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v_e_414_, v___y_418_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___boxed(lean_object* v_e_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
uint8_t v___y_14072__boxed_431_; lean_object* v_res_432_; 
v___y_14072__boxed_431_ = lean_unbox(v___y_424_);
v_res_432_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(v_e_423_, v___y_14072__boxed_431_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(lean_object* v_m_433_, lean_object* v_query_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_zero_438_; uint8_t v_isZero_439_; 
v_zero_438_ = lean_unsigned_to_nat(0u);
v_isZero_439_ = lean_nat_dec_eq(v_x_436_, v_zero_438_);
if (v_isZero_439_ == 1)
{
lean_dec(v_x_437_);
lean_dec(v_x_436_);
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_box(2);
return v___x_440_;
}
else
{
lean_object* v_val_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_val_441_ = lean_ctor_get(v_x_435_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_435_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v_x_435_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_val_441_);
lean_dec(v_x_435_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_val_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v_keyArray_449_; lean_object* v_valueArray_450_; lean_object* v___x_451_; uint8_t v_isSome_452_; 
v_keyArray_449_ = lean_ctor_get(v_m_433_, 1);
v_valueArray_450_ = lean_ctor_get(v_m_433_, 2);
v___x_451_ = lean_array_fget_borrowed(v_keyArray_449_, v_x_437_);
v_isSome_452_ = lean_noption_is_some(v___x_451_);
if (v_isSome_452_ == 0)
{
lean_dec(v_x_436_);
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v_x_437_);
return v___x_453_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_x_437_);
v_val_454_ = lean_ctor_get(v_x_435_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_x_435_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v_x_435_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v_x_435_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_val_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_one_462_; lean_object* v_n_463_; lean_object* v___y_465_; 
v_one_462_ = lean_unsigned_to_nat(1u);
v_n_463_ = lean_nat_sub(v_x_436_, v_one_462_);
lean_dec(v_x_436_);
if (v_isSome_452_ == 0)
{
goto v___jp_471_;
}
else
{
lean_object* v___x_473_; uint8_t v_isSome_474_; 
v___x_473_ = lean_array_fget_borrowed(v_valueArray_450_, v_x_437_);
v_isSome_474_ = lean_noption_is_some(v___x_473_);
if (v_isSome_474_ == 0)
{
goto v___jp_471_;
}
else
{
lean_object* v_val_475_; size_t v___x_476_; size_t v___x_477_; uint8_t v___x_478_; 
lean_inc(v___x_451_);
v_val_475_ = lean_noption_get(v___x_451_);
v___x_476_ = lean_ptr_addr(v_val_475_);
v___x_477_ = lean_ptr_addr(v_query_434_);
v___x_478_ = lean_usize_dec_eq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
lean_dec(v_val_475_);
v___x_479_ = lean_array_get_size(v_keyArray_449_);
v___x_480_ = lean_nat_add(v_x_437_, v_one_462_);
lean_dec(v_x_437_);
v___x_481_ = lean_nat_dec_lt(v___x_480_, v___x_479_);
if (v___x_481_ == 0)
{
lean_dec(v___x_480_);
v_x_436_ = v_n_463_;
v_x_437_ = v_zero_438_;
goto _start;
}
else
{
v_x_436_ = v_n_463_;
v_x_437_ = v___x_480_;
goto _start;
}
}
else
{
lean_object* v_val_484_; lean_object* v___x_485_; 
lean_dec(v_n_463_);
lean_dec(v_x_435_);
lean_inc(v___x_473_);
v_val_484_ = lean_noption_get(v___x_473_);
v___x_485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_485_, 0, v_x_437_);
lean_ctor_set(v___x_485_, 1, v_val_475_);
lean_ctor_set(v___x_485_, 2, v_val_484_);
return v___x_485_;
}
}
}
v___jp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_array_get_size(v_keyArray_449_);
v___x_467_ = lean_nat_add(v_x_437_, v_one_462_);
lean_dec(v_x_437_);
v___x_468_ = lean_nat_dec_lt(v___x_467_, v___x_466_);
if (v___x_468_ == 0)
{
lean_dec(v___x_467_);
v_x_435_ = v___y_465_;
v_x_436_ = v_n_463_;
v_x_437_ = v_zero_438_;
goto _start;
}
else
{
v_x_435_ = v___y_465_;
v_x_436_ = v_n_463_;
v_x_437_ = v___x_467_;
goto _start;
}
}
v___jp_471_:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v___x_472_; 
lean_inc(v_x_437_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_x_437_);
v___y_465_ = v___x_472_;
goto v___jp_464_;
}
else
{
v___y_465_ = v_x_435_;
goto v___jp_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg___boxed(lean_object* v_m_486_, lean_object* v_query_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_m_486_, v_query_487_, v_x_488_, v_x_489_, v_x_490_);
lean_dec_ref(v_query_487_);
lean_dec_ref(v_m_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object* v_m_492_, lean_object* v_query_493_){
_start:
{
lean_object* v_keyArray_494_; lean_object* v___x_495_; size_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v_fold_500_; uint64_t v___x_501_; uint64_t v___x_502_; uint64_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_keyArray_494_ = lean_ctor_get(v_m_492_, 1);
v___x_495_ = lean_array_get_size(v_keyArray_494_);
v___x_496_ = lean_ptr_addr(v_query_493_);
v___x_497_ = lean_usize_to_uint64(v___x_496_);
v___x_498_ = 32ULL;
v___x_499_ = lean_uint64_shift_right(v___x_497_, v___x_498_);
v_fold_500_ = lean_uint64_xor(v___x_497_, v___x_499_);
v___x_501_ = 16ULL;
v___x_502_ = lean_uint64_shift_right(v_fold_500_, v___x_501_);
v___x_503_ = lean_uint64_xor(v_fold_500_, v___x_502_);
v___x_504_ = lean_uint64_to_usize(v___x_503_);
v___x_505_ = lean_usize_of_nat(v___x_495_);
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_sub(v___x_505_, v___x_506_);
v___x_508_ = lean_usize_land(v___x_504_, v___x_507_);
v___x_509_ = lean_usize_to_nat(v___x_508_);
v___x_510_ = lean_box(0);
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_m_492_, v_query_493_, v___x_510_, v___x_495_, v___x_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object* v_m_512_, lean_object* v_query_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_m_512_, v_query_513_);
lean_dec_ref(v_query_513_);
lean_dec_ref(v_m_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___redArg(lean_object* v_m_515_, lean_object* v_query_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_m_515_, v_query_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_index_518_; lean_object* v_key_519_; lean_object* v_value_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_index_518_ = lean_ctor_get(v___x_517_, 0);
v_key_519_ = lean_ctor_get(v___x_517_, 1);
v_value_520_ = lean_ctor_get(v___x_517_, 2);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_517_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_value_520_);
lean_inc(v_key_519_);
lean_inc(v_index_518_);
lean_dec(v___x_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_index_518_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_key_519_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_value_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v___x_517_);
v___x_528_ = lean_box(1);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___redArg___boxed(lean_object* v_m_529_, lean_object* v_query_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___redArg(v_m_529_, v_query_530_);
lean_dec_ref(v_query_530_);
lean_dec_ref(v_m_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___redArg(lean_object* v_m_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___redArg(v_m_532_, v_a_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_value_535_; lean_object* v___x_536_; 
v_value_535_ = lean_ctor_get(v___x_534_, 2);
lean_inc(v_value_535_);
lean_dec_ref_known(v___x_534_, 3);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_value_535_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___redArg___boxed(lean_object* v_m_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___redArg(v_m_538_, v_a_539_);
lean_dec_ref(v_a_539_);
lean_dec_ref(v_m_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___redArg(lean_object* v_b_541_, lean_object* v_acc_542_, lean_object* v_i_543_){
_start:
{
lean_object* v___y_545_; lean_object* v_keyArray_553_; lean_object* v_valueArray_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_keyArray_553_ = lean_ctor_get(v_b_541_, 1);
v_valueArray_554_ = lean_ctor_get(v_b_541_, 2);
v___x_555_ = lean_array_get_size(v_keyArray_553_);
v___x_556_ = lean_nat_dec_lt(v_i_543_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_i_543_);
return v_acc_542_;
}
else
{
lean_object* v___x_557_; uint8_t v_isSome_558_; 
v___x_557_ = lean_array_fget_borrowed(v_keyArray_553_, v_i_543_);
v_isSome_558_ = lean_noption_is_some(v___x_557_);
if (v_isSome_558_ == 0)
{
goto v___jp_549_;
}
else
{
lean_object* v___x_559_; uint8_t v_isSome_560_; 
v___x_559_ = lean_array_fget_borrowed(v_valueArray_554_, v_i_543_);
v_isSome_560_ = lean_noption_is_some(v___x_559_);
if (v_isSome_560_ == 0)
{
goto v___jp_549_;
}
else
{
lean_object* v_val_561_; lean_object* v_val_562_; lean_object* v_i_564_; lean_object* v___x_569_; 
lean_inc(v___x_557_);
v_val_561_ = lean_noption_get(v___x_557_);
lean_inc(v___x_559_);
v_val_562_ = lean_noption_get(v___x_559_);
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_acc_542_, v_val_561_);
switch(lean_obj_tag(v___x_569_))
{
case 0:
{
lean_object* v_index_570_; lean_object* v_size_571_; lean_object* v___x_572_; 
v_index_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_index_570_);
lean_dec_ref_known(v___x_569_, 3);
v_size_571_ = lean_ctor_get(v_acc_542_, 0);
lean_inc(v_size_571_);
v___x_572_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_542_, v_size_571_, v_index_570_, v_val_561_, v_val_562_);
lean_dec(v_index_570_);
v___y_545_ = v___x_572_;
goto v___jp_544_;
}
case 1:
{
lean_object* v_index_573_; 
v_index_573_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_index_573_);
lean_dec_ref_known(v___x_569_, 1);
v_i_564_ = v_index_573_;
goto v___jp_563_;
}
default: 
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_542_, v___x_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_index_576_; 
v_index_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_index_576_);
lean_dec_ref_known(v___x_575_, 1);
v_i_564_ = v_index_576_;
goto v___jp_563_;
}
else
{
lean_dec(v_val_562_);
lean_dec(v_val_561_);
v___y_545_ = v_acc_542_;
goto v___jp_544_;
}
}
}
v___jp_563_:
{
lean_object* v_size_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_size_565_ = lean_ctor_get(v_acc_542_, 0);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_size_565_, v___x_566_);
v___x_568_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_542_, v___x_567_, v_i_564_, v_val_561_, v_val_562_);
lean_dec(v_i_564_);
v___y_545_ = v___x_568_;
goto v___jp_544_;
}
}
}
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_add(v_i_543_, v___x_546_);
lean_dec(v_i_543_);
v_acc_542_ = v___y_545_;
v_i_543_ = v___x_547_;
goto _start;
}
v___jp_549_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_add(v_i_543_, v___x_550_);
lean_dec(v_i_543_);
v_i_543_ = v___x_551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_b_577_, lean_object* v_acc_578_, lean_object* v_i_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___redArg(v_b_577_, v_acc_578_, v_i_579_);
lean_dec_ref(v_b_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___redArg(lean_object* v_init_581_, lean_object* v_b_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___redArg(v_b_582_, v_init_581_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___redArg___boxed(lean_object* v_init_585_, lean_object* v_b_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___redArg(v_init_585_, v_b_586_);
lean_dec_ref(v_b_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object* v_m_588_){
_start:
{
lean_object* v_keyArray_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_cellCount_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_target_596_; lean_object* v___x_597_; 
v_keyArray_589_ = lean_ctor_get(v_m_588_, 1);
v___x_590_ = lean_array_get_size(v_keyArray_589_);
v___x_591_ = lean_unsigned_to_nat(2u);
v_cellCount_592_ = lean_nat_mul(v___x_590_, v___x_591_);
v___x_593_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_592_);
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_592_);
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_592_);
v_target_596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_596_, 0, v___x_593_);
lean_ctor_set(v_target_596_, 1, v___x_594_);
lean_ctor_set(v_target_596_, 2, v___x_595_);
v___x_597_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___redArg(v_target_596_, v_m_588_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object* v_m_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_m_598_);
lean_dec_ref(v_m_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* v_e_606_, uint8_t v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_t_615_; lean_object* v_b_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_639_; uint64_t v___y_640_; lean_object* v_snd_641_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; uint64_t v___y_649_; lean_object* v_i_650_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; uint64_t v___y_661_; lean_object* v___y_662_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; uint64_t v___y_677_; lean_object* v_i_678_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; uint64_t v___y_689_; lean_object* v___y_690_; uint64_t v_key_703_; lean_object* v___y_704_; lean_object* v___y_751_; lean_object* v_info_752_; uint8_t v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_766_; uint8_t v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___x_786_; lean_object* v_cache_874_; lean_object* v_keyArray_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_786_ = lean_st_ref_get(v_a_608_);
v_cache_874_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_cache_874_);
lean_dec(v___x_786_);
v_keyArray_875_ = lean_ctor_get(v_cache_874_, 1);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_array_get_size(v_keyArray_875_);
v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_dec_ref(v_cache_874_);
goto v___jp_787_;
}
else
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___redArg(v_cache_874_, v_e_606_);
lean_dec_ref(v_cache_874_);
if (lean_obj_tag(v___x_879_) == 1)
{
lean_object* v_val_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v_e_606_);
v_val_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_val_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set_tag(v___x_882_, 0);
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_val_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_dec(v___x_879_);
goto v___jp_787_;
}
}
v___jp_614_:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_t_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_b_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_637_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_637_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_637_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_637_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
uint64_t v___x_630_; uint64_t v___x_631_; uint64_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_630_ = lean_unbox_uint64(v_a_624_);
lean_dec(v_a_624_);
v___x_631_ = lean_unbox_uint64(v_a_626_);
lean_dec(v_a_626_);
v___x_632_ = lean_uint64_mix_hash(v___x_630_, v___x_631_);
v___x_633_ = lean_box_uint64(v___x_632_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_633_);
v___x_635_ = v___x_628_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_dec(v_a_624_);
return v___x_625_;
}
}
else
{
lean_dec_ref(v_b_616_);
return v___x_623_;
}
}
v___jp_638_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_st_ref_put(v___y_639_, v_snd_641_);
v___x_643_ = lean_box_uint64(v___y_640_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
v___jp_645_:
{
lean_object* v_size_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_size_651_ = lean_ctor_get(v___y_648_, 0);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_add(v_size_651_, v___x_652_);
v___x_654_ = lean_box_uint64(v___y_649_);
v___x_655_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_648_, v___x_653_, v_i_650_, v_e_606_, v___x_654_);
lean_dec(v_i_650_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___y_647_);
v___y_639_ = v___y_646_;
v___y_640_ = v___y_649_;
v_snd_641_ = v___x_656_;
goto v___jp_638_;
}
v___jp_657_:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v___y_662_, v_e_606_);
switch(lean_obj_tag(v___x_663_))
{
case 0:
{
lean_object* v_index_664_; lean_object* v_size_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v___y_658_);
v_index_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_index_664_);
lean_dec_ref_known(v___x_663_, 3);
v_size_665_ = lean_ctor_get(v___y_662_, 0);
lean_inc(v_size_665_);
v___x_666_ = lean_box_uint64(v___y_661_);
v___x_667_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_662_, v_size_665_, v_index_664_, v_e_606_, v___x_666_);
lean_dec(v_index_664_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___y_660_);
v___y_639_ = v___y_659_;
v___y_640_ = v___y_661_;
v_snd_641_ = v___x_668_;
goto v___jp_638_;
}
case 1:
{
lean_object* v_index_669_; 
lean_dec(v___y_658_);
v_index_669_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_index_669_);
lean_dec_ref_known(v___x_663_, 1);
v___y_646_ = v___y_659_;
v___y_647_ = v___y_660_;
v___y_648_ = v___y_662_;
v___y_649_ = v___y_661_;
v_i_650_ = v_index_669_;
goto v___jp_645_;
}
default: 
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_662_, v___y_658_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_index_671_; 
v_index_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_index_671_);
lean_dec_ref_known(v___x_670_, 1);
v___y_646_ = v___y_659_;
v___y_647_ = v___y_660_;
v___y_648_ = v___y_662_;
v___y_649_ = v___y_661_;
v_i_650_ = v_index_671_;
goto v___jp_645_;
}
else
{
lean_object* v___x_672_; 
lean_dec_ref(v_e_606_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___y_662_);
lean_ctor_set(v___x_672_, 1, v___y_660_);
v___y_639_ = v___y_659_;
v___y_640_ = v___y_661_;
v_snd_641_ = v___x_672_;
goto v___jp_638_;
}
}
}
}
v___jp_673_:
{
lean_object* v_size_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_size_679_ = lean_ctor_get(v___y_674_, 0);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_size_679_, v___x_680_);
v___x_682_ = lean_box_uint64(v___y_677_);
v___x_683_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_674_, v___x_681_, v_i_678_, v_e_606_, v___x_682_);
lean_dec(v_i_678_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___y_676_);
v___y_639_ = v___y_675_;
v___y_640_ = v___y_677_;
v_snd_641_ = v___x_684_;
goto v___jp_638_;
}
v___jp_685_:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___y_690_);
lean_dec_ref(v___y_690_);
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v___x_691_, v_e_606_);
switch(lean_obj_tag(v___x_692_))
{
case 0:
{
lean_object* v_index_693_; lean_object* v_size_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v___y_686_);
v_index_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_index_693_);
lean_dec_ref_known(v___x_692_, 3);
v_size_694_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_size_694_);
v___x_695_ = lean_box_uint64(v___y_689_);
v___x_696_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_691_, v_size_694_, v_index_693_, v_e_606_, v___x_695_);
lean_dec(v_index_693_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___y_688_);
v___y_639_ = v___y_687_;
v___y_640_ = v___y_689_;
v_snd_641_ = v___x_697_;
goto v___jp_638_;
}
case 1:
{
lean_object* v_index_698_; 
lean_dec(v___y_686_);
v_index_698_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_index_698_);
lean_dec_ref_known(v___x_692_, 1);
v___y_674_ = v___x_691_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_689_;
v_i_678_ = v_index_698_;
goto v___jp_673_;
}
default: 
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_691_, v___y_686_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_index_700_; 
v_index_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_index_700_);
lean_dec_ref_known(v___x_699_, 1);
v___y_674_ = v___x_691_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_689_;
v_i_678_ = v_index_700_;
goto v___jp_673_;
}
else
{
lean_object* v___x_701_; 
lean_dec_ref(v_e_606_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_691_);
lean_ctor_set(v___x_701_, 1, v___y_688_);
v___y_639_ = v___y_687_;
v___y_640_ = v___y_689_;
v_snd_641_ = v___x_701_;
goto v___jp_638_;
}
}
}
}
v___jp_702_:
{
lean_object* v___x_705_; lean_object* v_cache_706_; lean_object* v_keyToExprs_707_; lean_object* v_size_708_; lean_object* v_keyArray_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_705_ = lean_st_ref_take(v___y_704_);
v_cache_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_ref(v_cache_706_);
v_keyToExprs_707_ = lean_ctor_get(v___x_705_, 1);
lean_inc_ref(v_keyToExprs_707_);
v_size_708_ = lean_ctor_get(v_cache_706_, 0);
v_keyArray_709_ = lean_ctor_get(v_cache_706_, 1);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_array_get_size(v_keyArray_709_);
v___x_712_ = lean_nat_dec_lt(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v_keyToExprs_707_);
lean_dec_ref(v_cache_706_);
lean_dec_ref(v_e_606_);
v___y_639_ = v___y_704_;
v___y_640_ = v_key_703_;
v_snd_641_ = v___x_705_;
goto v___jp_638_;
}
else
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_747_; 
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; lean_object* v_unused_749_; 
v_unused_748_ = lean_ctor_get(v___x_705_, 1);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v___x_705_, 0);
lean_dec(v_unused_749_);
v___x_714_ = v___x_705_;
v_isShared_715_ = v_isSharedCheck_747_;
goto v_resetjp_713_;
}
else
{
lean_dec(v___x_705_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_747_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_cache_706_, v_e_606_);
switch(lean_obj_tag(v___x_716_))
{
case 0:
{
lean_object* v_index_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
lean_inc(v_size_708_);
v_index_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_index_717_);
lean_dec_ref_known(v___x_716_, 3);
v___x_718_ = lean_box_uint64(v_key_703_);
v___x_719_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_706_, v_size_708_, v_index_717_, v_e_606_, v___x_718_);
lean_dec(v_index_717_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_719_);
v___x_721_ = v___x_714_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_keyToExprs_707_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v___y_639_ = v___y_704_;
v___y_640_ = v_key_703_;
v_snd_641_ = v___x_721_;
goto v___jp_638_;
}
}
case 1:
{
lean_object* v_index_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_index_723_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_index_723_);
lean_dec_ref_known(v___x_716_, 1);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_size_708_, v___x_724_);
v___x_726_ = lean_nat_dec_lt(v___x_725_, v___x_711_);
if (v___x_726_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_index_723_);
lean_del_object(v___x_714_);
v___y_686_ = v___x_710_;
v___y_687_ = v___y_704_;
v___y_688_ = v_keyToExprs_707_;
v___y_689_ = v_key_703_;
v___y_690_ = v_cache_706_;
goto v___jp_685_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_727_ = lean_unsigned_to_nat(4u);
v___x_728_ = lean_nat_mul(v___x_725_, v___x_727_);
v___x_729_ = lean_unsigned_to_nat(3u);
v___x_730_ = lean_nat_mul(v___x_711_, v___x_729_);
v___x_731_ = lean_nat_dec_le(v___x_728_, v___x_730_);
lean_dec(v___x_730_);
lean_dec(v___x_728_);
if (v___x_731_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_index_723_);
lean_del_object(v___x_714_);
v___y_686_ = v___x_710_;
v___y_687_ = v___y_704_;
v___y_688_ = v_keyToExprs_707_;
v___y_689_ = v_key_703_;
v___y_690_ = v_cache_706_;
goto v___jp_685_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_732_ = lean_box_uint64(v_key_703_);
v___x_733_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_706_, v___x_725_, v_index_723_, v_e_606_, v___x_732_);
lean_dec(v_index_723_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_733_);
v___x_735_ = v___x_714_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_keyToExprs_707_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v___y_639_ = v___y_704_;
v___y_640_ = v_key_703_;
v_snd_641_ = v___x_735_;
goto v___jp_638_;
}
}
}
}
default: 
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
lean_del_object(v___x_714_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_size_708_, v___x_737_);
v___x_739_ = lean_nat_dec_lt(v___x_738_, v___x_711_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v___x_738_);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_cache_706_);
lean_dec_ref(v_cache_706_);
v___y_658_ = v___x_710_;
v___y_659_ = v___y_704_;
v___y_660_ = v_keyToExprs_707_;
v___y_661_ = v_key_703_;
v___y_662_ = v___x_740_;
goto v___jp_657_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_741_ = lean_unsigned_to_nat(4u);
v___x_742_ = lean_nat_mul(v___x_738_, v___x_741_);
lean_dec(v___x_738_);
v___x_743_ = lean_unsigned_to_nat(3u);
v___x_744_ = lean_nat_mul(v___x_711_, v___x_743_);
v___x_745_ = lean_nat_dec_le(v___x_742_, v___x_744_);
lean_dec(v___x_744_);
lean_dec(v___x_742_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_cache_706_);
lean_dec_ref(v_cache_706_);
v___y_658_ = v___x_710_;
v___y_659_ = v___y_704_;
v___y_660_ = v_keyToExprs_707_;
v___y_661_ = v_key_703_;
v___y_662_ = v___x_746_;
goto v___jp_657_;
}
else
{
v___y_658_ = v___x_710_;
v___y_659_ = v___y_704_;
v___y_660_ = v_keyToExprs_707_;
v___y_661_ = v_key_703_;
v___y_662_ = v_cache_706_;
goto v___jp_657_;
}
}
}
}
}
}
}
v___jp_750_:
{
lean_object* v___x_759_; 
v___x_759_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___y_751_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint64_t v___x_763_; lean_object* v___x_764_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = l_Lean_Expr_getAppNumArgs(v_e_606_);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_unbox_uint64(v_a_760_);
lean_dec(v_a_760_);
v___x_764_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v___x_761_, v_e_606_, v___x_761_, v_info_752_, v___x_762_, v___x_763_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec_ref(v_info_752_);
lean_dec_ref(v_e_606_);
lean_dec(v___x_761_);
return v___x_764_;
}
else
{
lean_dec_ref(v_info_752_);
lean_dec_ref(v_e_606_);
return v___x_759_;
}
}
v___jp_765_:
{
uint8_t v___x_773_; 
v___x_773_ = l_Lean_Expr_hasLooseBVars(v___y_766_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_box(0);
lean_inc_ref(v___y_766_);
v___x_775_ = l_Lean_Meta_getFunInfo(v___y_766_, v___x_774_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___y_751_ = v___y_766_;
v_info_752_ = v_a_776_;
v___y_753_ = v___y_767_;
v___y_754_ = v___y_768_;
v___y_755_ = v___y_769_;
v___y_756_ = v___y_770_;
v___y_757_ = v___y_771_;
v___y_758_ = v___y_772_;
goto v___jp_750_;
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___y_766_);
lean_dec_ref(v_e_606_);
v_a_777_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_775_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v___x_785_; 
v___x_785_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1));
v___y_751_ = v___y_766_;
v_info_752_ = v___x_785_;
v___y_753_ = v___y_767_;
v___y_754_ = v___y_768_;
v___y_755_ = v___y_769_;
v___y_756_ = v___y_770_;
v___y_757_ = v___y_771_;
v___y_758_ = v___y_772_;
goto v___jp_750_;
}
}
v___jp_787_:
{
switch(lean_obj_tag(v_e_606_))
{
case 2:
{
lean_object* v___x_788_; 
lean_inc_ref(v_e_606_);
v___x_788_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v_e_606_, v_a_610_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_802_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_802_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_802_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_802_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
uint8_t v___x_793_; 
v___x_793_ = lean_expr_eqv(v_a_789_, v_e_606_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_del_object(v___x_791_);
v___x_794_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_a_789_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; uint64_t v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v___x_796_ = lean_unbox_uint64(v_a_795_);
lean_dec(v_a_795_);
v_key_703_ = v___x_796_;
v___y_704_ = v_a_608_;
goto v___jp_702_;
}
else
{
lean_dec_ref_known(v_e_606_, 1);
return v___x_794_;
}
}
else
{
uint64_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_a_789_);
v___x_797_ = l_Lean_Expr_hash(v_e_606_);
lean_dec_ref_known(v_e_606_, 1);
v___x_798_ = lean_box_uint64(v___x_797_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_798_);
v___x_800_ = v___x_791_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref_known(v_e_606_, 1);
v_a_803_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_788_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_788_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
case 4:
{
lean_object* v_declName_811_; 
v_declName_811_ = lean_ctor_get(v_e_606_, 0);
lean_inc(v_declName_811_);
lean_dec_ref_known(v_e_606_, 2);
if (lean_obj_tag(v_declName_811_) == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1));
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
else
{
uint64_t v_hash_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_hash_814_ = lean_ctor_get_uint64(v_declName_811_, sizeof(void*)*2);
lean_dec(v_declName_811_);
v___x_815_ = lean_box_uint64(v_hash_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
case 5:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = l_Lean_Expr_getAppFn(v_e_606_);
v___x_818_ = l_Lean_Expr_isMVar(v___x_817_);
if (v___x_818_ == 0)
{
v___y_766_ = v___x_817_;
v___y_767_ = v_a_607_;
v___y_768_ = v_a_608_;
v___y_769_ = v_a_609_;
v___y_770_ = v_a_610_;
v___y_771_ = v_a_611_;
v___y_772_ = v_a_612_;
goto v___jp_765_;
}
else
{
lean_object* v___x_819_; 
lean_inc_ref(v_e_606_);
v___x_819_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v_e_606_, v_a_610_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; uint8_t v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = lean_expr_eqv(v_a_820_, v_e_606_);
if (v___x_821_ == 0)
{
lean_dec_ref_known(v_e_606_, 2);
lean_dec_ref(v___x_817_);
v_e_606_ = v_a_820_;
goto _start;
}
else
{
lean_dec(v_a_820_);
v___y_766_ = v___x_817_;
v___y_767_ = v_a_607_;
v___y_768_ = v_a_608_;
v___y_769_ = v_a_609_;
v___y_770_ = v_a_610_;
v___y_771_ = v_a_611_;
v___y_772_ = v_a_612_;
goto v___jp_765_;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref_known(v_e_606_, 2);
lean_dec_ref(v___x_817_);
v_a_823_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_819_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_831_; lean_object* v_body_832_; 
v_binderType_831_ = lean_ctor_get(v_e_606_, 1);
lean_inc_ref(v_binderType_831_);
v_body_832_ = lean_ctor_get(v_e_606_, 2);
lean_inc_ref(v_body_832_);
lean_dec_ref_known(v_e_606_, 3);
v_t_615_ = v_binderType_831_;
v_b_616_ = v_body_832_;
v___y_617_ = v_a_607_;
v___y_618_ = v_a_608_;
v___y_619_ = v_a_609_;
v___y_620_ = v_a_610_;
v___y_621_ = v_a_611_;
v___y_622_ = v_a_612_;
goto v___jp_614_;
}
case 7:
{
lean_object* v_binderType_833_; lean_object* v_body_834_; 
v_binderType_833_ = lean_ctor_get(v_e_606_, 1);
lean_inc_ref(v_binderType_833_);
v_body_834_ = lean_ctor_get(v_e_606_, 2);
lean_inc_ref(v_body_834_);
lean_dec_ref_known(v_e_606_, 3);
v_t_615_ = v_binderType_833_;
v_b_616_ = v_body_834_;
v___y_617_ = v_a_607_;
v___y_618_ = v_a_608_;
v___y_619_ = v_a_609_;
v___y_620_ = v_a_610_;
v___y_621_ = v_a_611_;
v___y_622_ = v_a_612_;
goto v___jp_614_;
}
case 8:
{
lean_object* v_value_835_; lean_object* v_body_836_; lean_object* v___x_837_; 
v_value_835_ = lean_ctor_get(v_e_606_, 2);
lean_inc_ref(v_value_835_);
v_body_836_ = lean_ctor_get(v_e_606_, 3);
lean_inc_ref(v_body_836_);
lean_dec_ref_known(v_e_606_, 4);
v___x_837_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_835_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_836_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_851_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_851_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_844_ = lean_unbox_uint64(v_a_838_);
lean_dec(v_a_838_);
v___x_845_ = lean_unbox_uint64(v_a_840_);
lean_dec(v_a_840_);
v___x_846_ = lean_uint64_mix_hash(v___x_844_, v___x_845_);
v___x_847_ = lean_box_uint64(v___x_846_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_847_);
v___x_849_ = v___x_842_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_dec(v_a_838_);
return v___x_839_;
}
}
else
{
lean_dec_ref(v_body_836_);
return v___x_837_;
}
}
case 10:
{
lean_object* v_expr_852_; lean_object* v___x_853_; 
v_expr_852_ = lean_ctor_get(v_e_606_, 1);
lean_inc_ref(v_expr_852_);
v___x_853_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_852_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; uint64_t v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = lean_unbox_uint64(v_a_854_);
lean_dec(v_a_854_);
v_key_703_ = v___x_855_;
v___y_704_ = v_a_608_;
goto v___jp_702_;
}
else
{
lean_dec_ref_known(v_e_606_, 2);
return v___x_853_;
}
}
case 11:
{
lean_object* v_idx_856_; lean_object* v_struct_857_; lean_object* v___x_858_; 
v_idx_856_ = lean_ctor_get(v_e_606_, 1);
lean_inc(v_idx_856_);
v_struct_857_ = lean_ctor_get(v_e_606_, 2);
lean_inc_ref(v_struct_857_);
lean_dec_ref_known(v_e_606_, 3);
v___x_858_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_857_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_870_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_870_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_870_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_870_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
uint64_t v___x_863_; uint64_t v___x_864_; uint64_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_863_ = lean_uint64_of_nat(v_idx_856_);
lean_dec(v_idx_856_);
v___x_864_ = lean_unbox_uint64(v_a_859_);
lean_dec(v_a_859_);
v___x_865_ = lean_uint64_mix_hash(v___x_863_, v___x_864_);
v___x_866_ = lean_box_uint64(v___x_865_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_866_);
v___x_868_ = v___x_861_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_dec(v_idx_856_);
return v___x_858_;
}
}
default: 
{
uint64_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_Expr_hash(v_e_606_);
lean_dec_ref(v_e_606_);
v___x_872_ = lean_box_uint64(v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(lean_object* v___x_888_, lean_object* v_e_889_, lean_object* v_upperBound_890_, lean_object* v_info_891_, lean_object* v_a_892_, uint64_t v_b_893_, uint8_t v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint64_t v_a_902_; uint8_t v___y_907_; uint8_t v___x_916_; 
v___x_916_ = lean_nat_dec_lt(v_a_892_, v_upperBound_890_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v_a_892_);
v___x_917_ = lean_box_uint64(v_b_893_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
else
{
lean_object* v_paramInfo_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_paramInfo_919_ = lean_ctor_get(v_info_891_, 0);
v___x_920_ = lean_array_get_size(v_paramInfo_919_);
v___x_921_ = lean_nat_dec_lt(v_a_892_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_922_ = lean_nat_sub(v___x_888_, v_a_892_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_sub(v___x_922_, v___x_923_);
lean_dec(v___x_922_);
v___x_925_ = l_Lean_Expr_getRevArg_x21(v_e_889_, v___x_924_);
v___x_926_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_925_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; uint64_t v___x_928_; uint64_t v___x_929_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = lean_unbox_uint64(v_a_927_);
lean_dec(v_a_927_);
v___x_929_ = lean_uint64_mix_hash(v_b_893_, v___x_928_);
v_a_902_ = v___x_929_;
goto v___jp_901_;
}
else
{
lean_dec(v_a_892_);
return v___x_926_;
}
}
else
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_array_fget_borrowed(v_paramInfo_919_, v_a_892_);
v___x_931_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_930_);
if (v___x_931_ == 0)
{
v___y_907_ = v___x_931_;
goto v___jp_906_;
}
else
{
uint8_t v_isProp_932_; 
v_isProp_932_ = lean_ctor_get_uint8(v___x_930_, sizeof(void*)*1 + 2);
if (v_isProp_932_ == 0)
{
v___y_907_ = v___x_931_;
goto v___jp_906_;
}
else
{
v_a_902_ = v_b_893_;
goto v___jp_901_;
}
}
}
}
v___jp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_a_892_, v___x_903_);
lean_dec(v_a_892_);
v_a_892_ = v___x_904_;
v_b_893_ = v_a_902_;
goto _start;
}
v___jp_906_:
{
if (v___y_907_ == 0)
{
v_a_902_ = v_b_893_;
goto v___jp_901_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_908_ = lean_nat_sub(v___x_888_, v_a_892_);
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_nat_sub(v___x_908_, v___x_909_);
lean_dec(v___x_908_);
v___x_911_ = l_Lean_Expr_getRevArg_x21(v_e_889_, v___x_910_);
v___x_912_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_911_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint64_t v___x_914_; uint64_t v___x_915_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_unbox_uint64(v_a_913_);
lean_dec(v_a_913_);
v___x_915_ = lean_uint64_mix_hash(v_b_893_, v___x_914_);
v_a_902_ = v___x_915_;
goto v___jp_901_;
}
else
{
lean_dec(v_a_892_);
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg___boxed(lean_object* v___x_933_, lean_object* v_e_934_, lean_object* v_upperBound_935_, lean_object* v_info_936_, lean_object* v_a_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint64_t v_b_boxed_946_; uint8_t v___y_14328__boxed_947_; lean_object* v_res_948_; 
v_b_boxed_946_ = lean_unbox_uint64(v_b_938_);
lean_dec_ref(v_b_938_);
v___y_14328__boxed_947_ = lean_unbox(v___y_939_);
v_res_948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v___x_933_, v_e_934_, v_upperBound_935_, v_info_936_, v_a_937_, v_b_boxed_946_, v___y_14328__boxed_947_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v_info_936_);
lean_dec(v_upperBound_935_);
lean_dec_ref(v_e_934_);
lean_dec(v___x_933_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* v_e_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint8_t v_a_boxed_957_; lean_object* v_res_958_; 
v_a_boxed_957_ = lean_unbox(v_a_950_);
v_res_958_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_949_, v_a_boxed_957_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* v_00_u03b2_959_, lean_object* v_m_960_, lean_object* v_query_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_m_960_, v_query_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object* v_00_u03b2_963_, lean_object* v_m_964_, lean_object* v_query_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(v_00_u03b2_963_, v_m_964_, v_query_965_);
lean_dec_ref(v_query_965_);
lean_dec_ref(v_m_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object* v_00_u03b2_967_, lean_object* v_m_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_m_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object* v_00_u03b2_970_, lean_object* v_m_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v_00_u03b2_970_, v_m_971_);
lean_dec_ref(v_m_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(lean_object* v___x_973_, lean_object* v_e_974_, lean_object* v_upperBound_975_, lean_object* v_info_976_, lean_object* v_inst_977_, lean_object* v_R_978_, lean_object* v_a_979_, uint64_t v_b_980_, lean_object* v_c_981_, uint8_t v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v___x_973_, v_e_974_, v_upperBound_975_, v_info_976_, v_a_979_, v_b_980_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___boxed(lean_object* v___x_990_, lean_object* v_e_991_, lean_object* v_upperBound_992_, lean_object* v_info_993_, lean_object* v_inst_994_, lean_object* v_R_995_, lean_object* v_a_996_, lean_object* v_b_997_, lean_object* v_c_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint64_t v_b_boxed_1006_; uint8_t v___y_14980__boxed_1007_; lean_object* v_res_1008_; 
v_b_boxed_1006_ = lean_unbox_uint64(v_b_997_);
lean_dec_ref(v_b_997_);
v___y_14980__boxed_1007_ = lean_unbox(v___y_999_);
v_res_1008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(v___x_990_, v_e_991_, v_upperBound_992_, v_info_993_, v_inst_994_, v_R_995_, v_a_996_, v_b_boxed_1006_, v_c_998_, v___y_14980__boxed_1007_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_info_993_);
lean_dec(v_upperBound_992_);
lean_dec_ref(v_e_991_);
lean_dec(v___x_990_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4(lean_object* v_00_u03b2_1009_, lean_object* v_m_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___redArg(v_m_1010_, v_a_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4___boxed(lean_object* v_00_u03b2_1013_, lean_object* v_m_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4(v_00_u03b2_1013_, v_m_1014_, v_a_1015_);
lean_dec_ref(v_a_1015_);
lean_dec_ref(v_m_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(lean_object* v_00_u03b2_1017_, lean_object* v_m_1018_, lean_object* v_query_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_m_1018_, v_query_1019_, v_x_1020_, v_x_1021_, v_x_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_m_1026_, lean_object* v_query_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(v_00_u03b2_1025_, v_m_1026_, v_query_1027_, v_x_1028_, v_x_1029_, v_x_1030_, v_x_1031_);
lean_dec_ref(v_query_1027_);
lean_dec_ref(v_m_1026_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2(lean_object* v_00_u03b2_1033_, lean_object* v_init_1034_, lean_object* v_b_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___redArg(v_init_1034_, v_b_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1037_, lean_object* v_init_1038_, lean_object* v_b_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2(v_00_u03b2_1037_, v_init_1038_, v_b_1039_);
lean_dec_ref(v_b_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6(lean_object* v_00_u03b2_1041_, lean_object* v_m_1042_, lean_object* v_query_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___redArg(v_m_1042_, v_query_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1045_, lean_object* v_m_1046_, lean_object* v_query_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__4_spec__6(v_00_u03b2_1045_, v_m_1046_, v_query_1047_);
lean_dec_ref(v_query_1047_);
lean_dec_ref(v_m_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1049_, lean_object* v_b_1050_, lean_object* v_acc_1051_, lean_object* v_i_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___redArg(v_b_1050_, v_acc_1051_, v_i_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1054_, lean_object* v_b_1055_, lean_object* v_acc_1056_, lean_object* v_i_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_spec__2_spec__4(v_00_u03b2_1054_, v_b_1055_, v_acc_1056_, v_i_1057_);
lean_dec_ref(v_b_1055_);
return v_res_1058_;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___f_1061_; 
v___x_1060_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_1061_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1061_, 0, v___x_1060_);
return v___f_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t v_k_1062_, lean_object* v_____do__lift_1063_){
_start:
{
lean_object* v_keyToExprs_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_keyToExprs_1064_ = lean_ctor_get(v_____do__lift_1063_, 1);
v___f_1065_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0));
v___f_1066_ = lean_obj_once(&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1, &l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1_once, _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1);
v___x_1067_ = lean_box_uint64(v_k_1062_);
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_1066_, v___f_1065_, v_keyToExprs_1064_, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* v_k_1069_, lean_object* v_____do__lift_1070_){
_start:
{
uint64_t v_k_boxed_1071_; lean_object* v_res_1072_; 
v_k_boxed_1071_ = lean_unbox_uint64(v_k_1069_);
lean_dec_ref(v_k_1069_);
v_res_1072_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v_k_boxed_1071_, v_____do__lift_1070_);
lean_dec_ref(v_____do__lift_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(lean_object* v_m_1073_, uint64_t v_query_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v_zero_1078_; uint8_t v_isZero_1079_; 
v_zero_1078_ = lean_unsigned_to_nat(0u);
v_isZero_1079_ = lean_nat_dec_eq(v_x_1076_, v_zero_1078_);
if (v_isZero_1079_ == 1)
{
lean_dec(v_x_1077_);
lean_dec(v_x_1076_);
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_box(2);
return v___x_1080_;
}
else
{
lean_object* v_val_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_val_1081_ = lean_ctor_get(v_x_1075_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v_x_1075_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_val_1081_);
lean_dec(v_x_1075_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_val_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_keyArray_1089_; lean_object* v_valueArray_1090_; lean_object* v___x_1091_; uint8_t v_isSome_1092_; 
v_keyArray_1089_ = lean_ctor_get(v_m_1073_, 1);
v_valueArray_1090_ = lean_ctor_get(v_m_1073_, 2);
v___x_1091_ = lean_array_fget_borrowed(v_keyArray_1089_, v_x_1077_);
v_isSome_1092_ = lean_noption_is_some(v___x_1091_);
if (v_isSome_1092_ == 0)
{
lean_dec(v_x_1076_);
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_x_1077_);
return v___x_1093_;
}
else
{
lean_object* v_val_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_x_1077_);
v_val_1094_ = lean_ctor_get(v_x_1075_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v_x_1075_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_val_1094_);
lean_dec(v_x_1075_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_val_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_one_1102_; lean_object* v_n_1103_; lean_object* v___y_1105_; 
v_one_1102_ = lean_unsigned_to_nat(1u);
v_n_1103_ = lean_nat_sub(v_x_1076_, v_one_1102_);
lean_dec(v_x_1076_);
if (v_isSome_1092_ == 0)
{
goto v___jp_1111_;
}
else
{
lean_object* v___x_1113_; uint8_t v_isSome_1114_; 
v___x_1113_ = lean_array_fget_borrowed(v_valueArray_1090_, v_x_1077_);
v_isSome_1114_ = lean_noption_is_some(v___x_1113_);
if (v_isSome_1114_ == 0)
{
goto v___jp_1111_;
}
else
{
lean_object* v_val_1115_; uint64_t v___x_1116_; uint8_t v___x_1117_; 
lean_inc(v___x_1091_);
v_val_1115_ = lean_noption_get(v___x_1091_);
v___x_1116_ = lean_unbox_uint64(v_val_1115_);
v___x_1117_ = lean_uint64_dec_eq(v___x_1116_, v_query_1074_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
lean_dec(v_val_1115_);
v___x_1118_ = lean_array_get_size(v_keyArray_1089_);
v___x_1119_ = lean_nat_add(v_x_1077_, v_one_1102_);
lean_dec(v_x_1077_);
v___x_1120_ = lean_nat_dec_lt(v___x_1119_, v___x_1118_);
if (v___x_1120_ == 0)
{
lean_dec(v___x_1119_);
v_x_1076_ = v_n_1103_;
v_x_1077_ = v_zero_1078_;
goto _start;
}
else
{
v_x_1076_ = v_n_1103_;
v_x_1077_ = v___x_1119_;
goto _start;
}
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1124_; 
lean_dec(v_n_1103_);
lean_dec(v_x_1075_);
lean_inc(v___x_1113_);
v_val_1123_ = lean_noption_get(v___x_1113_);
v___x_1124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1124_, 0, v_x_1077_);
lean_ctor_set(v___x_1124_, 1, v_val_1115_);
lean_ctor_set(v___x_1124_, 2, v_val_1123_);
return v___x_1124_;
}
}
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_array_get_size(v_keyArray_1089_);
v___x_1107_ = lean_nat_add(v_x_1077_, v_one_1102_);
lean_dec(v_x_1077_);
v___x_1108_ = lean_nat_dec_lt(v___x_1107_, v___x_1106_);
if (v___x_1108_ == 0)
{
lean_dec(v___x_1107_);
v_x_1075_ = v___y_1105_;
v_x_1076_ = v_n_1103_;
v_x_1077_ = v_zero_1078_;
goto _start;
}
else
{
v_x_1075_ = v___y_1105_;
v_x_1076_ = v_n_1103_;
v_x_1077_ = v___x_1107_;
goto _start;
}
}
v___jp_1111_:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v___x_1112_; 
lean_inc(v_x_1077_);
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_x_1077_);
v___y_1105_ = v___x_1112_;
goto v___jp_1104_;
}
else
{
v___y_1105_ = v_x_1075_;
goto v___jp_1104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg___boxed(lean_object* v_m_1125_, lean_object* v_query_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
uint64_t v_query_boxed_1130_; lean_object* v_res_1131_; 
v_query_boxed_1130_ = lean_unbox_uint64(v_query_1126_);
lean_dec_ref(v_query_1126_);
v_res_1131_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_m_1125_, v_query_boxed_1130_, v_x_1127_, v_x_1128_, v_x_1129_);
lean_dec_ref(v_m_1125_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(lean_object* v_m_1132_, uint64_t v_query_1133_){
_start:
{
lean_object* v_keyArray_1134_; lean_object* v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; uint64_t v_fold_1138_; uint64_t v___x_1139_; uint64_t v___x_1140_; uint64_t v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_keyArray_1134_ = lean_ctor_get(v_m_1132_, 1);
v___x_1135_ = lean_array_get_size(v_keyArray_1134_);
v___x_1136_ = 32ULL;
v___x_1137_ = lean_uint64_shift_right(v_query_1133_, v___x_1136_);
v_fold_1138_ = lean_uint64_xor(v_query_1133_, v___x_1137_);
v___x_1139_ = 16ULL;
v___x_1140_ = lean_uint64_shift_right(v_fold_1138_, v___x_1139_);
v___x_1141_ = lean_uint64_xor(v_fold_1138_, v___x_1140_);
v___x_1142_ = lean_uint64_to_usize(v___x_1141_);
v___x_1143_ = lean_usize_of_nat(v___x_1135_);
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_sub(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_usize_land(v___x_1142_, v___x_1145_);
v___x_1147_ = lean_usize_to_nat(v___x_1146_);
v___x_1148_ = lean_box(0);
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_m_1132_, v_query_1133_, v___x_1148_, v___x_1135_, v___x_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg___boxed(lean_object* v_m_1150_, lean_object* v_query_1151_){
_start:
{
uint64_t v_query_boxed_1152_; lean_object* v_res_1153_; 
v_query_boxed_1152_ = lean_unbox_uint64(v_query_1151_);
lean_dec_ref(v_query_1151_);
v_res_1153_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1150_, v_query_boxed_1152_);
lean_dec_ref(v_m_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(lean_object* v_m_1154_, uint64_t v_query_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1154_, v_query_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_index_1157_; lean_object* v_key_1158_; lean_object* v_value_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_index_1157_ = lean_ctor_get(v___x_1156_, 0);
v_key_1158_ = lean_ctor_get(v___x_1156_, 1);
v_value_1159_ = lean_ctor_get(v___x_1156_, 2);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1156_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_value_1159_);
lean_inc(v_key_1158_);
lean_inc(v_index_1157_);
lean_dec(v___x_1156_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_index_1157_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_key_1158_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_value_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v___x_1167_; 
lean_dec(v___x_1156_);
v___x_1167_ = lean_box(1);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg___boxed(lean_object* v_m_1168_, lean_object* v_query_1169_){
_start:
{
uint64_t v_query_boxed_1170_; lean_object* v_res_1171_; 
v_query_boxed_1170_ = lean_unbox_uint64(v_query_1169_);
lean_dec_ref(v_query_1169_);
v_res_1171_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_m_1168_, v_query_boxed_1170_);
lean_dec_ref(v_m_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object* v_m_1172_, uint64_t v_a_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_m_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_value_1175_; lean_object* v___x_1176_; 
v_value_1175_ = lean_ctor_get(v___x_1174_, 2);
lean_inc(v_value_1175_);
lean_dec_ref_known(v___x_1174_, 3);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_value_1175_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* v_m_1178_, lean_object* v_a_1179_){
_start:
{
uint64_t v_a_boxed_1180_; lean_object* v_res_1181_; 
v_a_boxed_1180_ = lean_unbox_uint64(v_a_1179_);
lean_dec_ref(v_a_1179_);
v_res_1181_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_1178_, v_a_boxed_1180_);
lean_dec_ref(v_m_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___redArg(lean_object* v_b_1182_, lean_object* v_acc_1183_, lean_object* v_i_1184_){
_start:
{
lean_object* v___y_1186_; lean_object* v_keyArray_1194_; lean_object* v_valueArray_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_keyArray_1194_ = lean_ctor_get(v_b_1182_, 1);
v_valueArray_1195_ = lean_ctor_get(v_b_1182_, 2);
v___x_1196_ = lean_array_get_size(v_keyArray_1194_);
v___x_1197_ = lean_nat_dec_lt(v_i_1184_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_dec(v_i_1184_);
return v_acc_1183_;
}
else
{
lean_object* v___x_1198_; uint8_t v_isSome_1199_; 
v___x_1198_ = lean_array_fget_borrowed(v_keyArray_1194_, v_i_1184_);
v_isSome_1199_ = lean_noption_is_some(v___x_1198_);
if (v_isSome_1199_ == 0)
{
goto v___jp_1190_;
}
else
{
lean_object* v___x_1200_; uint8_t v_isSome_1201_; 
v___x_1200_ = lean_array_fget_borrowed(v_valueArray_1195_, v_i_1184_);
v_isSome_1201_ = lean_noption_is_some(v___x_1200_);
if (v_isSome_1201_ == 0)
{
goto v___jp_1190_;
}
else
{
lean_object* v_val_1202_; lean_object* v_val_1203_; lean_object* v_i_1205_; uint64_t v___x_1210_; lean_object* v___x_1211_; 
lean_inc(v___x_1198_);
v_val_1202_ = lean_noption_get(v___x_1198_);
lean_inc(v___x_1200_);
v_val_1203_ = lean_noption_get(v___x_1200_);
v___x_1210_ = lean_unbox_uint64(v_val_1202_);
v___x_1211_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_acc_1183_, v___x_1210_);
switch(lean_obj_tag(v___x_1211_))
{
case 0:
{
lean_object* v_index_1212_; lean_object* v_size_1213_; lean_object* v___x_1214_; 
v_index_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_index_1212_);
lean_dec_ref_known(v___x_1211_, 3);
v_size_1213_ = lean_ctor_get(v_acc_1183_, 0);
lean_inc(v_size_1213_);
v___x_1214_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1183_, v_size_1213_, v_index_1212_, v_val_1202_, v_val_1203_);
lean_dec(v_index_1212_);
v___y_1186_ = v___x_1214_;
goto v___jp_1185_;
}
case 1:
{
lean_object* v_index_1215_; 
v_index_1215_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_index_1215_);
lean_dec_ref_known(v___x_1211_, 1);
v_i_1205_ = v_index_1215_;
goto v___jp_1204_;
}
default: 
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1183_, v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_index_1218_; 
v_index_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_index_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v_i_1205_ = v_index_1218_;
goto v___jp_1204_;
}
else
{
lean_dec(v_val_1203_);
lean_dec(v_val_1202_);
v___y_1186_ = v_acc_1183_;
goto v___jp_1185_;
}
}
}
v___jp_1204_:
{
lean_object* v_size_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_size_1206_ = lean_ctor_get(v_acc_1183_, 0);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_size_1206_, v___x_1207_);
v___x_1209_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1183_, v___x_1208_, v_i_1205_, v_val_1202_, v_val_1203_);
lean_dec(v_i_1205_);
v___y_1186_ = v___x_1209_;
goto v___jp_1185_;
}
}
}
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_add(v_i_1184_, v___x_1187_);
lean_dec(v_i_1184_);
v_acc_1183_ = v___y_1186_;
v_i_1184_ = v___x_1188_;
goto _start;
}
v___jp_1190_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_i_1184_, v___x_1191_);
lean_dec(v_i_1184_);
v_i_1184_ = v___x_1192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_b_1219_, lean_object* v_acc_1220_, lean_object* v_i_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___redArg(v_b_1219_, v_acc_1220_, v_i_1221_);
lean_dec_ref(v_b_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___redArg(lean_object* v_init_1223_, lean_object* v_b_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___redArg(v_b_1224_, v_init_1223_, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___redArg___boxed(lean_object* v_init_1227_, lean_object* v_b_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___redArg(v_init_1227_, v_b_1228_);
lean_dec_ref(v_b_1228_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(lean_object* v_m_1230_){
_start:
{
lean_object* v_keyArray_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_cellCount_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_target_1238_; lean_object* v___x_1239_; 
v_keyArray_1231_ = lean_ctor_get(v_m_1230_, 1);
v___x_1232_ = lean_array_get_size(v_keyArray_1231_);
v___x_1233_ = lean_unsigned_to_nat(2u);
v_cellCount_1234_ = lean_nat_mul(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1234_);
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1234_);
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1234_);
v_target_1238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1238_, 0, v___x_1235_);
lean_ctor_set(v_target_1238_, 1, v___x_1236_);
lean_ctor_set(v_target_1238_, 2, v___x_1237_);
v___x_1239_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___redArg(v_target_1238_, v_m_1230_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg___boxed(lean_object* v_m_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_m_1240_);
lean_dec_ref(v_m_1240_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* v_e_1245_, lean_object* v_as_x27_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
if (lean_obj_tag(v_as_x27_1246_) == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v_e_1245_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_b_1247_);
return v___x_1253_;
}
else
{
lean_object* v_head_1254_; lean_object* v_tail_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v_b_1247_);
v_head_1254_ = lean_ctor_get(v_as_x27_1246_, 0);
v_tail_1255_ = lean_ctor_get(v_as_x27_1246_, 1);
lean_inc(v_head_1254_);
lean_inc_ref(v_e_1245_);
v___x_1256_ = l_Lean_Meta_isExprDefEq(v_e_1245_, v_head_1254_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1270_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1270_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1270_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_unbox(v_a_1257_);
lean_dec(v_a_1257_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_del_object(v___x_1259_);
v___x_1263_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
v_as_x27_1246_ = v_tail_1255_;
v_b_1247_ = v___x_1263_;
goto _start;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
lean_dec_ref(v_e_1245_);
lean_inc(v_head_1254_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_head_1254_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1261_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1266_);
v___x_1268_ = v___x_1259_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_e_1245_);
v_a_1271_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1256_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1256_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object* v_e_1279_, lean_object* v_as_x27_1280_, lean_object* v_b_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1279_, v_as_x27_1280_, v_b_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v_as_x27_1280_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* v_e_1288_, uint8_t v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1296_; 
lean_inc_ref(v_e_1288_);
v___x_1296_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1522_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1522_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1522_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v_keyToExprs_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1520_; 
v___x_1301_ = lean_st_ref_get(v_a_1290_);
v_keyToExprs_1302_ = lean_ctor_get(v___x_1301_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1521_);
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1520_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_keyToExprs_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1520_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
uint64_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_unbox_uint64(v_a_1297_);
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_keyToExprs_1302_, v___x_1306_);
lean_dec_ref(v_keyToExprs_1302_);
if (lean_obj_tag(v___x_1307_) == 1)
{
lean_object* v_val_1308_; lean_object* v_keyedConfig_1309_; uint8_t v_trackZetaDelta_1310_; lean_object* v_zetaDeltaSet_1311_; lean_object* v_lctx_1312_; lean_object* v_localInstances_1313_; lean_object* v_defEqCtx_x3f_1314_; lean_object* v_synthPendingDepth_1315_; lean_object* v_customCanUnfoldPredicate_x3f_1316_; uint8_t v_univApprox_1317_; uint8_t v_inTypeClassResolution_1318_; uint8_t v_cacheInferType_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1304_);
lean_del_object(v___x_1299_);
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v_keyedConfig_1309_ = lean_ctor_get(v_a_1291_, 0);
v_trackZetaDelta_1310_ = lean_ctor_get_uint8(v_a_1291_, sizeof(void*)*7);
v_zetaDeltaSet_1311_ = lean_ctor_get(v_a_1291_, 1);
v_lctx_1312_ = lean_ctor_get(v_a_1291_, 2);
v_localInstances_1313_ = lean_ctor_get(v_a_1291_, 3);
v_defEqCtx_x3f_1314_ = lean_ctor_get(v_a_1291_, 4);
v_synthPendingDepth_1315_ = lean_ctor_get(v_a_1291_, 5);
v_customCanUnfoldPredicate_x3f_1316_ = lean_ctor_get(v_a_1291_, 6);
v_univApprox_1317_ = lean_ctor_get_uint8(v_a_1291_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1318_ = lean_ctor_get_uint8(v_a_1291_, sizeof(void*)*7 + 2);
v_cacheInferType_1319_ = lean_ctor_get_uint8(v_a_1291_, sizeof(void*)*7 + 3);
v___x_1320_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
lean_inc_ref(v_keyedConfig_1309_);
v___x_1321_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_a_1289_, v_keyedConfig_1309_);
lean_inc(v_customCanUnfoldPredicate_x3f_1316_);
lean_inc(v_synthPendingDepth_1315_);
lean_inc(v_defEqCtx_x3f_1314_);
lean_inc_ref(v_localInstances_1313_);
lean_inc_ref(v_lctx_1312_);
lean_inc(v_zetaDeltaSet_1311_);
v___x_1322_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v_zetaDeltaSet_1311_);
lean_ctor_set(v___x_1322_, 2, v_lctx_1312_);
lean_ctor_set(v___x_1322_, 3, v_localInstances_1313_);
lean_ctor_set(v___x_1322_, 4, v_defEqCtx_x3f_1314_);
lean_ctor_set(v___x_1322_, 5, v_synthPendingDepth_1315_);
lean_ctor_set(v___x_1322_, 6, v_customCanUnfoldPredicate_x3f_1316_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*7, v_trackZetaDelta_1310_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*7 + 1, v_univApprox_1317_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1318_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*7 + 3, v_cacheInferType_1319_);
lean_inc_ref(v_e_1288_);
v___x_1323_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1288_, v_val_1308_, v___x_1320_, v___x_1322_, v_a_1292_, v_a_1293_, v_a_1294_);
lean_dec_ref_known(v___x_1322_, 7);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1424_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1424_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1424_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_fst_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1422_; 
v_fst_1328_ = lean_ctor_get(v_a_1324_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_a_1324_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v_a_1324_, 1);
lean_dec(v_unused_1423_);
v___x_1330_ = v_a_1324_;
v_isShared_1331_ = v_isSharedCheck_1422_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_fst_1328_);
lean_dec(v_a_1324_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1422_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
if (lean_obj_tag(v_fst_1328_) == 0)
{
lean_object* v___x_1332_; lean_object* v_cache_1333_; lean_object* v_keyToExprs_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1417_; 
v___x_1332_ = lean_st_ref_take(v_a_1290_);
v_cache_1333_ = lean_ctor_get(v___x_1332_, 0);
v_keyToExprs_1334_ = lean_ctor_get(v___x_1332_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1336_ = v___x_1332_;
v_isShared_1337_ = v_isSharedCheck_1417_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_keyToExprs_1334_);
lean_inc(v_cache_1333_);
lean_dec(v___x_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1417_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___y_1339_; lean_object* v___x_1348_; 
lean_inc_ref(v_e_1288_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 1);
lean_ctor_set(v___x_1330_, 1, v_val_1308_);
lean_ctor_set(v___x_1330_, 0, v_e_1288_);
v___x_1348_ = v___x_1330_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_e_1288_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_val_1308_);
v___x_1348_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1347_;
}
v___jp_1338_:
{
lean_object* v___x_1341_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___y_1339_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_cache_1333_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___y_1339_);
v___x_1341_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = lean_st_ref_put(v_a_1290_, v___x_1341_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_e_1288_);
v___x_1344_ = v___x_1326_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_e_1288_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
v_reusejp_1347_:
{
lean_object* v___y_1350_; lean_object* v_i_1351_; lean_object* v___y_1357_; lean_object* v___y_1368_; lean_object* v_i_1369_; uint64_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_unbox_uint64(v_a_1297_);
v___x_1386_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1334_, v___x_1385_);
switch(lean_obj_tag(v___x_1386_))
{
case 0:
{
lean_object* v_index_1387_; lean_object* v_size_1388_; lean_object* v___x_1389_; 
v_index_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_index_1387_);
lean_dec_ref_known(v___x_1386_, 3);
v_size_1388_ = lean_ctor_get(v_keyToExprs_1334_, 0);
lean_inc(v_size_1388_);
v___x_1389_ = l_Std_DHashMap_Raw_setEntry___redArg(v_keyToExprs_1334_, v_size_1388_, v_index_1387_, v_a_1297_, v___x_1348_);
lean_dec(v_index_1387_);
v___y_1339_ = v___x_1389_;
goto v___jp_1338_;
}
case 1:
{
lean_object* v_index_1390_; lean_object* v_size_1391_; lean_object* v_keyArray_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_index_1390_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_index_1390_);
lean_dec_ref_known(v___x_1386_, 1);
v_size_1391_ = lean_ctor_get(v_keyToExprs_1334_, 0);
v_keyArray_1392_ = lean_ctor_get(v_keyToExprs_1334_, 1);
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_add(v_size_1391_, v___x_1393_);
v___x_1395_ = lean_array_get_size(v_keyArray_1392_);
v___x_1396_ = lean_nat_dec_lt(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec(v___x_1394_);
lean_dec(v_index_1390_);
goto v___jp_1374_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1397_ = lean_unsigned_to_nat(4u);
v___x_1398_ = lean_nat_mul(v___x_1394_, v___x_1397_);
v___x_1399_ = lean_unsigned_to_nat(3u);
v___x_1400_ = lean_nat_mul(v___x_1395_, v___x_1399_);
v___x_1401_ = lean_nat_dec_le(v___x_1398_, v___x_1400_);
lean_dec(v___x_1400_);
lean_dec(v___x_1398_);
if (v___x_1401_ == 0)
{
lean_dec(v___x_1394_);
lean_dec(v_index_1390_);
goto v___jp_1374_;
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Std_DHashMap_Raw_setEntry___redArg(v_keyToExprs_1334_, v___x_1394_, v_index_1390_, v_a_1297_, v___x_1348_);
lean_dec(v_index_1390_);
v___y_1339_ = v___x_1402_;
goto v___jp_1338_;
}
}
}
default: 
{
lean_object* v_size_1403_; lean_object* v_keyArray_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_size_1403_ = lean_ctor_get(v_keyToExprs_1334_, 0);
v_keyArray_1404_ = lean_ctor_get(v_keyToExprs_1334_, 1);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_nat_add(v_size_1403_, v___x_1405_);
v___x_1407_ = lean_array_get_size(v_keyArray_1404_);
v___x_1408_ = lean_nat_dec_lt(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
lean_dec(v___x_1406_);
v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_keyToExprs_1334_);
lean_dec_ref(v_keyToExprs_1334_);
v___y_1357_ = v___x_1409_;
goto v___jp_1356_;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1410_ = lean_unsigned_to_nat(4u);
v___x_1411_ = lean_nat_mul(v___x_1406_, v___x_1410_);
lean_dec(v___x_1406_);
v___x_1412_ = lean_unsigned_to_nat(3u);
v___x_1413_ = lean_nat_mul(v___x_1407_, v___x_1412_);
v___x_1414_ = lean_nat_dec_le(v___x_1411_, v___x_1413_);
lean_dec(v___x_1413_);
lean_dec(v___x_1411_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_keyToExprs_1334_);
lean_dec_ref(v_keyToExprs_1334_);
v___y_1357_ = v___x_1415_;
goto v___jp_1356_;
}
else
{
v___y_1357_ = v_keyToExprs_1334_;
goto v___jp_1356_;
}
}
}
}
v___jp_1349_:
{
lean_object* v_size_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_size_1352_ = lean_ctor_get(v___y_1350_, 0);
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_nat_add(v_size_1352_, v___x_1353_);
v___x_1355_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1350_, v___x_1354_, v_i_1351_, v_a_1297_, v___x_1348_);
lean_dec(v_i_1351_);
v___y_1339_ = v___x_1355_;
goto v___jp_1338_;
}
v___jp_1356_:
{
uint64_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_unbox_uint64(v_a_1297_);
v___x_1359_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v___y_1357_, v___x_1358_);
switch(lean_obj_tag(v___x_1359_))
{
case 0:
{
lean_object* v_index_1360_; lean_object* v_size_1361_; lean_object* v___x_1362_; 
v_index_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_index_1360_);
lean_dec_ref_known(v___x_1359_, 3);
v_size_1361_ = lean_ctor_get(v___y_1357_, 0);
lean_inc(v_size_1361_);
v___x_1362_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1357_, v_size_1361_, v_index_1360_, v_a_1297_, v___x_1348_);
lean_dec(v_index_1360_);
v___y_1339_ = v___x_1362_;
goto v___jp_1338_;
}
case 1:
{
lean_object* v_index_1363_; 
v_index_1363_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_index_1363_);
lean_dec_ref_known(v___x_1359_, 1);
v___y_1350_ = v___y_1357_;
v_i_1351_ = v_index_1363_;
goto v___jp_1349_;
}
default: 
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1357_, v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_index_1366_; 
v_index_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_index_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___y_1350_ = v___y_1357_;
v_i_1351_ = v_index_1366_;
goto v___jp_1349_;
}
else
{
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1297_);
v___y_1339_ = v___y_1357_;
goto v___jp_1338_;
}
}
}
}
v___jp_1367_:
{
lean_object* v_size_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_size_1370_ = lean_ctor_get(v___y_1368_, 0);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_size_1370_, v___x_1371_);
v___x_1373_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1368_, v___x_1372_, v_i_1369_, v_a_1297_, v___x_1348_);
lean_dec(v_i_1369_);
v___y_1339_ = v___x_1373_;
goto v___jp_1338_;
}
v___jp_1374_:
{
lean_object* v___x_1375_; uint64_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_keyToExprs_1334_);
lean_dec_ref(v_keyToExprs_1334_);
v___x_1376_ = lean_unbox_uint64(v_a_1297_);
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v___x_1375_, v___x_1376_);
switch(lean_obj_tag(v___x_1377_))
{
case 0:
{
lean_object* v_index_1378_; lean_object* v_size_1379_; lean_object* v___x_1380_; 
v_index_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_index_1378_);
lean_dec_ref_known(v___x_1377_, 3);
v_size_1379_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_size_1379_);
v___x_1380_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1375_, v_size_1379_, v_index_1378_, v_a_1297_, v___x_1348_);
lean_dec(v_index_1378_);
v___y_1339_ = v___x_1380_;
goto v___jp_1338_;
}
case 1:
{
lean_object* v_index_1381_; 
v_index_1381_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_index_1381_);
lean_dec_ref_known(v___x_1377_, 1);
v___y_1368_ = v___x_1375_;
v_i_1369_ = v_index_1381_;
goto v___jp_1367_;
}
default: 
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1375_, v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_index_1384_; 
v_index_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_index_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___y_1368_ = v___x_1375_;
v_i_1369_ = v_index_1384_;
goto v___jp_1367_;
}
else
{
lean_dec_ref(v___x_1348_);
lean_dec(v_a_1297_);
v___y_1339_ = v___x_1375_;
goto v___jp_1338_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_1418_; lean_object* v___x_1420_; 
lean_del_object(v___x_1330_);
lean_dec(v_val_1308_);
lean_dec(v_a_1297_);
lean_dec_ref(v_e_1288_);
v_val_1418_ = lean_ctor_get(v_fst_1328_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v_fst_1328_, 1);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_val_1418_);
v___x_1420_ = v___x_1326_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_val_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_val_1308_);
lean_dec(v_a_1297_);
lean_dec_ref(v_e_1288_);
v_a_1425_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1323_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1323_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v_cache_1434_; lean_object* v_keyToExprs_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v___x_1307_);
v___x_1433_ = lean_st_ref_take(v_a_1290_);
v_cache_1434_ = lean_ctor_get(v___x_1433_, 0);
v_keyToExprs_1435_ = lean_ctor_get(v___x_1433_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1437_ = v___x_1433_;
v_isShared_1438_ = v_isSharedCheck_1519_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_keyToExprs_1435_);
lean_inc(v_cache_1434_);
lean_dec(v___x_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1519_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___y_1440_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = lean_box(0);
lean_inc_ref(v_e_1288_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set_tag(v___x_1304_, 1);
lean_ctor_set(v___x_1304_, 1, v___x_1448_);
lean_ctor_set(v___x_1304_, 0, v_e_1288_);
v___x_1450_ = v___x_1304_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_e_1288_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1449_;
}
v___jp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___y_1440_);
v___x_1442_ = v___x_1437_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_cache_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___y_1440_);
v___x_1442_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_st_ref_put(v_a_1290_, v___x_1442_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_e_1288_);
v___x_1445_ = v___x_1299_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_e_1288_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
v_reusejp_1449_:
{
lean_object* v___y_1452_; lean_object* v_i_1453_; lean_object* v___y_1459_; lean_object* v___y_1470_; lean_object* v_i_1471_; uint64_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_unbox_uint64(v_a_1297_);
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1435_, v___x_1487_);
switch(lean_obj_tag(v___x_1488_))
{
case 0:
{
lean_object* v_index_1489_; lean_object* v_size_1490_; lean_object* v___x_1491_; 
v_index_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_index_1489_);
lean_dec_ref_known(v___x_1488_, 3);
v_size_1490_ = lean_ctor_get(v_keyToExprs_1435_, 0);
lean_inc(v_size_1490_);
v___x_1491_ = l_Std_DHashMap_Raw_setEntry___redArg(v_keyToExprs_1435_, v_size_1490_, v_index_1489_, v_a_1297_, v___x_1450_);
lean_dec(v_index_1489_);
v___y_1440_ = v___x_1491_;
goto v___jp_1439_;
}
case 1:
{
lean_object* v_index_1492_; lean_object* v_size_1493_; lean_object* v_keyArray_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v_index_1492_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_index_1492_);
lean_dec_ref_known(v___x_1488_, 1);
v_size_1493_ = lean_ctor_get(v_keyToExprs_1435_, 0);
v_keyArray_1494_ = lean_ctor_get(v_keyToExprs_1435_, 1);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_add(v_size_1493_, v___x_1495_);
v___x_1497_ = lean_array_get_size(v_keyArray_1494_);
v___x_1498_ = lean_nat_dec_lt(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_dec(v___x_1496_);
lean_dec(v_index_1492_);
goto v___jp_1476_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1499_ = lean_unsigned_to_nat(4u);
v___x_1500_ = lean_nat_mul(v___x_1496_, v___x_1499_);
v___x_1501_ = lean_unsigned_to_nat(3u);
v___x_1502_ = lean_nat_mul(v___x_1497_, v___x_1501_);
v___x_1503_ = lean_nat_dec_le(v___x_1500_, v___x_1502_);
lean_dec(v___x_1502_);
lean_dec(v___x_1500_);
if (v___x_1503_ == 0)
{
lean_dec(v___x_1496_);
lean_dec(v_index_1492_);
goto v___jp_1476_;
}
else
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DHashMap_Raw_setEntry___redArg(v_keyToExprs_1435_, v___x_1496_, v_index_1492_, v_a_1297_, v___x_1450_);
lean_dec(v_index_1492_);
v___y_1440_ = v___x_1504_;
goto v___jp_1439_;
}
}
}
default: 
{
lean_object* v_size_1505_; lean_object* v_keyArray_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_size_1505_ = lean_ctor_get(v_keyToExprs_1435_, 0);
v_keyArray_1506_ = lean_ctor_get(v_keyToExprs_1435_, 1);
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = lean_nat_add(v_size_1505_, v___x_1507_);
v___x_1509_ = lean_array_get_size(v_keyArray_1506_);
v___x_1510_ = lean_nat_dec_lt(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_dec(v___x_1508_);
v___x_1511_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_keyToExprs_1435_);
lean_dec_ref(v_keyToExprs_1435_);
v___y_1459_ = v___x_1511_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1512_ = lean_unsigned_to_nat(4u);
v___x_1513_ = lean_nat_mul(v___x_1508_, v___x_1512_);
lean_dec(v___x_1508_);
v___x_1514_ = lean_unsigned_to_nat(3u);
v___x_1515_ = lean_nat_mul(v___x_1509_, v___x_1514_);
v___x_1516_ = lean_nat_dec_le(v___x_1513_, v___x_1515_);
lean_dec(v___x_1515_);
lean_dec(v___x_1513_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_keyToExprs_1435_);
lean_dec_ref(v_keyToExprs_1435_);
v___y_1459_ = v___x_1517_;
goto v___jp_1458_;
}
else
{
v___y_1459_ = v_keyToExprs_1435_;
goto v___jp_1458_;
}
}
}
}
v___jp_1451_:
{
lean_object* v_size_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_size_1454_ = lean_ctor_get(v___y_1452_, 0);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_add(v_size_1454_, v___x_1455_);
v___x_1457_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1452_, v___x_1456_, v_i_1453_, v_a_1297_, v___x_1450_);
lean_dec(v_i_1453_);
v___y_1440_ = v___x_1457_;
goto v___jp_1439_;
}
v___jp_1458_:
{
uint64_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_unbox_uint64(v_a_1297_);
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v___y_1459_, v___x_1460_);
switch(lean_obj_tag(v___x_1461_))
{
case 0:
{
lean_object* v_index_1462_; lean_object* v_size_1463_; lean_object* v___x_1464_; 
v_index_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_index_1462_);
lean_dec_ref_known(v___x_1461_, 3);
v_size_1463_ = lean_ctor_get(v___y_1459_, 0);
lean_inc(v_size_1463_);
v___x_1464_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1459_, v_size_1463_, v_index_1462_, v_a_1297_, v___x_1450_);
lean_dec(v_index_1462_);
v___y_1440_ = v___x_1464_;
goto v___jp_1439_;
}
case 1:
{
lean_object* v_index_1465_; 
v_index_1465_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_index_1465_);
lean_dec_ref_known(v___x_1461_, 1);
v___y_1452_ = v___y_1459_;
v_i_1453_ = v_index_1465_;
goto v___jp_1451_;
}
default: 
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1459_, v___x_1466_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_index_1468_; 
v_index_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_index_1468_);
lean_dec_ref_known(v___x_1467_, 1);
v___y_1452_ = v___y_1459_;
v_i_1453_ = v_index_1468_;
goto v___jp_1451_;
}
else
{
lean_dec_ref(v___x_1450_);
lean_dec(v_a_1297_);
v___y_1440_ = v___y_1459_;
goto v___jp_1439_;
}
}
}
}
v___jp_1469_:
{
lean_object* v_size_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_size_1472_ = lean_ctor_get(v___y_1470_, 0);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_size_1472_, v___x_1473_);
v___x_1475_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1470_, v___x_1474_, v_i_1471_, v_a_1297_, v___x_1450_);
lean_dec(v_i_1471_);
v___y_1440_ = v___x_1475_;
goto v___jp_1439_;
}
v___jp_1476_:
{
lean_object* v___x_1477_; uint64_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_keyToExprs_1435_);
lean_dec_ref(v_keyToExprs_1435_);
v___x_1478_ = lean_unbox_uint64(v_a_1297_);
v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v___x_1477_, v___x_1478_);
switch(lean_obj_tag(v___x_1479_))
{
case 0:
{
lean_object* v_index_1480_; lean_object* v_size_1481_; lean_object* v___x_1482_; 
v_index_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_index_1480_);
lean_dec_ref_known(v___x_1479_, 3);
v_size_1481_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_size_1481_);
v___x_1482_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1477_, v_size_1481_, v_index_1480_, v_a_1297_, v___x_1450_);
lean_dec(v_index_1480_);
v___y_1440_ = v___x_1482_;
goto v___jp_1439_;
}
case 1:
{
lean_object* v_index_1483_; 
v_index_1483_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_index_1483_);
lean_dec_ref_known(v___x_1479_, 1);
v___y_1470_ = v___x_1477_;
v_i_1471_ = v_index_1483_;
goto v___jp_1469_;
}
default: 
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1477_, v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_index_1486_; 
v_index_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_index_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___y_1470_ = v___x_1477_;
v_i_1471_ = v_index_1486_;
goto v___jp_1469_;
}
else
{
lean_dec_ref(v___x_1450_);
lean_dec(v_a_1297_);
v___y_1440_ = v___x_1477_;
goto v___jp_1439_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v_e_1288_);
v_a_1523_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1296_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1296_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
uint8_t v_a_boxed_1539_; lean_object* v_res_1540_; 
v_a_boxed_1539_ = lean_unbox(v_a_1532_);
v_res_1540_ = l_Lean_Meta_Canonicalizer_canon(v_e_1531_, v_a_boxed_1539_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object* v_00_u03b2_1541_, lean_object* v_m_1542_, uint64_t v_a_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_1542_, v_a_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* v_00_u03b2_1545_, lean_object* v_m_1546_, lean_object* v_a_1547_){
_start:
{
uint64_t v_a_boxed_1548_; lean_object* v_res_1549_; 
v_a_boxed_1548_ = lean_unbox_uint64(v_a_1547_);
lean_dec_ref(v_a_1547_);
v_res_1549_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(v_00_u03b2_1545_, v_m_1546_, v_a_boxed_1548_);
lean_dec_ref(v_m_1546_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object* v_e_1550_, lean_object* v_as_1551_, lean_object* v_as_x27_1552_, lean_object* v_b_1553_, lean_object* v_a_1554_, uint8_t v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1550_, v_as_x27_1552_, v_b_1553_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object* v_e_1563_, lean_object* v_as_1564_, lean_object* v_as_x27_1565_, lean_object* v_b_1566_, lean_object* v_a_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v___y_16443__boxed_1575_; lean_object* v_res_1576_; 
v___y_16443__boxed_1575_ = lean_unbox(v___y_1568_);
v_res_1576_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(v_e_1563_, v_as_1564_, v_as_x27_1565_, v_b_1566_, v_a_1567_, v___y_16443__boxed_1575_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v_as_x27_1565_);
lean_dec(v_as_1564_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2(lean_object* v_00_u03b2_1577_, lean_object* v_m_1578_, uint64_t v_query_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1578_, v_query_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2___boxed(lean_object* v_00_u03b2_1581_, lean_object* v_m_1582_, lean_object* v_query_1583_){
_start:
{
uint64_t v_query_boxed_1584_; lean_object* v_res_1585_; 
v_query_boxed_1584_ = lean_unbox_uint64(v_query_1583_);
lean_dec_ref(v_query_1583_);
v_res_1585_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2(v_00_u03b2_1581_, v_m_1582_, v_query_boxed_1584_);
lean_dec_ref(v_m_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3(lean_object* v_00_u03b2_1586_, lean_object* v_m_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___redArg(v_m_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3___boxed(lean_object* v_00_u03b2_1589_, lean_object* v_m_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3(v_00_u03b2_1589_, v_m_1590_);
lean_dec_ref(v_m_1590_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(lean_object* v_00_u03b2_1592_, lean_object* v_m_1593_, uint64_t v_query_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_m_1593_, v_query_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1596_, lean_object* v_m_1597_, lean_object* v_query_1598_){
_start:
{
uint64_t v_query_boxed_1599_; lean_object* v_res_1600_; 
v_query_boxed_1599_ = lean_unbox_uint64(v_query_1598_);
lean_dec_ref(v_query_1598_);
v_res_1600_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(v_00_u03b2_1596_, v_m_1597_, v_query_boxed_1599_);
lean_dec_ref(v_m_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(lean_object* v_00_u03b2_1601_, lean_object* v_m_1602_, uint64_t v_query_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_m_1602_, v_query_1603_, v_x_1604_, v_x_1605_, v_x_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1609_, lean_object* v_m_1610_, lean_object* v_query_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
uint64_t v_query_boxed_1616_; lean_object* v_res_1617_; 
v_query_boxed_1616_ = lean_unbox_uint64(v_query_1611_);
lean_dec_ref(v_query_1611_);
v_res_1617_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(v_00_u03b2_1609_, v_m_1610_, v_query_boxed_1616_, v_x_1612_, v_x_1613_, v_x_1614_, v_x_1615_);
lean_dec_ref(v_m_1610_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5(lean_object* v_00_u03b2_1618_, lean_object* v_init_1619_, lean_object* v_b_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___redArg(v_init_1619_, v_b_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1622_, lean_object* v_init_1623_, lean_object* v_b_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5(v_00_u03b2_1622_, v_init_1623_, v_b_1624_);
lean_dec_ref(v_b_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1626_, lean_object* v_b_1627_, lean_object* v_acc_1628_, lean_object* v_i_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___redArg(v_b_1627_, v_acc_1628_, v_i_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1631_, lean_object* v_b_1632_, lean_object* v_acc_1633_, lean_object* v_i_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Canonicalizer_canon_spec__3_spec__5_spec__6(v_00_u03b2_1631_, v_b_1632_, v_acc_1633_, v_i_1634_);
lean_dec_ref(v_b_1632_);
return v_res_1635_;
}
}
lean_object* runtime_initialize_Lean_Util_ShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Canonicalizer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited_default);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited);
l_Lean_Meta_Canonicalizer_instInhabitedState = _init_l_Lean_Meta_Canonicalizer_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Canonicalizer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Canonicalizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Canonicalizer(builtin);
}
#ifdef __cplusplus
}
#endif
