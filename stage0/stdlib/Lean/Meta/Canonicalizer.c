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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
lean_object* l_instDecidableEqUInt64___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value),((lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_box(0);
v___x_29_ = lean_unsigned_to_nat(16u);
v___x_30_ = lean_mk_array(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0);
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState(void){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object* v_x_37_, uint8_t v_transparency_38_, lean_object* v_s_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_st_mk_ref(v_s_39_);
v___x_46_ = lean_box(v_transparency_38_);
lean_inc(v_a_43_);
lean_inc_ref(v_a_42_);
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v___x_45_);
v___x_47_ = lean_apply_7(v_x_37_, v___x_46_, v___x_45_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, lean_box(0));
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_56_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_56_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lean_st_ref_get(v___x_45_);
lean_dec(v___x_45_);
lean_dec(v___x_52_);
if (v_isShared_51_ == 0)
{
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_48_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
else
{
lean_dec(v___x_45_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object* v_x_57_, lean_object* v_transparency_58_, lean_object* v_s_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
uint8_t v_transparency_boxed_65_; lean_object* v_res_66_; 
v_transparency_boxed_65_ = lean_unbox(v_transparency_58_);
v_res_66_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v_x_57_, v_transparency_boxed_65_, v_s_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object* v_00_u03b1_67_, lean_object* v_x_68_, uint8_t v_transparency_69_, lean_object* v_s_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v_x_68_, v_transparency_69_, v_s_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v_transparency_79_, lean_object* v_s_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
uint8_t v_transparency_boxed_86_; lean_object* v_res_87_; 
v_transparency_boxed_86_ = lean_unbox(v_transparency_79_);
v_res_87_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27(v_00_u03b1_77_, v_x_78_, v_transparency_boxed_86_, v_s_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object* v_x_88_, uint8_t v_transparency_89_, lean_object* v_s_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_st_mk_ref(v_s_90_);
v___x_97_ = lean_box(v_transparency_89_);
lean_inc(v_a_94_);
lean_inc_ref(v_a_93_);
lean_inc(v_a_92_);
lean_inc_ref(v_a_91_);
lean_inc(v___x_96_);
v___x_98_ = lean_apply_7(v_x_88_, v___x_97_, v___x_96_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, lean_box(0));
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_108_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_108_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = lean_st_ref_get(v___x_96_);
lean_dec(v___x_96_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_a_99_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec(v___x_96_);
v_a_109_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_98_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_98_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object* v_x_117_, lean_object* v_transparency_118_, lean_object* v_s_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
uint8_t v_transparency_boxed_125_; lean_object* v_res_126_; 
v_transparency_boxed_125_ = lean_unbox(v_transparency_118_);
v_res_126_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(v_x_117_, v_transparency_boxed_125_, v_s_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object* v_00_u03b1_127_, lean_object* v_x_128_, uint8_t v_transparency_129_, lean_object* v_s_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(v_x_128_, v_transparency_129_, v_s_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object* v_00_u03b1_137_, lean_object* v_x_138_, lean_object* v_transparency_139_, lean_object* v_s_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_transparency_boxed_146_; lean_object* v_res_147_; 
v_transparency_boxed_146_ = lean_unbox(v_transparency_139_);
v_res_147_ = l_Lean_Meta_Canonicalizer_CanonM_run(v_00_u03b1_137_, v_x_138_, v_transparency_boxed_146_, v_s_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object* v_e_148_, lean_object* v_____do__lift_149_){
_start:
{
lean_object* v_cache_150_; lean_object* v_buckets_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_cache_150_ = lean_ctor_get(v_____do__lift_149_, 0);
v_buckets_151_ = lean_ctor_get(v_cache_150_, 1);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_array_get_size(v_buckets_151_);
v___x_154_ = lean_nat_dec_lt(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
lean_dec_ref(v_e_148_);
v___x_155_ = lean_box(0);
return v___x_155_;
}
else
{
lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_158_; 
v___f_156_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_157_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_156_, v___f_157_, v_cache_150_, v_e_148_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object* v_e_159_, lean_object* v_____do__lift_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(v_e_159_, v_____do__lift_160_);
lean_dec_ref(v_____do__lift_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object* v_e_162_, uint64_t v_key_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v_cache_172_; lean_object* v_keyToExprs_173_; lean_object* v_buckets_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_166_ = lean_st_ref_take(v_a_164_);
v_cache_172_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_cache_172_);
v_keyToExprs_173_ = lean_ctor_get(v___x_166_, 1);
lean_inc_ref(v_keyToExprs_173_);
v_buckets_174_ = lean_ctor_get(v_cache_172_, 1);
v___x_175_ = lean_box(0);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_array_get_size(v_buckets_174_);
v___x_178_ = lean_nat_dec_lt(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec_ref(v_keyToExprs_173_);
lean_dec_ref(v_cache_172_);
lean_dec_ref(v_e_162_);
v_fst_168_ = v___x_175_;
v_snd_169_ = v___x_166_;
goto v___jp_167_;
}
else
{
lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_189_; 
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_190_ = lean_ctor_get(v___x_166_, 1);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v___x_166_, 0);
lean_dec(v_unused_191_);
v___x_180_ = v___x_166_;
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
else
{
lean_dec(v___x_166_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___f_182_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_183_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_184_ = lean_box_uint64(v_key_163_);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_182_, v___f_183_, v_cache_172_, v_e_162_, v___x_184_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_185_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_keyToExprs_173_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v_fst_168_ = v___x_175_;
v_snd_169_ = v___x_187_;
goto v___jp_167_;
}
}
}
v___jp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_st_ref_set(v_a_164_, v_snd_169_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v_fst_168_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object* v_e_192_, lean_object* v_key_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
uint64_t v_key_boxed_196_; lean_object* v_res_197_; 
v_key_boxed_196_ = lean_unbox_uint64(v_key_193_);
lean_dec_ref(v_key_193_);
v_res_197_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_192_, v_key_boxed_196_, v_a_194_);
lean_dec(v_a_194_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object* v_e_198_, uint64_t v_key_199_, uint8_t v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v_cache_213_; lean_object* v_keyToExprs_214_; lean_object* v_buckets_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_207_ = lean_st_ref_take(v_a_201_);
v_cache_213_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_cache_213_);
v_keyToExprs_214_ = lean_ctor_get(v___x_207_, 1);
lean_inc_ref(v_keyToExprs_214_);
v_buckets_215_ = lean_ctor_get(v_cache_213_, 1);
v___x_216_ = lean_box(0);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_array_get_size(v_buckets_215_);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_keyToExprs_214_);
lean_dec_ref(v_cache_213_);
lean_dec_ref(v_e_198_);
v_fst_209_ = v___x_216_;
v_snd_210_ = v___x_207_;
goto v___jp_208_;
}
else
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_230_; 
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_231_ = lean_ctor_get(v___x_207_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v___x_207_, 0);
lean_dec(v_unused_232_);
v___x_221_ = v___x_207_;
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
else
{
lean_dec(v___x_207_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___f_223_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_224_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_225_ = lean_box_uint64(v_key_199_);
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_223_, v___f_224_, v_cache_213_, v_e_198_, v___x_225_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_226_);
v___x_228_ = v___x_221_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_keyToExprs_214_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v_fst_209_ = v___x_216_;
v_snd_210_ = v___x_228_;
goto v___jp_208_;
}
}
}
v___jp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_st_ref_set(v_a_201_, v_snd_210_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v_fst_209_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object* v_e_233_, lean_object* v_key_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
uint64_t v_key_boxed_242_; uint8_t v_a_boxed_243_; lean_object* v_res_244_; 
v_key_boxed_242_ = lean_unbox_uint64(v_key_234_);
lean_dec_ref(v_key_234_);
v_a_boxed_243_ = lean_unbox(v_a_235_);
v_res_244_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(v_e_233_, v_key_boxed_242_, v_a_boxed_243_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object* v_e_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = l_Lean_Expr_hasMVar(v_e_245_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_e_245_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v_mctx_251_; lean_object* v___x_252_; lean_object* v_fst_253_; lean_object* v_snd_254_; lean_object* v___x_255_; lean_object* v_cache_256_; lean_object* v_zetaDeltaFVarIds_257_; lean_object* v_postponed_258_; lean_object* v_diag_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_268_; 
v___x_250_ = lean_st_ref_get(v___y_246_);
v_mctx_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc_ref(v_mctx_251_);
lean_dec(v___x_250_);
v___x_252_ = l_Lean_instantiateMVarsCore(v_mctx_251_, v_e_245_);
v_fst_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_fst_253_);
v_snd_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_snd_254_);
lean_dec_ref(v___x_252_);
v___x_255_ = lean_st_ref_take(v___y_246_);
v_cache_256_ = lean_ctor_get(v___x_255_, 1);
v_zetaDeltaFVarIds_257_ = lean_ctor_get(v___x_255_, 2);
v_postponed_258_ = lean_ctor_get(v___x_255_, 3);
v_diag_259_ = lean_ctor_get(v___x_255_, 4);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; 
v_unused_269_ = lean_ctor_get(v___x_255_, 0);
lean_dec(v_unused_269_);
v___x_261_ = v___x_255_;
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_diag_259_);
lean_inc(v_postponed_258_);
lean_inc(v_zetaDeltaFVarIds_257_);
lean_inc(v_cache_256_);
lean_dec(v___x_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_snd_254_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_snd_254_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_cache_256_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_zetaDeltaFVarIds_257_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_postponed_258_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_diag_259_);
v___x_264_ = v_reuseFailAlloc_267_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_st_ref_set(v___y_246_, v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_fst_253_);
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object* v_e_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_270_, v___y_271_);
lean_dec(v___y_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object* v_e_274_, uint8_t v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_274_, v___y_278_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object* v_e_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint8_t v___y_13886__boxed_291_; lean_object* v_res_292_; 
v___y_13886__boxed_291_ = lean_unbox(v___y_284_);
v_res_292_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v_e_283_, v___y_13886__boxed_291_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v_key_296_; lean_object* v_value_297_; lean_object* v_tail_298_; size_t v___x_299_; size_t v___x_300_; uint8_t v___x_301_; 
v_key_296_ = lean_ctor_get(v_x_294_, 0);
v_value_297_ = lean_ctor_get(v_x_294_, 1);
v_tail_298_ = lean_ctor_get(v_x_294_, 2);
v___x_299_ = lean_ptr_addr(v_key_296_);
v___x_300_ = lean_ptr_addr(v_a_293_);
v___x_301_ = lean_usize_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
v_x_294_ = v_tail_298_;
goto _start;
}
else
{
lean_object* v___x_303_; 
lean_inc(v_value_297_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v_value_297_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg___boxed(lean_object* v_a_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(v_a_304_, v_x_305_);
lean_dec(v_x_305_);
lean_dec_ref(v_a_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(lean_object* v_m_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_buckets_309_; lean_object* v___x_310_; size_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v_fold_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_buckets_309_ = lean_ctor_get(v_m_307_, 1);
v___x_310_ = lean_array_get_size(v_buckets_309_);
v___x_311_ = lean_ptr_addr(v_a_308_);
v___x_312_ = lean_usize_to_uint64(v___x_311_);
v___x_313_ = 32ULL;
v___x_314_ = lean_uint64_shift_right(v___x_312_, v___x_313_);
v_fold_315_ = lean_uint64_xor(v___x_312_, v___x_314_);
v___x_316_ = 16ULL;
v___x_317_ = lean_uint64_shift_right(v_fold_315_, v___x_316_);
v___x_318_ = lean_uint64_xor(v_fold_315_, v___x_317_);
v___x_319_ = lean_uint64_to_usize(v___x_318_);
v___x_320_ = lean_usize_of_nat(v___x_310_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_sub(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_land(v___x_319_, v___x_322_);
v___x_324_ = lean_array_uget_borrowed(v_buckets_309_, v___x_323_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(v_a_308_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg___boxed(lean_object* v_m_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_m_326_, v_a_327_);
lean_dec_ref(v_a_327_);
lean_dec_ref(v_m_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
return v_x_329_;
}
else
{
lean_object* v_key_331_; lean_object* v_value_332_; lean_object* v_tail_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_357_; 
v_key_331_ = lean_ctor_get(v_x_330_, 0);
v_value_332_ = lean_ctor_get(v_x_330_, 1);
v_tail_333_ = lean_ctor_get(v_x_330_, 2);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_330_);
if (v_isSharedCheck_357_ == 0)
{
v___x_335_ = v_x_330_;
v_isShared_336_ = v_isSharedCheck_357_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_tail_333_);
lean_inc(v_value_332_);
lean_inc(v_key_331_);
lean_dec(v_x_330_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_357_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; size_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_337_ = lean_array_get_size(v_x_329_);
v___x_338_ = lean_ptr_addr(v_key_331_);
v___x_339_ = lean_usize_to_uint64(v___x_338_);
v___x_340_ = 32ULL;
v___x_341_ = lean_uint64_shift_right(v___x_339_, v___x_340_);
v_fold_342_ = lean_uint64_xor(v___x_339_, v___x_341_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_337_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v___x_351_ = lean_array_uget_borrowed(v_x_329_, v___x_350_);
lean_inc(v___x_351_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 2, v___x_351_);
v___x_353_ = v___x_335_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_key_331_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_value_332_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v___x_351_);
v___x_353_ = v_reuseFailAlloc_356_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_array_uset(v_x_329_, v___x_350_, v___x_353_);
v_x_329_ = v___x_354_;
v_x_330_ = v_tail_333_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(lean_object* v_i_358_, lean_object* v_source_359_, lean_object* v_target_360_){
_start:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_array_get_size(v_source_359_);
v___x_362_ = lean_nat_dec_lt(v_i_358_, v___x_361_);
if (v___x_362_ == 0)
{
lean_dec_ref(v_source_359_);
lean_dec(v_i_358_);
return v_target_360_;
}
else
{
lean_object* v_es_363_; lean_object* v___x_364_; lean_object* v_source_365_; lean_object* v_target_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_es_363_ = lean_array_fget(v_source_359_, v_i_358_);
v___x_364_ = lean_box(0);
v_source_365_ = lean_array_fset(v_source_359_, v_i_358_, v___x_364_);
v_target_366_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(v_target_360_, v_es_363_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v_i_358_, v___x_367_);
lean_dec(v_i_358_);
v_i_358_ = v___x_368_;
v_source_359_ = v_source_365_;
v_target_360_ = v_target_366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(lean_object* v_data_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_nbuckets_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_371_ = lean_array_get_size(v_data_370_);
v___x_372_ = lean_unsigned_to_nat(2u);
v_nbuckets_373_ = lean_nat_mul(v___x_371_, v___x_372_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_box(0);
v___x_376_ = lean_mk_array(v_nbuckets_373_, v___x_375_);
v___x_377_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(v___x_374_, v_data_370_, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_dec(v_b_379_);
lean_dec_ref(v_a_378_);
return v_x_380_;
}
else
{
lean_object* v_key_381_; lean_object* v_value_382_; lean_object* v_tail_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_397_; 
v_key_381_ = lean_ctor_get(v_x_380_, 0);
v_value_382_ = lean_ctor_get(v_x_380_, 1);
v_tail_383_ = lean_ctor_get(v_x_380_, 2);
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_380_);
if (v_isSharedCheck_397_ == 0)
{
v___x_385_ = v_x_380_;
v_isShared_386_ = v_isSharedCheck_397_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_tail_383_);
lean_inc(v_value_382_);
lean_inc(v_key_381_);
lean_dec(v_x_380_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_397_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
size_t v___x_387_; size_t v___x_388_; uint8_t v___x_389_; 
v___x_387_ = lean_ptr_addr(v_key_381_);
v___x_388_ = lean_ptr_addr(v_a_378_);
v___x_389_ = lean_usize_dec_eq(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_378_, v_b_379_, v_tail_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 2, v___x_390_);
v___x_392_ = v___x_385_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_key_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_value_382_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
else
{
lean_object* v___x_395_; 
lean_dec(v_value_382_);
lean_dec(v_key_381_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v_b_379_);
lean_ctor_set(v___x_385_, 0, v_a_378_);
v___x_395_ = v___x_385_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_378_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_b_379_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_tail_383_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(lean_object* v_a_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
else
{
lean_object* v_key_401_; lean_object* v_tail_402_; size_t v___x_403_; size_t v___x_404_; uint8_t v___x_405_; 
v_key_401_ = lean_ctor_get(v_x_399_, 0);
v_tail_402_ = lean_ctor_get(v_x_399_, 2);
v___x_403_ = lean_ptr_addr(v_key_401_);
v___x_404_ = lean_ptr_addr(v_a_398_);
v___x_405_ = lean_usize_dec_eq(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
v_x_399_ = v_tail_402_;
goto _start;
}
else
{
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg___boxed(lean_object* v_a_407_, lean_object* v_x_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_407_, v_x_408_);
lean_dec(v_x_408_);
lean_dec_ref(v_a_407_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object* v_m_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v_size_414_; lean_object* v_buckets_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_459_; 
v_size_414_ = lean_ctor_get(v_m_411_, 0);
v_buckets_415_ = lean_ctor_get(v_m_411_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_m_411_);
if (v_isSharedCheck_459_ == 0)
{
v___x_417_ = v_m_411_;
v_isShared_418_ = v_isSharedCheck_459_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_buckets_415_);
lean_inc(v_size_414_);
lean_dec(v_m_411_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_459_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; size_t v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v_fold_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v___x_432_; lean_object* v_bkt_433_; uint8_t v___x_434_; 
v___x_419_ = lean_array_get_size(v_buckets_415_);
v___x_420_ = lean_ptr_addr(v_a_412_);
v___x_421_ = lean_usize_to_uint64(v___x_420_);
v___x_422_ = 32ULL;
v___x_423_ = lean_uint64_shift_right(v___x_421_, v___x_422_);
v_fold_424_ = lean_uint64_xor(v___x_421_, v___x_423_);
v___x_425_ = 16ULL;
v___x_426_ = lean_uint64_shift_right(v_fold_424_, v___x_425_);
v___x_427_ = lean_uint64_xor(v_fold_424_, v___x_426_);
v___x_428_ = lean_uint64_to_usize(v___x_427_);
v___x_429_ = lean_usize_of_nat(v___x_419_);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_sub(v___x_429_, v___x_430_);
v___x_432_ = lean_usize_land(v___x_428_, v___x_431_);
v_bkt_433_ = lean_array_uget_borrowed(v_buckets_415_, v___x_432_);
v___x_434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_412_, v_bkt_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v_size_x27_436_; lean_object* v___x_437_; lean_object* v_buckets_x27_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v_size_x27_436_ = lean_nat_add(v_size_414_, v___x_435_);
lean_dec(v_size_414_);
lean_inc(v_bkt_433_);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v_a_412_);
lean_ctor_set(v___x_437_, 1, v_b_413_);
lean_ctor_set(v___x_437_, 2, v_bkt_433_);
v_buckets_x27_438_ = lean_array_uset(v_buckets_415_, v___x_432_, v___x_437_);
v___x_439_ = lean_unsigned_to_nat(4u);
v___x_440_ = lean_nat_mul(v_size_x27_436_, v___x_439_);
v___x_441_ = lean_unsigned_to_nat(3u);
v___x_442_ = lean_nat_div(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_array_get_size(v_buckets_x27_438_);
v___x_444_ = lean_nat_dec_le(v___x_442_, v___x_443_);
lean_dec(v___x_442_);
if (v___x_444_ == 0)
{
lean_object* v_val_445_; lean_object* v___x_447_; 
v_val_445_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(v_buckets_x27_438_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_val_445_);
lean_ctor_set(v___x_417_, 0, v_size_x27_436_);
v___x_447_ = v___x_417_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_size_x27_436_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_val_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
else
{
lean_object* v___x_450_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_buckets_x27_438_);
lean_ctor_set(v___x_417_, 0, v_size_x27_436_);
v___x_450_ = v___x_417_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_size_x27_436_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_buckets_x27_438_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_object* v___x_452_; lean_object* v_buckets_x27_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
lean_inc(v_bkt_433_);
v___x_452_ = lean_box(0);
v_buckets_x27_453_ = lean_array_uset(v_buckets_415_, v___x_432_, v___x_452_);
v___x_454_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_412_, v_b_413_, v_bkt_433_);
v___x_455_ = lean_array_uset(v_buckets_x27_453_, v___x_432_, v___x_454_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_455_);
v___x_457_ = v___x_417_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_size_414_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
static uint64_t _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2(void){
_start:
{
lean_object* v___x_464_; uint64_t v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(1723u);
v___x_465_ = lean_uint64_of_nat(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1(void){
_start:
{
uint64_t v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_uint64_once(&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2, &l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_once, _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2);
v___x_467_ = lean_box_uint64(v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* v_e_468_, uint8_t v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_t_477_; lean_object* v_b_478_; uint8_t v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint64_t v___y_501_; lean_object* v___y_502_; lean_object* v_snd_503_; uint64_t v_key_508_; lean_object* v___y_509_; lean_object* v___y_529_; lean_object* v_info_530_; uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_544_; uint8_t v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___x_564_; lean_object* v_cache_652_; lean_object* v_buckets_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_564_ = lean_st_ref_get(v_a_470_);
v_cache_652_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_cache_652_);
lean_dec(v___x_564_);
v_buckets_653_ = lean_ctor_get(v_cache_652_, 1);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_array_get_size(v_buckets_653_);
v___x_656_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec_ref(v_cache_652_);
goto v___jp_565_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_cache_652_, v_e_468_);
lean_dec_ref(v_cache_652_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_e_468_);
v_val_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 0);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_val_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_dec(v___x_657_);
goto v___jp_565_;
}
}
v___jp_476_:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_t_477_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_b_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_499_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_499_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_492_ = lean_unbox_uint64(v_a_486_);
lean_dec(v_a_486_);
v___x_493_ = lean_unbox_uint64(v_a_488_);
lean_dec(v_a_488_);
v___x_494_ = lean_uint64_mix_hash(v___x_492_, v___x_493_);
v___x_495_ = lean_box_uint64(v___x_494_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_495_);
v___x_497_ = v___x_490_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_dec(v_a_486_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_b_478_);
return v___x_485_;
}
}
v___jp_500_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_st_ref_set(v___y_502_, v_snd_503_);
v___x_505_ = lean_box_uint64(v___y_501_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
v___jp_507_:
{
lean_object* v___x_510_; lean_object* v_cache_511_; lean_object* v_keyToExprs_512_; lean_object* v_buckets_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_510_ = lean_st_ref_take(v___y_509_);
v_cache_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc_ref(v_cache_511_);
v_keyToExprs_512_ = lean_ctor_get(v___x_510_, 1);
lean_inc_ref(v_keyToExprs_512_);
v_buckets_513_ = lean_ctor_get(v_cache_511_, 1);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_array_get_size(v_buckets_513_);
v___x_516_ = lean_nat_dec_lt(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec_ref(v_keyToExprs_512_);
lean_dec_ref(v_cache_511_);
lean_dec_ref(v_e_468_);
v___y_501_ = v_key_508_;
v___y_502_ = v___y_509_;
v_snd_503_ = v___x_510_;
goto v___jp_500_;
}
else
{
lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_526_ = lean_ctor_get(v___x_510_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v___x_510_, 0);
lean_dec(v_unused_527_);
v___x_518_ = v___x_510_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_dec(v___x_510_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_box_uint64(v_key_508_);
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_cache_511_, v_e_468_, v___x_520_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_521_);
v___x_523_ = v___x_518_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_keyToExprs_512_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
v___y_501_ = v_key_508_;
v___y_502_ = v___y_509_;
v_snd_503_ = v___x_523_;
goto v___jp_500_;
}
}
}
}
v___jp_528_:
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___y_529_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint64_t v___x_541_; lean_object* v___x_542_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_Expr_getAppNumArgs(v_e_468_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_unbox_uint64(v_a_538_);
lean_dec(v_a_538_);
v___x_542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_539_, v_e_468_, v___x_539_, v_info_530_, v___x_540_, v___x_541_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec_ref(v_info_530_);
lean_dec_ref(v_e_468_);
lean_dec(v___x_539_);
return v___x_542_;
}
else
{
lean_dec_ref(v_info_530_);
lean_dec_ref(v_e_468_);
return v___x_537_;
}
}
v___jp_543_:
{
uint8_t v___x_551_; 
v___x_551_ = l_Lean_Expr_hasLooseBVars(v___y_544_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_box(0);
lean_inc_ref(v___y_544_);
v___x_553_ = l_Lean_Meta_getFunInfo(v___y_544_, v___x_552_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___y_529_ = v___y_544_;
v_info_530_ = v_a_554_;
v___y_531_ = v___y_545_;
v___y_532_ = v___y_546_;
v___y_533_ = v___y_547_;
v___y_534_ = v___y_548_;
v___y_535_ = v___y_549_;
v___y_536_ = v___y_550_;
goto v___jp_528_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v___y_544_);
lean_dec_ref(v_e_468_);
v_a_555_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_553_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1));
v___y_529_ = v___y_544_;
v_info_530_ = v___x_563_;
v___y_531_ = v___y_545_;
v___y_532_ = v___y_546_;
v___y_533_ = v___y_547_;
v___y_534_ = v___y_548_;
v___y_535_ = v___y_549_;
v___y_536_ = v___y_550_;
goto v___jp_528_;
}
}
v___jp_565_:
{
switch(lean_obj_tag(v_e_468_))
{
case 2:
{
lean_object* v___x_566_; 
lean_inc_ref(v_e_468_);
v___x_566_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_468_, v_a_472_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_580_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_580_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_580_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_580_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
uint8_t v___x_571_; 
v___x_571_ = lean_expr_eqv(v_a_567_, v_e_468_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_del_object(v___x_569_);
v___x_572_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_a_567_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; uint64_t v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = lean_unbox_uint64(v_a_573_);
lean_dec(v_a_573_);
v_key_508_ = v___x_574_;
v___y_509_ = v_a_470_;
goto v___jp_507_;
}
else
{
lean_dec_ref_known(v_e_468_, 1);
return v___x_572_;
}
}
else
{
uint64_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_dec(v_a_567_);
v___x_575_ = l_Lean_Expr_hash(v_e_468_);
lean_dec_ref_known(v_e_468_, 1);
v___x_576_ = lean_box_uint64(v___x_575_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_576_);
v___x_578_ = v___x_569_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref_known(v_e_468_, 1);
v_a_581_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_566_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_566_);
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
case 4:
{
lean_object* v_declName_589_; 
v_declName_589_ = lean_ctor_get(v_e_468_, 0);
lean_inc(v_declName_589_);
lean_dec_ref_known(v_e_468_, 2);
if (lean_obj_tag(v_declName_589_) == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
else
{
uint64_t v_hash_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_hash_592_ = lean_ctor_get_uint64(v_declName_589_, sizeof(void*)*2);
lean_dec(v_declName_589_);
v___x_593_ = lean_box_uint64(v_hash_592_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
case 5:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = l_Lean_Expr_getAppFn(v_e_468_);
v___x_596_ = l_Lean_Expr_isMVar(v___x_595_);
if (v___x_596_ == 0)
{
v___y_544_ = v___x_595_;
v___y_545_ = v_a_469_;
v___y_546_ = v_a_470_;
v___y_547_ = v_a_471_;
v___y_548_ = v_a_472_;
v___y_549_ = v_a_473_;
v___y_550_ = v_a_474_;
goto v___jp_543_;
}
else
{
lean_object* v___x_597_; 
lean_inc_ref(v_e_468_);
v___x_597_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_468_, v_a_472_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; uint8_t v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = lean_expr_eqv(v_a_598_, v_e_468_);
if (v___x_599_ == 0)
{
lean_dec_ref_known(v_e_468_, 2);
lean_dec_ref(v___x_595_);
v_e_468_ = v_a_598_;
goto _start;
}
else
{
lean_dec(v_a_598_);
v___y_544_ = v___x_595_;
v___y_545_ = v_a_469_;
v___y_546_ = v_a_470_;
v___y_547_ = v_a_471_;
v___y_548_ = v_a_472_;
v___y_549_ = v_a_473_;
v___y_550_ = v_a_474_;
goto v___jp_543_;
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref_known(v_e_468_, 2);
lean_dec_ref(v___x_595_);
v_a_601_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_597_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_609_; lean_object* v_body_610_; 
v_binderType_609_ = lean_ctor_get(v_e_468_, 1);
lean_inc_ref(v_binderType_609_);
v_body_610_ = lean_ctor_get(v_e_468_, 2);
lean_inc_ref(v_body_610_);
lean_dec_ref_known(v_e_468_, 3);
v_t_477_ = v_binderType_609_;
v_b_478_ = v_body_610_;
v___y_479_ = v_a_469_;
v___y_480_ = v_a_470_;
v___y_481_ = v_a_471_;
v___y_482_ = v_a_472_;
v___y_483_ = v_a_473_;
v___y_484_ = v_a_474_;
goto v___jp_476_;
}
case 7:
{
lean_object* v_binderType_611_; lean_object* v_body_612_; 
v_binderType_611_ = lean_ctor_get(v_e_468_, 1);
lean_inc_ref(v_binderType_611_);
v_body_612_ = lean_ctor_get(v_e_468_, 2);
lean_inc_ref(v_body_612_);
lean_dec_ref_known(v_e_468_, 3);
v_t_477_ = v_binderType_611_;
v_b_478_ = v_body_612_;
v___y_479_ = v_a_469_;
v___y_480_ = v_a_470_;
v___y_481_ = v_a_471_;
v___y_482_ = v_a_472_;
v___y_483_ = v_a_473_;
v___y_484_ = v_a_474_;
goto v___jp_476_;
}
case 8:
{
lean_object* v_value_613_; lean_object* v_body_614_; lean_object* v___x_615_; 
v_value_613_ = lean_ctor_get(v_e_468_, 2);
lean_inc_ref(v_value_613_);
v_body_614_ = lean_ctor_get(v_e_468_, 3);
lean_inc_ref(v_body_614_);
lean_dec_ref_known(v_e_468_, 4);
v___x_615_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_613_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_614_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_629_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_629_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint64_t v___x_622_; uint64_t v___x_623_; uint64_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_622_ = lean_unbox_uint64(v_a_616_);
lean_dec(v_a_616_);
v___x_623_ = lean_unbox_uint64(v_a_618_);
lean_dec(v_a_618_);
v___x_624_ = lean_uint64_mix_hash(v___x_622_, v___x_623_);
v___x_625_ = lean_box_uint64(v___x_624_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_625_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_dec(v_a_616_);
return v___x_617_;
}
}
else
{
lean_dec_ref(v_body_614_);
return v___x_615_;
}
}
case 10:
{
lean_object* v_expr_630_; lean_object* v___x_631_; 
v_expr_630_ = lean_ctor_get(v_e_468_, 1);
lean_inc_ref(v_expr_630_);
v___x_631_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_630_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; uint64_t v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = lean_unbox_uint64(v_a_632_);
lean_dec(v_a_632_);
v_key_508_ = v___x_633_;
v___y_509_ = v_a_470_;
goto v___jp_507_;
}
else
{
lean_dec_ref_known(v_e_468_, 2);
return v___x_631_;
}
}
case 11:
{
lean_object* v_idx_634_; lean_object* v_struct_635_; lean_object* v___x_636_; 
v_idx_634_ = lean_ctor_get(v_e_468_, 1);
lean_inc(v_idx_634_);
v_struct_635_ = lean_ctor_get(v_e_468_, 2);
lean_inc_ref(v_struct_635_);
lean_dec_ref_known(v_e_468_, 3);
v___x_636_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_635_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_648_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_648_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_648_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_648_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
uint64_t v___x_641_; uint64_t v___x_642_; uint64_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_641_ = lean_uint64_of_nat(v_idx_634_);
lean_dec(v_idx_634_);
v___x_642_ = lean_unbox_uint64(v_a_637_);
lean_dec(v_a_637_);
v___x_643_ = lean_uint64_mix_hash(v___x_641_, v___x_642_);
v___x_644_ = lean_box_uint64(v___x_643_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_644_);
v___x_646_ = v___x_639_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_dec(v_idx_634_);
return v___x_636_;
}
}
default: 
{
uint64_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = l_Lean_Expr_hash(v_e_468_);
lean_dec_ref(v_e_468_);
v___x_650_ = lean_box_uint64(v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(lean_object* v___x_666_, lean_object* v_e_667_, lean_object* v_upperBound_668_, lean_object* v_info_669_, lean_object* v_a_670_, uint64_t v_b_671_, uint8_t v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
uint64_t v_a_680_; uint8_t v___y_685_; uint8_t v___x_694_; 
v___x_694_ = lean_nat_dec_lt(v_a_670_, v_upperBound_668_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_a_670_);
v___x_695_ = lean_box_uint64(v_b_671_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v_paramInfo_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_paramInfo_697_ = lean_ctor_get(v_info_669_, 0);
v___x_698_ = lean_array_get_size(v_paramInfo_697_);
v___x_699_ = lean_nat_dec_lt(v_a_670_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_700_ = lean_nat_sub(v___x_666_, v_a_670_);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_sub(v___x_700_, v___x_701_);
lean_dec(v___x_700_);
v___x_703_ = l_Lean_Expr_getRevArg_x21(v_e_667_, v___x_702_);
v___x_704_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_703_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; uint64_t v___x_706_; uint64_t v___x_707_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_unbox_uint64(v_a_705_);
lean_dec(v_a_705_);
v___x_707_ = lean_uint64_mix_hash(v_b_671_, v___x_706_);
v_a_680_ = v___x_707_;
goto v___jp_679_;
}
else
{
lean_dec(v_a_670_);
return v___x_704_;
}
}
else
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_array_fget_borrowed(v_paramInfo_697_, v_a_670_);
v___x_709_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_708_);
if (v___x_709_ == 0)
{
v___y_685_ = v___x_709_;
goto v___jp_684_;
}
else
{
uint8_t v_isProp_710_; 
v_isProp_710_ = lean_ctor_get_uint8(v___x_708_, sizeof(void*)*1 + 2);
if (v_isProp_710_ == 0)
{
v___y_685_ = v___x_709_;
goto v___jp_684_;
}
else
{
v_a_680_ = v_b_671_;
goto v___jp_679_;
}
}
}
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_a_670_, v___x_681_);
lean_dec(v_a_670_);
v_a_670_ = v___x_682_;
v_b_671_ = v_a_680_;
goto _start;
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
v_a_680_ = v_b_671_;
goto v___jp_679_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_686_ = lean_nat_sub(v___x_666_, v_a_670_);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_sub(v___x_686_, v___x_687_);
lean_dec(v___x_686_);
v___x_689_ = l_Lean_Expr_getRevArg_x21(v_e_667_, v___x_688_);
v___x_690_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_689_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; uint64_t v___x_692_; uint64_t v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = lean_unbox_uint64(v_a_691_);
lean_dec(v_a_691_);
v___x_693_ = lean_uint64_mix_hash(v_b_671_, v___x_692_);
v_a_680_ = v___x_693_;
goto v___jp_679_;
}
else
{
lean_dec(v_a_670_);
return v___x_690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg___boxed(lean_object* v___x_711_, lean_object* v_e_712_, lean_object* v_upperBound_713_, lean_object* v_info_714_, lean_object* v_a_715_, lean_object* v_b_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint64_t v_b_boxed_724_; uint8_t v___y_14188__boxed_725_; lean_object* v_res_726_; 
v_b_boxed_724_ = lean_unbox_uint64(v_b_716_);
lean_dec_ref(v_b_716_);
v___y_14188__boxed_725_ = lean_unbox(v___y_717_);
v_res_726_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_711_, v_e_712_, v_upperBound_713_, v_info_714_, v_a_715_, v_b_boxed_724_, v___y_14188__boxed_725_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v_info_714_);
lean_dec(v_upperBound_713_);
lean_dec_ref(v_e_712_);
lean_dec(v___x_711_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* v_e_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
uint8_t v_a_boxed_735_; lean_object* v_res_736_; 
v_a_boxed_735_ = lean_unbox(v_a_728_);
v_res_736_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_727_, v_a_boxed_735_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* v_00_u03b2_737_, lean_object* v_m_738_, lean_object* v_a_739_, lean_object* v_b_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_m_738_, v_a_739_, v_b_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(lean_object* v___x_742_, lean_object* v_e_743_, lean_object* v_upperBound_744_, lean_object* v_info_745_, lean_object* v_inst_746_, lean_object* v_R_747_, lean_object* v_a_748_, uint64_t v_b_749_, lean_object* v_c_750_, uint8_t v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_742_, v_e_743_, v_upperBound_744_, v_info_745_, v_a_748_, v_b_749_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___boxed(lean_object* v___x_759_, lean_object* v_e_760_, lean_object* v_upperBound_761_, lean_object* v_info_762_, lean_object* v_inst_763_, lean_object* v_R_764_, lean_object* v_a_765_, lean_object* v_b_766_, lean_object* v_c_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint64_t v_b_boxed_775_; uint8_t v___y_14686__boxed_776_; lean_object* v_res_777_; 
v_b_boxed_775_ = lean_unbox_uint64(v_b_766_);
lean_dec_ref(v_b_766_);
v___y_14686__boxed_776_ = lean_unbox(v___y_768_);
v_res_777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(v___x_759_, v_e_760_, v_upperBound_761_, v_info_762_, v_inst_763_, v_R_764_, v_a_765_, v_b_boxed_775_, v_c_767_, v___y_14686__boxed_776_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v_info_762_);
lean_dec(v_upperBound_761_);
lean_dec_ref(v_e_760_);
lean_dec(v___x_759_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(lean_object* v_00_u03b2_778_, lean_object* v_m_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_m_779_, v_a_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___boxed(lean_object* v_00_u03b2_782_, lean_object* v_m_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(v_00_u03b2_782_, v_m_783_, v_a_784_);
lean_dec_ref(v_a_784_);
lean_dec_ref(v_m_783_);
return v_res_785_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(lean_object* v_00_u03b2_786_, lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___boxed(lean_object* v_00_u03b2_790_, lean_object* v_a_791_, lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(v_00_u03b2_790_, v_a_791_, v_x_792_);
lean_dec(v_x_792_);
lean_dec_ref(v_a_791_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1(lean_object* v_00_u03b2_795_, lean_object* v_data_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(v_data_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2(lean_object* v_00_u03b2_798_, lean_object* v_a_799_, lean_object* v_b_800_, lean_object* v_x_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_799_, v_b_800_, v_x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6(lean_object* v_00_u03b2_803_, lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(v_a_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___boxed(lean_object* v_00_u03b2_807_, lean_object* v_a_808_, lean_object* v_x_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6(v_00_u03b2_807_, v_a_808_, v_x_809_);
lean_dec(v_x_809_);
lean_dec_ref(v_a_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_811_, lean_object* v_i_812_, lean_object* v_source_813_, lean_object* v_target_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(v_i_812_, v_source_813_, v_target_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(v_x_817_, v_x_818_);
return v___x_819_;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_821_; lean_object* v___f_822_; 
v___x_821_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_822_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_822_, 0, v___x_821_);
return v___f_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t v_k_823_, lean_object* v_____do__lift_824_){
_start:
{
lean_object* v_keyToExprs_825_; lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_keyToExprs_825_ = lean_ctor_get(v_____do__lift_824_, 1);
v___f_826_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0));
v___f_827_ = lean_obj_once(&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1, &l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1_once, _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1);
v___x_828_ = lean_box_uint64(v_k_823_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_827_, v___f_826_, v_keyToExprs_825_, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* v_k_830_, lean_object* v_____do__lift_831_){
_start:
{
uint64_t v_k_boxed_832_; lean_object* v_res_833_; 
v_k_boxed_832_ = lean_unbox_uint64(v_k_830_);
lean_dec_ref(v_k_830_);
v_res_833_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v_k_boxed_832_, v_____do__lift_831_);
lean_dec_ref(v_____do__lift_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(uint64_t v_a_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_box(0);
return v___x_836_;
}
else
{
lean_object* v_key_837_; lean_object* v_value_838_; lean_object* v_tail_839_; uint64_t v___x_840_; uint8_t v___x_841_; 
v_key_837_ = lean_ctor_get(v_x_835_, 0);
v_value_838_ = lean_ctor_get(v_x_835_, 1);
v_tail_839_ = lean_ctor_get(v_x_835_, 2);
v___x_840_ = lean_unbox_uint64(v_key_837_);
v___x_841_ = lean_uint64_dec_eq(v___x_840_, v_a_834_);
if (v___x_841_ == 0)
{
v_x_835_ = v_tail_839_;
goto _start;
}
else
{
lean_object* v___x_843_; 
lean_inc(v_value_838_);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v_value_838_);
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg___boxed(lean_object* v_a_844_, lean_object* v_x_845_){
_start:
{
uint64_t v_a_boxed_846_; lean_object* v_res_847_; 
v_a_boxed_846_ = lean_unbox_uint64(v_a_844_);
lean_dec_ref(v_a_844_);
v_res_847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_boxed_846_, v_x_845_);
lean_dec(v_x_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object* v_m_848_, uint64_t v_a_849_){
_start:
{
lean_object* v_buckets_850_; lean_object* v___x_851_; uint64_t v___x_852_; uint64_t v___x_853_; uint64_t v_fold_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_buckets_850_ = lean_ctor_get(v_m_848_, 1);
v___x_851_ = lean_array_get_size(v_buckets_850_);
v___x_852_ = 32ULL;
v___x_853_ = lean_uint64_shift_right(v_a_849_, v___x_852_);
v_fold_854_ = lean_uint64_xor(v_a_849_, v___x_853_);
v___x_855_ = 16ULL;
v___x_856_ = lean_uint64_shift_right(v_fold_854_, v___x_855_);
v___x_857_ = lean_uint64_xor(v_fold_854_, v___x_856_);
v___x_858_ = lean_uint64_to_usize(v___x_857_);
v___x_859_ = lean_usize_of_nat(v___x_851_);
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_sub(v___x_859_, v___x_860_);
v___x_862_ = lean_usize_land(v___x_858_, v___x_861_);
v___x_863_ = lean_array_uget_borrowed(v_buckets_850_, v___x_862_);
v___x_864_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_849_, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* v_m_865_, lean_object* v_a_866_){
_start:
{
uint64_t v_a_boxed_867_; lean_object* v_res_868_; 
v_a_boxed_867_ = lean_unbox_uint64(v_a_866_);
lean_dec_ref(v_a_866_);
v_res_868_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_865_, v_a_boxed_867_);
lean_dec_ref(v_m_865_);
return v_res_868_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(uint64_t v_a_869_, lean_object* v_x_870_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
uint8_t v___x_871_; 
v___x_871_ = 0;
return v___x_871_;
}
else
{
lean_object* v_key_872_; lean_object* v_tail_873_; uint64_t v___x_874_; uint8_t v___x_875_; 
v_key_872_ = lean_ctor_get(v_x_870_, 0);
v_tail_873_ = lean_ctor_get(v_x_870_, 2);
v___x_874_ = lean_unbox_uint64(v_key_872_);
v___x_875_ = lean_uint64_dec_eq(v___x_874_, v_a_869_);
if (v___x_875_ == 0)
{
v_x_870_ = v_tail_873_;
goto _start;
}
else
{
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg___boxed(lean_object* v_a_877_, lean_object* v_x_878_){
_start:
{
uint64_t v_a_boxed_879_; uint8_t v_res_880_; lean_object* v_r_881_; 
v_a_boxed_879_ = lean_unbox_uint64(v_a_877_);
lean_dec_ref(v_a_877_);
v_res_880_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_boxed_879_, v_x_878_);
lean_dec(v_x_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(uint64_t v_a_882_, lean_object* v_b_883_, lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_dec(v_b_883_);
return v_x_884_;
}
else
{
lean_object* v_key_885_; lean_object* v_value_886_; lean_object* v_tail_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_901_; 
v_key_885_ = lean_ctor_get(v_x_884_, 0);
v_value_886_ = lean_ctor_get(v_x_884_, 1);
v_tail_887_ = lean_ctor_get(v_x_884_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_901_ == 0)
{
v___x_889_ = v_x_884_;
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_tail_887_);
lean_inc(v_value_886_);
lean_inc(v_key_885_);
lean_dec(v_x_884_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint64_t v___x_891_; uint8_t v___x_892_; 
v___x_891_ = lean_unbox_uint64(v_key_885_);
v___x_892_ = lean_uint64_dec_eq(v___x_891_, v_a_882_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_882_, v_b_883_, v_tail_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 2, v___x_893_);
v___x_895_ = v___x_889_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_key_885_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_value_886_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v_value_886_);
lean_dec(v_key_885_);
v___x_897_ = lean_box_uint64(v_a_882_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v_b_883_);
lean_ctor_set(v___x_889_, 0, v___x_897_);
v___x_899_ = v___x_889_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_b_883_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_tail_887_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg___boxed(lean_object* v_a_902_, lean_object* v_b_903_, lean_object* v_x_904_){
_start:
{
uint64_t v_a_boxed_905_; lean_object* v_res_906_; 
v_a_boxed_905_ = lean_unbox_uint64(v_a_902_);
lean_dec_ref(v_a_902_);
v_res_906_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_boxed_905_, v_b_903_, v_x_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
return v_x_907_;
}
else
{
lean_object* v_key_909_; lean_object* v_value_910_; lean_object* v_tail_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_935_; 
v_key_909_ = lean_ctor_get(v_x_908_, 0);
v_value_910_ = lean_ctor_get(v_x_908_, 1);
v_tail_911_ = lean_ctor_get(v_x_908_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_935_ == 0)
{
v___x_913_ = v_x_908_;
v_isShared_914_ = v_isSharedCheck_935_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_tail_911_);
lean_inc(v_value_910_);
lean_inc(v_key_909_);
lean_dec(v_x_908_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_935_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; uint64_t v_fold_920_; uint64_t v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_915_ = lean_array_get_size(v_x_907_);
v___x_916_ = 32ULL;
v___x_917_ = lean_unbox_uint64(v_key_909_);
v___x_918_ = lean_uint64_shift_right(v___x_917_, v___x_916_);
v___x_919_ = lean_unbox_uint64(v_key_909_);
v_fold_920_ = lean_uint64_xor(v___x_919_, v___x_918_);
v___x_921_ = 16ULL;
v___x_922_ = lean_uint64_shift_right(v_fold_920_, v___x_921_);
v___x_923_ = lean_uint64_xor(v_fold_920_, v___x_922_);
v___x_924_ = lean_uint64_to_usize(v___x_923_);
v___x_925_ = lean_usize_of_nat(v___x_915_);
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_sub(v___x_925_, v___x_926_);
v___x_928_ = lean_usize_land(v___x_924_, v___x_927_);
v___x_929_ = lean_array_uget_borrowed(v_x_907_, v___x_928_);
lean_inc(v___x_929_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 2, v___x_929_);
v___x_931_ = v___x_913_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_key_909_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_value_910_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v___x_929_);
v___x_931_ = v_reuseFailAlloc_934_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; 
v___x_932_ = lean_array_uset(v_x_907_, v___x_928_, v___x_931_);
v_x_907_ = v___x_932_;
v_x_908_ = v_tail_911_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(lean_object* v_i_936_, lean_object* v_source_937_, lean_object* v_target_938_){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_array_get_size(v_source_937_);
v___x_940_ = lean_nat_dec_lt(v_i_936_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_source_937_);
lean_dec(v_i_936_);
return v_target_938_;
}
else
{
lean_object* v_es_941_; lean_object* v___x_942_; lean_object* v_source_943_; lean_object* v_target_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_es_941_ = lean_array_fget(v_source_937_, v_i_936_);
v___x_942_ = lean_box(0);
v_source_943_ = lean_array_fset(v_source_937_, v_i_936_, v___x_942_);
v_target_944_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(v_target_938_, v_es_941_);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_add(v_i_936_, v___x_945_);
lean_dec(v_i_936_);
v_i_936_ = v___x_946_;
v_source_937_ = v_source_943_;
v_target_938_ = v_target_944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(lean_object* v_data_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_nbuckets_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_949_ = lean_array_get_size(v_data_948_);
v___x_950_ = lean_unsigned_to_nat(2u);
v_nbuckets_951_ = lean_nat_mul(v___x_949_, v___x_950_);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_box(0);
v___x_954_ = lean_mk_array(v_nbuckets_951_, v___x_953_);
v___x_955_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(v___x_952_, v_data_948_, v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(lean_object* v_m_956_, uint64_t v_a_957_, lean_object* v_b_958_){
_start:
{
lean_object* v_size_959_; lean_object* v_buckets_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1003_; 
v_size_959_ = lean_ctor_get(v_m_956_, 0);
v_buckets_960_ = lean_ctor_get(v_m_956_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_m_956_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_962_ = v_m_956_;
v_isShared_963_ = v_isSharedCheck_1003_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_buckets_960_);
lean_inc(v_size_959_);
lean_dec(v_m_956_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1003_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v_fold_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; lean_object* v_bkt_976_; uint8_t v___x_977_; 
v___x_964_ = lean_array_get_size(v_buckets_960_);
v___x_965_ = 32ULL;
v___x_966_ = lean_uint64_shift_right(v_a_957_, v___x_965_);
v_fold_967_ = lean_uint64_xor(v_a_957_, v___x_966_);
v___x_968_ = 16ULL;
v___x_969_ = lean_uint64_shift_right(v_fold_967_, v___x_968_);
v___x_970_ = lean_uint64_xor(v_fold_967_, v___x_969_);
v___x_971_ = lean_uint64_to_usize(v___x_970_);
v___x_972_ = lean_usize_of_nat(v___x_964_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_sub(v___x_972_, v___x_973_);
v___x_975_ = lean_usize_land(v___x_971_, v___x_974_);
v_bkt_976_ = lean_array_uget_borrowed(v_buckets_960_, v___x_975_);
v___x_977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_957_, v_bkt_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v_size_x27_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_buckets_x27_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_978_ = lean_unsigned_to_nat(1u);
v_size_x27_979_ = lean_nat_add(v_size_959_, v___x_978_);
lean_dec(v_size_959_);
v___x_980_ = lean_box_uint64(v_a_957_);
lean_inc(v_bkt_976_);
v___x_981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v_b_958_);
lean_ctor_set(v___x_981_, 2, v_bkt_976_);
v_buckets_x27_982_ = lean_array_uset(v_buckets_960_, v___x_975_, v___x_981_);
v___x_983_ = lean_unsigned_to_nat(4u);
v___x_984_ = lean_nat_mul(v_size_x27_979_, v___x_983_);
v___x_985_ = lean_unsigned_to_nat(3u);
v___x_986_ = lean_nat_div(v___x_984_, v___x_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_array_get_size(v_buckets_x27_982_);
v___x_988_ = lean_nat_dec_le(v___x_986_, v___x_987_);
lean_dec(v___x_986_);
if (v___x_988_ == 0)
{
lean_object* v_val_989_; lean_object* v___x_991_; 
v_val_989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(v_buckets_x27_982_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v_val_989_);
lean_ctor_set(v___x_962_, 0, v_size_x27_979_);
v___x_991_ = v___x_962_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_size_x27_979_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_val_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v___x_994_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v_buckets_x27_982_);
lean_ctor_set(v___x_962_, 0, v_size_x27_979_);
v___x_994_ = v___x_962_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_size_x27_979_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_buckets_x27_982_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
lean_object* v___x_996_; lean_object* v_buckets_x27_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_inc(v_bkt_976_);
v___x_996_ = lean_box(0);
v_buckets_x27_997_ = lean_array_uset(v_buckets_960_, v___x_975_, v___x_996_);
v___x_998_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_957_, v_b_958_, v_bkt_976_);
v___x_999_ = lean_array_uset(v_buckets_x27_997_, v___x_975_, v___x_998_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_999_);
v___x_1001_ = v___x_962_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_size_959_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg___boxed(lean_object* v_m_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_){
_start:
{
uint64_t v_a_boxed_1007_; lean_object* v_res_1008_; 
v_a_boxed_1007_ = lean_unbox_uint64(v_a_1005_);
lean_dec_ref(v_a_1005_);
v_res_1008_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1004_, v_a_boxed_1007_, v_b_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* v_e_1012_, lean_object* v_as_x27_1013_, lean_object* v_b_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
if (lean_obj_tag(v_as_x27_1013_) == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v_e_1012_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_b_1014_);
return v___x_1020_;
}
else
{
lean_object* v_head_1021_; lean_object* v_tail_1022_; lean_object* v___x_1023_; 
lean_dec_ref(v_b_1014_);
v_head_1021_ = lean_ctor_get(v_as_x27_1013_, 0);
v_tail_1022_ = lean_ctor_get(v_as_x27_1013_, 1);
lean_inc(v_head_1021_);
lean_inc_ref(v_e_1012_);
v___x_1023_ = l_Lean_Meta_isExprDefEq(v_e_1012_, v_head_1021_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1037_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1037_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1037_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_unbox(v_a_1024_);
lean_dec(v_a_1024_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
lean_del_object(v___x_1026_);
v___x_1030_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
v_as_x27_1013_ = v_tail_1022_;
v_b_1014_ = v___x_1030_;
goto _start;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_dec_ref(v_e_1012_);
lean_inc(v_head_1021_);
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_head_1021_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_1028_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1033_);
v___x_1035_ = v___x_1026_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_e_1012_);
v_a_1038_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1023_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1023_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object* v_e_1046_, lean_object* v_as_x27_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1046_, v_as_x27_1047_, v_b_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v_as_x27_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* v_e_1055_, uint8_t v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1063_; 
lean_inc_ref(v_e_1055_);
v___x_1063_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1186_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1186_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1186_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v_keyToExprs_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1184_; 
v___x_1068_ = lean_st_ref_get(v_a_1057_);
v_keyToExprs_1069_ = lean_ctor_get(v___x_1068_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1185_);
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1184_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_keyToExprs_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1184_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
uint64_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_unbox_uint64(v_a_1064_);
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_keyToExprs_1069_, v___x_1073_);
lean_dec_ref(v_keyToExprs_1069_);
if (lean_obj_tag(v___x_1074_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1076_; uint8_t v_foApprox_1077_; uint8_t v_ctxApprox_1078_; uint8_t v_quasiPatternApprox_1079_; uint8_t v_constApprox_1080_; uint8_t v_isDefEqStuckEx_1081_; uint8_t v_unificationHints_1082_; uint8_t v_proofIrrelevance_1083_; uint8_t v_assignSyntheticOpaque_1084_; uint8_t v_offsetCnstrs_1085_; uint8_t v_etaStruct_1086_; uint8_t v_univApprox_1087_; uint8_t v_iota_1088_; uint8_t v_beta_1089_; uint8_t v_proj_1090_; uint8_t v_zeta_1091_; uint8_t v_zetaDelta_1092_; uint8_t v_zetaUnused_1093_; uint8_t v_zetaHave_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1163_; 
lean_del_object(v___x_1071_);
lean_del_object(v___x_1066_);
v_val_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = l_Lean_Meta_Context_config(v_a_1058_);
v_foApprox_1077_ = lean_ctor_get_uint8(v___x_1076_, 0);
v_ctxApprox_1078_ = lean_ctor_get_uint8(v___x_1076_, 1);
v_quasiPatternApprox_1079_ = lean_ctor_get_uint8(v___x_1076_, 2);
v_constApprox_1080_ = lean_ctor_get_uint8(v___x_1076_, 3);
v_isDefEqStuckEx_1081_ = lean_ctor_get_uint8(v___x_1076_, 4);
v_unificationHints_1082_ = lean_ctor_get_uint8(v___x_1076_, 5);
v_proofIrrelevance_1083_ = lean_ctor_get_uint8(v___x_1076_, 6);
v_assignSyntheticOpaque_1084_ = lean_ctor_get_uint8(v___x_1076_, 7);
v_offsetCnstrs_1085_ = lean_ctor_get_uint8(v___x_1076_, 8);
v_etaStruct_1086_ = lean_ctor_get_uint8(v___x_1076_, 10);
v_univApprox_1087_ = lean_ctor_get_uint8(v___x_1076_, 11);
v_iota_1088_ = lean_ctor_get_uint8(v___x_1076_, 12);
v_beta_1089_ = lean_ctor_get_uint8(v___x_1076_, 13);
v_proj_1090_ = lean_ctor_get_uint8(v___x_1076_, 14);
v_zeta_1091_ = lean_ctor_get_uint8(v___x_1076_, 15);
v_zetaDelta_1092_ = lean_ctor_get_uint8(v___x_1076_, 16);
v_zetaUnused_1093_ = lean_ctor_get_uint8(v___x_1076_, 17);
v_zetaHave_1094_ = lean_ctor_get_uint8(v___x_1076_, 18);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1096_ = v___x_1076_;
v_isShared_1097_ = v_isSharedCheck_1163_;
goto v_resetjp_1095_;
}
else
{
lean_dec(v___x_1076_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1163_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
uint8_t v_trackZetaDelta_1098_; lean_object* v_zetaDeltaSet_1099_; lean_object* v_lctx_1100_; lean_object* v_localInstances_1101_; lean_object* v_defEqCtx_x3f_1102_; lean_object* v_synthPendingDepth_1103_; lean_object* v_canUnfold_x3f_1104_; uint8_t v_univApprox_1105_; uint8_t v_inTypeClassResolution_1106_; uint8_t v_cacheInferType_1107_; lean_object* v_config_1109_; 
v_trackZetaDelta_1098_ = lean_ctor_get_uint8(v_a_1058_, sizeof(void*)*7);
v_zetaDeltaSet_1099_ = lean_ctor_get(v_a_1058_, 1);
v_lctx_1100_ = lean_ctor_get(v_a_1058_, 2);
v_localInstances_1101_ = lean_ctor_get(v_a_1058_, 3);
v_defEqCtx_x3f_1102_ = lean_ctor_get(v_a_1058_, 4);
v_synthPendingDepth_1103_ = lean_ctor_get(v_a_1058_, 5);
v_canUnfold_x3f_1104_ = lean_ctor_get(v_a_1058_, 6);
v_univApprox_1105_ = lean_ctor_get_uint8(v_a_1058_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1106_ = lean_ctor_get_uint8(v_a_1058_, sizeof(void*)*7 + 2);
v_cacheInferType_1107_ = lean_ctor_get_uint8(v_a_1058_, sizeof(void*)*7 + 3);
if (v_isShared_1097_ == 0)
{
v_config_1109_ = v___x_1096_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 0, v_foApprox_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 1, v_ctxApprox_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 2, v_quasiPatternApprox_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 3, v_constApprox_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 4, v_isDefEqStuckEx_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 5, v_unificationHints_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 6, v_proofIrrelevance_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 7, v_assignSyntheticOpaque_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 8, v_offsetCnstrs_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 10, v_etaStruct_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 11, v_univApprox_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 12, v_iota_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 13, v_beta_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 14, v_proj_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 15, v_zeta_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 16, v_zetaDelta_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 17, v_zetaUnused_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, 18, v_zetaHave_1094_);
v_config_1109_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
uint64_t v___x_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; lean_object* v___x_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; uint64_t v_key_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_ctor_set_uint8(v_config_1109_, 9, v_a_1056_);
v___x_1110_ = l_Lean_Meta_Context_configKey(v_a_1058_);
v___x_1111_ = 3ULL;
v___x_1112_ = lean_uint64_shift_right(v___x_1110_, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
v___x_1114_ = lean_uint64_shift_left(v___x_1112_, v___x_1111_);
v___x_1115_ = l_Lean_Meta_TransparencyMode_toUInt64(v_a_1056_);
v_key_1116_ = lean_uint64_lor(v___x_1114_, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1117_, 0, v_config_1109_);
lean_ctor_set_uint64(v___x_1117_, sizeof(void*)*1, v_key_1116_);
lean_inc(v_canUnfold_x3f_1104_);
lean_inc(v_synthPendingDepth_1103_);
lean_inc(v_defEqCtx_x3f_1102_);
lean_inc_ref(v_localInstances_1101_);
lean_inc_ref(v_lctx_1100_);
lean_inc(v_zetaDeltaSet_1099_);
v___x_1118_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_zetaDeltaSet_1099_);
lean_ctor_set(v___x_1118_, 2, v_lctx_1100_);
lean_ctor_set(v___x_1118_, 3, v_localInstances_1101_);
lean_ctor_set(v___x_1118_, 4, v_defEqCtx_x3f_1102_);
lean_ctor_set(v___x_1118_, 5, v_synthPendingDepth_1103_);
lean_ctor_set(v___x_1118_, 6, v_canUnfold_x3f_1104_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*7, v_trackZetaDelta_1098_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*7 + 1, v_univApprox_1105_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1106_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*7 + 3, v_cacheInferType_1107_);
lean_inc_ref(v_e_1055_);
v___x_1119_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1055_, v_val_1075_, v___x_1113_, v___x_1118_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec_ref_known(v___x_1118_, 7);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1153_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1153_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1153_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_fst_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1151_; 
v_fst_1124_ = lean_ctor_get(v_a_1120_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_a_1120_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v_a_1120_, 1);
lean_dec(v_unused_1152_);
v___x_1126_ = v_a_1120_;
v_isShared_1127_ = v_isSharedCheck_1151_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_fst_1124_);
lean_dec(v_a_1120_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1151_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
if (lean_obj_tag(v_fst_1124_) == 0)
{
lean_object* v___x_1128_; lean_object* v_cache_1129_; lean_object* v_keyToExprs_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1146_; 
v___x_1128_ = lean_st_ref_take(v_a_1057_);
v_cache_1129_ = lean_ctor_get(v___x_1128_, 0);
v_keyToExprs_1130_ = lean_ctor_get(v___x_1128_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1132_ = v___x_1128_;
v_isShared_1133_ = v_isSharedCheck_1146_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_keyToExprs_1130_);
lean_inc(v_cache_1129_);
lean_dec(v___x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1146_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
lean_inc_ref(v_e_1055_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set_tag(v___x_1126_, 1);
lean_ctor_set(v___x_1126_, 1, v_val_1075_);
lean_ctor_set(v___x_1126_, 0, v_e_1055_);
v___x_1135_ = v___x_1126_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_e_1055_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_val_1075_);
v___x_1135_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
uint64_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = lean_unbox_uint64(v_a_1064_);
lean_dec(v_a_1064_);
v___x_1137_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1130_, v___x_1136_, v___x_1135_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1137_);
v___x_1139_ = v___x_1132_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_cache_1129_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_st_ref_set(v_a_1057_, v___x_1139_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v_e_1055_);
v___x_1142_ = v___x_1122_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_e_1055_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; 
lean_del_object(v___x_1126_);
lean_dec(v_val_1075_);
lean_dec(v_a_1064_);
lean_dec_ref(v_e_1055_);
v_val_1147_ = lean_ctor_get(v_fst_1124_, 0);
lean_inc(v_val_1147_);
lean_dec_ref_known(v_fst_1124_, 1);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v_val_1147_);
v___x_1149_ = v___x_1122_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_val_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_val_1075_);
lean_dec(v_a_1064_);
lean_dec_ref(v_e_1055_);
v_a_1154_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1119_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1119_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
else
{
lean_object* v___x_1164_; lean_object* v_cache_1165_; lean_object* v_keyToExprs_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v___x_1074_);
v___x_1164_ = lean_st_ref_take(v_a_1057_);
v_cache_1165_ = lean_ctor_get(v___x_1164_, 0);
v_keyToExprs_1166_ = lean_ctor_get(v___x_1164_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1168_ = v___x_1164_;
v_isShared_1169_ = v_isSharedCheck_1183_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_keyToExprs_1166_);
lean_inc(v_cache_1165_);
lean_dec(v___x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1183_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_box(0);
lean_inc_ref(v_e_1055_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 1);
lean_ctor_set(v___x_1071_, 1, v___x_1170_);
lean_ctor_set(v___x_1071_, 0, v_e_1055_);
v___x_1172_ = v___x_1071_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_e_1055_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
uint64_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1173_ = lean_unbox_uint64(v_a_1064_);
lean_dec(v_a_1064_);
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1166_, v___x_1173_, v___x_1172_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1174_);
v___x_1176_ = v___x_1168_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_cache_1165_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_st_ref_set(v_a_1057_, v___x_1176_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v_e_1055_);
v___x_1179_ = v___x_1066_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_e_1055_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
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
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_e_1055_);
v_a_1187_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1063_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1063_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* v_e_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
uint8_t v_a_boxed_1203_; lean_object* v_res_1204_; 
v_a_boxed_1203_ = lean_unbox(v_a_1196_);
v_res_1204_ = l_Lean_Meta_Canonicalizer_canon(v_e_1195_, v_a_boxed_1203_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object* v_00_u03b2_1205_, lean_object* v_m_1206_, uint64_t v_a_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_1206_, v_a_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* v_00_u03b2_1209_, lean_object* v_m_1210_, lean_object* v_a_1211_){
_start:
{
uint64_t v_a_boxed_1212_; lean_object* v_res_1213_; 
v_a_boxed_1212_ = lean_unbox_uint64(v_a_1211_);
lean_dec_ref(v_a_1211_);
v_res_1213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(v_00_u03b2_1209_, v_m_1210_, v_a_boxed_1212_);
lean_dec_ref(v_m_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object* v_e_1214_, lean_object* v_as_1215_, lean_object* v_as_x27_1216_, lean_object* v_b_1217_, lean_object* v_a_1218_, uint8_t v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1214_, v_as_x27_1216_, v_b_1217_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object* v_e_1227_, lean_object* v_as_1228_, lean_object* v_as_x27_1229_, lean_object* v_b_1230_, lean_object* v_a_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___y_11069__boxed_1239_; lean_object* v_res_1240_; 
v___y_11069__boxed_1239_ = lean_unbox(v___y_1232_);
v_res_1240_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(v_e_1227_, v_as_1228_, v_as_x27_1229_, v_b_1230_, v_a_1231_, v___y_11069__boxed_1239_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v_as_x27_1229_);
lean_dec(v_as_1228_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(lean_object* v_00_u03b2_1241_, lean_object* v_m_1242_, uint64_t v_a_1243_, lean_object* v_b_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1242_, v_a_1243_, v_b_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_, lean_object* v_b_1249_){
_start:
{
uint64_t v_a_boxed_1250_; lean_object* v_res_1251_; 
v_a_boxed_1250_ = lean_unbox_uint64(v_a_1248_);
lean_dec_ref(v_a_1248_);
v_res_1251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(v_00_u03b2_1246_, v_m_1247_, v_a_boxed_1250_, v_b_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(lean_object* v_00_u03b2_1252_, uint64_t v_a_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_1253_, v_x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1256_, lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
uint64_t v_a_boxed_1259_; lean_object* v_res_1260_; 
v_a_boxed_1259_ = lean_unbox_uint64(v_a_1257_);
lean_dec_ref(v_a_1257_);
v_res_1260_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(v_00_u03b2_1256_, v_a_boxed_1259_, v_x_1258_);
lean_dec(v_x_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(lean_object* v_00_u03b2_1261_, uint64_t v_a_1262_, lean_object* v_x_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_a_1266_, lean_object* v_x_1267_){
_start:
{
uint64_t v_a_boxed_1268_; uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_a_boxed_1268_ = lean_unbox_uint64(v_a_1266_);
lean_dec_ref(v_a_1266_);
v_res_1269_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(v_00_u03b2_1265_, v_a_boxed_1268_, v_x_1267_);
lean_dec(v_x_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4(lean_object* v_00_u03b2_1271_, lean_object* v_data_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(v_data_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(lean_object* v_00_u03b2_1274_, uint64_t v_a_1275_, lean_object* v_b_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_1275_, v_b_1276_, v_x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1279_, lean_object* v_a_1280_, lean_object* v_b_1281_, lean_object* v_x_1282_){
_start:
{
uint64_t v_a_boxed_1283_; lean_object* v_res_1284_; 
v_a_boxed_1283_ = lean_unbox_uint64(v_a_1280_);
lean_dec_ref(v_a_1280_);
v_res_1284_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(v_00_u03b2_1279_, v_a_boxed_1283_, v_b_1281_, v_x_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1285_, lean_object* v_i_1286_, lean_object* v_source_1287_, lean_object* v_target_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(v_i_1286_, v_source_1287_, v_target_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1291_, v_x_1292_);
return v___x_1293_;
}
}
lean_object* runtime_initialize_Lean_Util_ShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Canonicalizer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1 = _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1);
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
