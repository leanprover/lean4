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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(187, 6, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1_value;
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
uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
size_t v___x_11_; size_t v___x_12_; uint8_t v___x_13_; 
v___x_11_ = lean_ptr_addr(v_a_9_);
v___x_12_ = lean_ptr_addr(v_b_10_);
v___x_13_ = lean_usize_dec_eq(v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT void l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_9_ = stack[0].m_obj;
lean_object* v_b_10_ = stack[1].m_obj;
uint8_t v_res_14_;
v_res_14_ = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(v_a_9_, v_b_10_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(v_a_15_, v_b_16_);
lean_dec_ref(v_b_16_);
lean_dec_ref(v_a_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(lean_object* v_a_21_){
_start:
{
size_t v___x_22_; uint64_t v___x_23_; 
v___x_22_ = lean_ptr_addr(v_a_21_);
v___x_23_ = lean_usize_to_uint64(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_21_ = stack[0].m_obj;
uint64_t v_res_24_;
v_res_24_ = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(v_a_21_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(lean_object* v_a_25_){
_start:
{
uint64_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(v_a_25_);
lean_dec_ref(v_a_25_);
v_r_27_ = lean_box_uint64(v_res_26_);
return v_r_27_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box(0);
v___x_31_ = lean_unsigned_to_nat(16u);
v___x_32_ = lean_mk_array(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1);
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
v___x_38_ = lean_obj_once(&l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2, &l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2_once, _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2);
return v___x_38_;
}
}
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object* v_x_39_, uint8_t v_transparency_40_, lean_object* v_s_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
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
LEAN_EXPORT void l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_39_ = stack[0].m_obj;
uint8_t v_transparency_40_ = stack[1].m_num;
lean_object* v_s_41_ = stack[2].m_obj;
lean_object* v_a_42_ = stack[3].m_obj;
lean_object* v_a_43_ = stack[4].m_obj;
lean_object* v_a_44_ = stack[5].m_obj;
lean_object* v_a_45_ = stack[6].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v_x_39_, v_transparency_40_, v_s_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object* v_x_60_, lean_object* v_transparency_61_, lean_object* v_s_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
uint8_t v_transparency_boxed_68_; lean_object* v_res_69_; 
v_transparency_boxed_68_ = lean_unbox(v_transparency_61_);
v_res_69_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v_x_60_, v_transparency_boxed_68_, v_s_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_69_;
}
}
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object* v_00_u03b1_70_, lean_object* v_x_71_, uint8_t v_transparency_72_, lean_object* v_s_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v_x_71_, v_transparency_72_, v_s_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Lean_Meta_Canonicalizer_CanonM_run_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_71_ = stack[1].m_obj;
uint8_t v_transparency_72_ = stack[2].m_num;
lean_object* v_s_73_ = stack[3].m_obj;
lean_object* v_a_74_ = stack[4].m_obj;
lean_object* v_a_75_ = stack[5].m_obj;
lean_object* v_a_76_ = stack[6].m_obj;
lean_object* v_a_77_ = stack[7].m_obj;
lean_object* v_res_80_;
v_res_80_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_box(0), v_x_71_, v_transparency_72_, v_s_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object* v_00_u03b1_81_, lean_object* v_x_82_, lean_object* v_transparency_83_, lean_object* v_s_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
uint8_t v_transparency_boxed_90_; lean_object* v_res_91_; 
v_transparency_boxed_90_ = lean_unbox(v_transparency_83_);
v_res_91_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27(v_00_u03b1_81_, v_x_82_, v_transparency_boxed_90_, v_s_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_91_;
}
}
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object* v_x_92_, uint8_t v_transparency_93_, lean_object* v_s_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_st_mk_ref(v_s_94_);
v___x_101_ = lean_box(v_transparency_93_);
lean_inc(v_a_98_);
lean_inc_ref(v_a_97_);
lean_inc(v_a_96_);
lean_inc_ref(v_a_95_);
lean_inc(v___x_100_);
v___x_102_ = lean_apply_7(v_x_92_, v___x_101_, v___x_100_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, lean_box(0));
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_112_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_112_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_112_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_112_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = lean_st_ref_get(v___x_100_);
lean_dec(v___x_100_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_a_103_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_108_);
v___x_110_ = v___x_105_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec(v___x_100_);
v_a_113_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_102_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_102_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Canonicalizer_CanonM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_92_ = stack[0].m_obj;
uint8_t v_transparency_93_ = stack[1].m_num;
lean_object* v_s_94_ = stack[2].m_obj;
lean_object* v_a_95_ = stack[3].m_obj;
lean_object* v_a_96_ = stack[4].m_obj;
lean_object* v_a_97_ = stack[5].m_obj;
lean_object* v_a_98_ = stack[6].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(v_x_92_, v_transparency_93_, v_s_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object* v_x_122_, lean_object* v_transparency_123_, lean_object* v_s_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
uint8_t v_transparency_boxed_130_; lean_object* v_res_131_; 
v_transparency_boxed_130_ = lean_unbox(v_transparency_123_);
v_res_131_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(v_x_122_, v_transparency_boxed_130_, v_s_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
return v_res_131_;
}
}
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object* v_00_u03b1_132_, lean_object* v_x_133_, uint8_t v_transparency_134_, lean_object* v_s_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(v_x_133_, v_transparency_134_, v_s_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
return v___x_141_;
}
}
LEAN_EXPORT void l_Lean_Meta_Canonicalizer_CanonM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_133_ = stack[1].m_obj;
uint8_t v_transparency_134_ = stack[2].m_num;
lean_object* v_s_135_ = stack[3].m_obj;
lean_object* v_a_136_ = stack[4].m_obj;
lean_object* v_a_137_ = stack[5].m_obj;
lean_object* v_a_138_ = stack[6].m_obj;
lean_object* v_a_139_ = stack[7].m_obj;
lean_object* v_res_142_;
v_res_142_ = l_Lean_Meta_Canonicalizer_CanonM_run(lean_box(0), v_x_133_, v_transparency_134_, v_s_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object* v_00_u03b1_143_, lean_object* v_x_144_, lean_object* v_transparency_145_, lean_object* v_s_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
uint8_t v_transparency_boxed_152_; lean_object* v_res_153_; 
v_transparency_boxed_152_ = lean_unbox(v_transparency_145_);
v_res_153_ = l_Lean_Meta_Canonicalizer_CanonM_run(v_00_u03b1_143_, v_x_144_, v_transparency_boxed_152_, v_s_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object* v_e_154_, lean_object* v_____do__lift_155_){
_start:
{
lean_object* v_cache_156_; lean_object* v_buckets_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_cache_156_ = lean_ctor_get(v_____do__lift_155_, 0);
v_buckets_157_ = lean_ctor_get(v_cache_156_, 1);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_array_get_size(v_buckets_157_);
v___x_160_ = lean_nat_dec_lt(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v_e_154_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_164_; 
v___f_162_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_163_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_162_, v___f_163_, v_cache_156_, v_e_154_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object* v_e_165_, lean_object* v_____do__lift_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(v_e_165_, v_____do__lift_166_);
lean_dec_ref(v_____do__lift_166_);
return v_res_167_;
}
}
lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object* v_e_168_, uint64_t v_key_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v_cache_180_; lean_object* v_keyToExprs_181_; lean_object* v_buckets_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___f_172_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_173_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_174_ = lean_st_ref_take(v_a_170_);
v_cache_180_ = lean_ctor_get(v___x_174_, 0);
v_keyToExprs_181_ = lean_ctor_get(v___x_174_, 1);
v_buckets_182_ = lean_ctor_get(v_cache_180_, 1);
v___x_183_ = lean_box(0);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_array_get_size(v_buckets_182_);
v___x_186_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_dec_ref(v_e_168_);
v_fst_176_ = v___x_183_;
v_snd_177_ = v___x_174_;
goto v___jp_175_;
}
else
{
lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
lean_inc_ref(v_keyToExprs_181_);
lean_inc_ref(v_cache_180_);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; lean_object* v_unused_197_; 
v_unused_196_ = lean_ctor_get(v___x_174_, 1);
lean_dec(v_unused_196_);
v_unused_197_ = lean_ctor_get(v___x_174_, 0);
lean_dec(v_unused_197_);
v___x_188_ = v___x_174_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_dec(v___x_174_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_box_uint64(v_key_169_);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_172_, v___f_173_, v_cache_180_, v_e_168_, v___x_190_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_191_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_keyToExprs_181_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
v_fst_176_ = v___x_183_;
v_snd_177_ = v___x_193_;
goto v___jp_175_;
}
}
}
v___jp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_st_ref_put(v_a_170_, v_snd_177_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v_fst_176_);
return v___x_179_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_168_ = stack[0].m_obj;
uint64_t v_key_169_ = stack[1].m_num;
lean_object* v_a_170_ = stack[2].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_168_, v_key_169_, v_a_170_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object* v_e_199_, lean_object* v_key_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
uint64_t v_key_boxed_203_; lean_object* v_res_204_; 
v_key_boxed_203_ = lean_unbox_uint64(v_key_200_);
lean_dec_ref(v_key_200_);
v_res_204_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_199_, v_key_boxed_203_, v_a_201_);
lean_dec(v_a_201_);
return v_res_204_;
}
}
lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object* v_e_205_, uint64_t v_key_206_, uint8_t v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v_fst_218_; lean_object* v_snd_219_; lean_object* v_cache_222_; lean_object* v_keyToExprs_223_; lean_object* v_buckets_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___f_214_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_215_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_216_ = lean_st_ref_take(v_a_208_);
v_cache_222_ = lean_ctor_get(v___x_216_, 0);
v_keyToExprs_223_ = lean_ctor_get(v___x_216_, 1);
v_buckets_224_ = lean_ctor_get(v_cache_222_, 1);
v___x_225_ = lean_box(0);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_array_get_size(v_buckets_224_);
v___x_228_ = lean_nat_dec_lt(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec_ref(v_e_205_);
v_fst_218_ = v___x_225_;
v_snd_219_ = v___x_216_;
goto v___jp_217_;
}
else
{
lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_237_; 
lean_inc_ref(v_keyToExprs_223_);
lean_inc_ref(v_cache_222_);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; lean_object* v_unused_239_; 
v_unused_238_ = lean_ctor_get(v___x_216_, 1);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v___x_216_, 0);
lean_dec(v_unused_239_);
v___x_230_ = v___x_216_;
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
else
{
lean_dec(v___x_216_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_box_uint64(v_key_206_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_214_, v___f_215_, v_cache_222_, v_e_205_, v___x_232_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_keyToExprs_223_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v_fst_218_ = v___x_225_;
v_snd_219_ = v___x_235_;
goto v___jp_217_;
}
}
}
v___jp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_st_ref_put(v_a_208_, v_snd_219_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_fst_218_);
return v___x_221_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_205_ = stack[0].m_obj;
uint64_t v_key_206_ = stack[1].m_num;
uint8_t v_a_207_ = stack[2].m_num;
lean_object* v_a_208_ = stack[3].m_obj;
lean_object* v_a_209_ = stack[4].m_obj;
lean_object* v_a_210_ = stack[5].m_obj;
lean_object* v_a_211_ = stack[6].m_obj;
lean_object* v_a_212_ = stack[7].m_obj;
lean_object* v_res_240_;
v_res_240_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(v_e_205_, v_key_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object* v_e_241_, lean_object* v_key_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
uint64_t v_key_boxed_250_; uint8_t v_a_boxed_251_; lean_object* v_res_252_; 
v_key_boxed_250_ = lean_unbox_uint64(v_key_242_);
lean_dec_ref(v_key_242_);
v_a_boxed_251_ = lean_unbox(v_a_243_);
v_res_252_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(v_e_241_, v_key_boxed_250_, v_a_boxed_251_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
return v_res_252_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object* v_e_253_, lean_object* v___y_254_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = l_Lean_Expr_hasMVar(v_e_253_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_e_253_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v_mctx_259_; lean_object* v___x_260_; lean_object* v_fst_261_; lean_object* v_snd_262_; lean_object* v___x_263_; lean_object* v_cache_264_; lean_object* v_zetaDeltaFVarIds_265_; lean_object* v_postponed_266_; lean_object* v_diag_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_276_; 
v___x_258_ = lean_st_ref_get(v___y_254_);
v_mctx_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_mctx_259_);
lean_dec(v___x_258_);
v___x_260_ = l_Lean_instantiateMVarsCore(v_mctx_259_, v_e_253_);
v_fst_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_fst_261_);
v_snd_262_ = lean_ctor_get(v___x_260_, 1);
lean_inc(v_snd_262_);
lean_dec_ref(v___x_260_);
v___x_263_ = lean_st_ref_take(v___y_254_);
v_cache_264_ = lean_ctor_get(v___x_263_, 1);
v_zetaDeltaFVarIds_265_ = lean_ctor_get(v___x_263_, 2);
v_postponed_266_ = lean_ctor_get(v___x_263_, 3);
v_diag_267_ = lean_ctor_get(v___x_263_, 4);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_277_);
v___x_269_ = v___x_263_;
v_isShared_270_ = v_isSharedCheck_276_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_diag_267_);
lean_inc(v_postponed_266_);
lean_inc(v_zetaDeltaFVarIds_265_);
lean_inc(v_cache_264_);
lean_dec(v___x_263_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_276_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v_snd_262_);
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_snd_262_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_cache_264_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_zetaDeltaFVarIds_265_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_postponed_266_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_diag_267_);
v___x_272_ = v_reuseFailAlloc_275_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_st_ref_put(v___y_254_, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_fst_261_);
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_253_ = stack[0].m_obj;
lean_object* v___y_254_ = stack[1].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_253_, v___y_254_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object* v_e_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_279_, v___y_280_);
lean_dec(v___y_280_);
return v_res_282_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object* v_e_283_, uint8_t v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_283_, v___y_287_);
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_283_ = stack[0].m_obj;
uint8_t v___y_284_ = stack[1].m_num;
lean_object* v___y_285_ = stack[2].m_obj;
lean_object* v___y_286_ = stack[3].m_obj;
lean_object* v___y_287_ = stack[4].m_obj;
lean_object* v___y_288_ = stack[5].m_obj;
lean_object* v___y_289_ = stack[6].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v_e_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object* v_e_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___y_13562__boxed_301_; lean_object* v_res_302_; 
v___y_13562__boxed_301_ = lean_unbox(v___y_294_);
v_res_302_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v_e_293_, v___y_13562__boxed_301_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(lean_object* v_a_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_box(0);
return v___x_305_;
}
else
{
lean_object* v_key_306_; lean_object* v_value_307_; lean_object* v_tail_308_; size_t v___x_309_; size_t v___x_310_; uint8_t v___x_311_; 
v_key_306_ = lean_ctor_get(v_x_304_, 0);
v_value_307_ = lean_ctor_get(v_x_304_, 1);
v_tail_308_ = lean_ctor_get(v_x_304_, 2);
v___x_309_ = lean_ptr_addr(v_key_306_);
v___x_310_ = lean_ptr_addr(v_a_303_);
v___x_311_ = lean_usize_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
v_x_304_ = v_tail_308_;
goto _start;
}
else
{
lean_object* v___x_313_; 
lean_inc(v_value_307_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_value_307_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg___boxed(lean_object* v_a_314_, lean_object* v_x_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(v_a_314_, v_x_315_);
lean_dec(v_x_315_);
lean_dec_ref(v_a_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(lean_object* v_m_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_buckets_319_; lean_object* v___x_320_; size_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v_fold_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_buckets_319_ = lean_ctor_get(v_m_317_, 1);
v___x_320_ = lean_array_get_size(v_buckets_319_);
v___x_321_ = lean_ptr_addr(v_a_318_);
v___x_322_ = lean_usize_to_uint64(v___x_321_);
v___x_323_ = 32ULL;
v___x_324_ = lean_uint64_shift_right(v___x_322_, v___x_323_);
v_fold_325_ = lean_uint64_xor(v___x_322_, v___x_324_);
v___x_326_ = 16ULL;
v___x_327_ = lean_uint64_shift_right(v_fold_325_, v___x_326_);
v___x_328_ = lean_uint64_xor(v_fold_325_, v___x_327_);
v___x_329_ = lean_uint64_to_usize(v___x_328_);
v___x_330_ = lean_usize_of_nat(v___x_320_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_sub(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_land(v___x_329_, v___x_332_);
v___x_334_ = lean_array_uget_borrowed(v_buckets_319_, v___x_333_);
v___x_335_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(v_a_318_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg___boxed(lean_object* v_m_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_m_336_, v_a_337_);
lean_dec_ref(v_a_337_);
lean_dec_ref(v_m_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
return v_x_339_;
}
else
{
lean_object* v_key_341_; lean_object* v_value_342_; lean_object* v_tail_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_367_; 
v_key_341_ = lean_ctor_get(v_x_340_, 0);
v_value_342_ = lean_ctor_get(v_x_340_, 1);
v_tail_343_ = lean_ctor_get(v_x_340_, 2);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_367_ == 0)
{
v___x_345_ = v_x_340_;
v_isShared_346_ = v_isSharedCheck_367_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_tail_343_);
lean_inc(v_value_342_);
lean_inc(v_key_341_);
lean_dec(v_x_340_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_367_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; size_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; uint64_t v_fold_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_347_ = lean_array_get_size(v_x_339_);
v___x_348_ = lean_ptr_addr(v_key_341_);
v___x_349_ = lean_usize_to_uint64(v___x_348_);
v___x_350_ = 32ULL;
v___x_351_ = lean_uint64_shift_right(v___x_349_, v___x_350_);
v_fold_352_ = lean_uint64_xor(v___x_349_, v___x_351_);
v___x_353_ = 16ULL;
v___x_354_ = lean_uint64_shift_right(v_fold_352_, v___x_353_);
v___x_355_ = lean_uint64_xor(v_fold_352_, v___x_354_);
v___x_356_ = lean_uint64_to_usize(v___x_355_);
v___x_357_ = lean_usize_of_nat(v___x_347_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_sub(v___x_357_, v___x_358_);
v___x_360_ = lean_usize_land(v___x_356_, v___x_359_);
v___x_361_ = lean_array_uget_borrowed(v_x_339_, v___x_360_);
lean_inc(v___x_361_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 2, v___x_361_);
v___x_363_ = v___x_345_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_key_341_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_value_342_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v___x_361_);
v___x_363_ = v_reuseFailAlloc_366_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = lean_array_uset(v_x_339_, v___x_360_, v___x_363_);
v_x_339_ = v___x_364_;
v_x_340_ = v_tail_343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(lean_object* v_i_368_, lean_object* v_source_369_, lean_object* v_target_370_){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_array_get_size(v_source_369_);
v___x_372_ = lean_nat_dec_lt(v_i_368_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec_ref(v_source_369_);
lean_dec(v_i_368_);
return v_target_370_;
}
else
{
lean_object* v_es_373_; lean_object* v___x_374_; lean_object* v_source_375_; lean_object* v_target_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_es_373_ = lean_array_fget(v_source_369_, v_i_368_);
v___x_374_ = lean_box(0);
v_source_375_ = lean_array_fset(v_source_369_, v_i_368_, v___x_374_);
v_target_376_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(v_target_370_, v_es_373_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_i_368_, v___x_377_);
lean_dec(v_i_368_);
v_i_368_ = v___x_378_;
v_source_369_ = v_source_375_;
v_target_370_ = v_target_376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(lean_object* v_data_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_nbuckets_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_381_ = lean_array_get_size(v_data_380_);
v___x_382_ = lean_unsigned_to_nat(2u);
v_nbuckets_383_ = lean_nat_mul(v___x_381_, v___x_382_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_box(0);
v___x_386_ = lean_mk_array(v_nbuckets_383_, v___x_385_);
v___x_387_ = lean_array_propagate_mark(v_data_380_, v___x_386_);
v___x_388_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(v___x_384_, v_data_380_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(lean_object* v_a_389_, lean_object* v_b_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_dec(v_b_390_);
lean_dec_ref(v_a_389_);
return v_x_391_;
}
else
{
lean_object* v_key_392_; lean_object* v_value_393_; lean_object* v_tail_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_408_; 
v_key_392_ = lean_ctor_get(v_x_391_, 0);
v_value_393_ = lean_ctor_get(v_x_391_, 1);
v_tail_394_ = lean_ctor_get(v_x_391_, 2);
v_isSharedCheck_408_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_408_ == 0)
{
v___x_396_ = v_x_391_;
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_tail_394_);
lean_inc(v_value_393_);
lean_inc(v_key_392_);
lean_dec(v_x_391_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
size_t v___x_398_; size_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_ptr_addr(v_key_392_);
v___x_399_ = lean_ptr_addr(v_a_389_);
v___x_400_ = lean_usize_dec_eq(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_389_, v_b_390_, v_tail_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 2, v___x_401_);
v___x_403_ = v___x_396_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_key_392_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_value_393_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
lean_object* v___x_406_; 
lean_dec(v_value_393_);
lean_dec(v_key_392_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v_b_390_);
lean_ctor_set(v___x_396_, 0, v_a_389_);
v___x_406_ = v___x_396_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_389_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_b_390_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_tail_394_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
else
{
lean_object* v_key_412_; lean_object* v_tail_413_; size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v_key_412_ = lean_ctor_get(v_x_410_, 0);
v_tail_413_ = lean_ctor_get(v_x_410_, 2);
v___x_414_ = lean_ptr_addr(v_key_412_);
v___x_415_ = lean_ptr_addr(v_a_409_);
v___x_416_ = lean_usize_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
v_x_410_ = v_tail_413_;
goto _start;
}
else
{
return v___x_416_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_409_ = stack[0].m_obj;
lean_object* v_x_410_ = stack[1].m_obj;
uint8_t v_res_418_;
v_res_418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_409_, v_x_410_);
stack->m_num = v_res_418_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg___boxed(lean_object* v_a_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_419_, v_x_420_);
lean_dec(v_x_420_);
lean_dec_ref(v_a_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object* v_m_423_, lean_object* v_a_424_, lean_object* v_b_425_){
_start:
{
lean_object* v_size_426_; lean_object* v_buckets_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_471_; 
v_size_426_ = lean_ctor_get(v_m_423_, 0);
v_buckets_427_ = lean_ctor_get(v_m_423_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_m_423_);
if (v_isSharedCheck_471_ == 0)
{
v___x_429_ = v_m_423_;
v_isShared_430_ = v_isSharedCheck_471_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_buckets_427_);
lean_inc(v_size_426_);
lean_dec(v_m_423_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_471_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; size_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v_fold_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v_bkt_445_; uint8_t v___x_446_; 
v___x_431_ = lean_array_get_size(v_buckets_427_);
v___x_432_ = lean_ptr_addr(v_a_424_);
v___x_433_ = lean_usize_to_uint64(v___x_432_);
v___x_434_ = 32ULL;
v___x_435_ = lean_uint64_shift_right(v___x_433_, v___x_434_);
v_fold_436_ = lean_uint64_xor(v___x_433_, v___x_435_);
v___x_437_ = 16ULL;
v___x_438_ = lean_uint64_shift_right(v_fold_436_, v___x_437_);
v___x_439_ = lean_uint64_xor(v_fold_436_, v___x_438_);
v___x_440_ = lean_uint64_to_usize(v___x_439_);
v___x_441_ = lean_usize_of_nat(v___x_431_);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_sub(v___x_441_, v___x_442_);
v___x_444_ = lean_usize_land(v___x_440_, v___x_443_);
v_bkt_445_ = lean_array_uget_borrowed(v_buckets_427_, v___x_444_);
v___x_446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_424_, v_bkt_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v_size_x27_448_; lean_object* v___x_449_; lean_object* v_buckets_x27_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_447_ = lean_unsigned_to_nat(1u);
v_size_x27_448_ = lean_nat_add(v_size_426_, v___x_447_);
lean_dec(v_size_426_);
lean_inc(v_bkt_445_);
v___x_449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_449_, 0, v_a_424_);
lean_ctor_set(v___x_449_, 1, v_b_425_);
lean_ctor_set(v___x_449_, 2, v_bkt_445_);
v_buckets_x27_450_ = lean_array_uset(v_buckets_427_, v___x_444_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(4u);
v___x_452_ = lean_nat_mul(v_size_x27_448_, v___x_451_);
v___x_453_ = lean_unsigned_to_nat(3u);
v___x_454_ = lean_nat_div(v___x_452_, v___x_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_array_get_size(v_buckets_x27_450_);
v___x_456_ = lean_nat_dec_le(v___x_454_, v___x_455_);
lean_dec(v___x_454_);
if (v___x_456_ == 0)
{
lean_object* v_val_457_; lean_object* v___x_459_; 
v_val_457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(v_buckets_x27_450_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_val_457_);
lean_ctor_set(v___x_429_, 0, v_size_x27_448_);
v___x_459_ = v___x_429_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_size_x27_448_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_val_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
lean_object* v___x_462_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_buckets_x27_450_);
lean_ctor_set(v___x_429_, 0, v_size_x27_448_);
v___x_462_ = v___x_429_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_size_x27_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_buckets_x27_450_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v___x_464_; lean_object* v_buckets_x27_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
lean_inc(v_bkt_445_);
v___x_464_ = lean_box(0);
v_buckets_x27_465_ = lean_array_uset(v_buckets_427_, v___x_444_, v___x_464_);
v___x_466_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_424_, v_b_425_, v_bkt_445_);
v___x_467_ = lean_array_uset(v_buckets_x27_465_, v___x_444_, v___x_466_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_467_);
v___x_469_ = v___x_429_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_size_426_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* v_e_478_, uint8_t v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_t_487_; lean_object* v_b_488_; uint8_t v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; uint64_t v___y_511_; lean_object* v___y_512_; lean_object* v_snd_513_; uint64_t v_key_518_; lean_object* v___y_519_; lean_object* v___y_539_; lean_object* v_info_540_; uint8_t v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_554_; uint8_t v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___x_574_; lean_object* v_cache_662_; lean_object* v_buckets_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_574_ = lean_st_ref_get(v_a_480_);
v_cache_662_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_cache_662_);
lean_dec(v___x_574_);
v_buckets_663_ = lean_ctor_get(v_cache_662_, 1);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_array_get_size(v_buckets_663_);
v___x_666_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec_ref(v_cache_662_);
goto v___jp_575_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_cache_662_, v_e_478_);
lean_dec_ref(v_cache_662_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_e_478_);
v_val_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_val_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 0);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_val_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_dec(v___x_667_);
goto v___jp_575_;
}
}
v___jp_486_:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_t_487_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_b_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_509_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_509_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_502_ = lean_unbox_uint64(v_a_496_);
lean_dec(v_a_496_);
v___x_503_ = lean_unbox_uint64(v_a_498_);
lean_dec(v_a_498_);
v___x_504_ = lean_uint64_mix_hash(v___x_502_, v___x_503_);
v___x_505_ = lean_box_uint64(v___x_504_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_505_);
v___x_507_ = v___x_500_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_dec(v_a_496_);
return v___x_497_;
}
}
else
{
lean_dec_ref(v_b_488_);
return v___x_495_;
}
}
v___jp_510_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_st_ref_put(v___y_512_, v_snd_513_);
v___x_515_ = lean_box_uint64(v___y_511_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
v___jp_517_:
{
lean_object* v___x_520_; lean_object* v_cache_521_; lean_object* v_keyToExprs_522_; lean_object* v_buckets_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_520_ = lean_st_ref_take(v___y_519_);
v_cache_521_ = lean_ctor_get(v___x_520_, 0);
v_keyToExprs_522_ = lean_ctor_get(v___x_520_, 1);
v_buckets_523_ = lean_ctor_get(v_cache_521_, 1);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_array_get_size(v_buckets_523_);
v___x_526_ = lean_nat_dec_lt(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v_e_478_);
v___y_511_ = v_key_518_;
v___y_512_ = v___y_519_;
v_snd_513_ = v___x_520_;
goto v___jp_510_;
}
else
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_535_; 
lean_inc_ref(v_keyToExprs_522_);
lean_inc_ref(v_cache_521_);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; 
v_unused_536_ = lean_ctor_get(v___x_520_, 1);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v___x_520_, 0);
lean_dec(v_unused_537_);
v___x_528_ = v___x_520_;
v_isShared_529_ = v_isSharedCheck_535_;
goto v_resetjp_527_;
}
else
{
lean_dec(v___x_520_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_535_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_530_ = lean_box_uint64(v_key_518_);
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_cache_521_, v_e_478_, v___x_530_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_531_);
v___x_533_ = v___x_528_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_keyToExprs_522_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v___y_511_ = v_key_518_;
v___y_512_ = v___y_519_;
v_snd_513_ = v___x_533_;
goto v___jp_510_;
}
}
}
}
v___jp_538_:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___y_539_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint64_t v___x_551_; lean_object* v___x_552_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = l_Lean_Expr_getAppNumArgs(v_e_478_);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_unbox_uint64(v_a_548_);
lean_dec(v_a_548_);
v___x_552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_549_, v_e_478_, v___x_549_, v_info_540_, v___x_550_, v___x_551_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec_ref(v_info_540_);
lean_dec_ref(v_e_478_);
lean_dec(v___x_549_);
return v___x_552_;
}
else
{
lean_dec_ref(v_info_540_);
lean_dec_ref(v_e_478_);
return v___x_547_;
}
}
v___jp_553_:
{
uint8_t v___x_561_; 
v___x_561_ = l_Lean_Expr_hasLooseBVars(v___y_554_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
lean_inc_ref(v___y_554_);
v___x_563_ = l_Lean_Meta_getFunInfo(v___y_554_, v___x_562_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___y_539_ = v___y_554_;
v_info_540_ = v_a_564_;
v___y_541_ = v___y_555_;
v___y_542_ = v___y_556_;
v___y_543_ = v___y_557_;
v___y_544_ = v___y_558_;
v___y_545_ = v___y_559_;
v___y_546_ = v___y_560_;
goto v___jp_538_;
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref(v___y_554_);
lean_dec_ref(v_e_478_);
v_a_565_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_563_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1));
v___y_539_ = v___y_554_;
v_info_540_ = v___x_573_;
v___y_541_ = v___y_555_;
v___y_542_ = v___y_556_;
v___y_543_ = v___y_557_;
v___y_544_ = v___y_558_;
v___y_545_ = v___y_559_;
v___y_546_ = v___y_560_;
goto v___jp_538_;
}
}
v___jp_575_:
{
switch(lean_obj_tag(v_e_478_))
{
case 2:
{
lean_object* v___x_576_; 
lean_inc_ref(v_e_478_);
v___x_576_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_478_, v_a_482_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_590_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_590_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
uint8_t v___x_581_; 
v___x_581_ = lean_expr_eqv(v_a_577_, v_e_478_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_del_object(v___x_579_);
v___x_582_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_a_577_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; uint64_t v___x_584_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = lean_unbox_uint64(v_a_583_);
lean_dec(v_a_583_);
v_key_518_ = v___x_584_;
v___y_519_ = v_a_480_;
goto v___jp_517_;
}
else
{
lean_dec_ref_known(v_e_478_, 1);
return v___x_582_;
}
}
else
{
uint64_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec(v_a_577_);
v___x_585_ = l_Lean_Expr_hash(v_e_478_);
lean_dec_ref_known(v_e_478_, 1);
v___x_586_ = lean_box_uint64(v___x_585_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_586_);
v___x_588_ = v___x_579_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref_known(v_e_478_, 1);
v_a_591_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_576_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_576_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
case 4:
{
lean_object* v_declName_599_; 
v_declName_599_ = lean_ctor_get(v_e_478_, 0);
lean_inc(v_declName_599_);
lean_dec_ref_known(v_e_478_, 2);
if (lean_obj_tag(v_declName_599_) == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1));
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
else
{
uint64_t v_hash_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_hash_602_ = lean_ctor_get_uint64(v_declName_599_, sizeof(void*)*2);
lean_dec(v_declName_599_);
v___x_603_ = lean_box_uint64(v_hash_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
case 5:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = l_Lean_Expr_getAppFn(v_e_478_);
v___x_606_ = l_Lean_Expr_isMVar(v___x_605_);
if (v___x_606_ == 0)
{
v___y_554_ = v___x_605_;
v___y_555_ = v_a_479_;
v___y_556_ = v_a_480_;
v___y_557_ = v_a_481_;
v___y_558_ = v_a_482_;
v___y_559_ = v_a_483_;
v___y_560_ = v_a_484_;
goto v___jp_553_;
}
else
{
lean_object* v___x_607_; 
lean_inc_ref(v_e_478_);
v___x_607_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_478_, v_a_482_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; uint8_t v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = lean_expr_eqv(v_a_608_, v_e_478_);
if (v___x_609_ == 0)
{
lean_dec_ref_known(v_e_478_, 2);
lean_dec_ref(v___x_605_);
v_e_478_ = v_a_608_;
goto _start;
}
else
{
lean_dec(v_a_608_);
v___y_554_ = v___x_605_;
v___y_555_ = v_a_479_;
v___y_556_ = v_a_480_;
v___y_557_ = v_a_481_;
v___y_558_ = v_a_482_;
v___y_559_ = v_a_483_;
v___y_560_ = v_a_484_;
goto v___jp_553_;
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref_known(v_e_478_, 2);
lean_dec_ref(v___x_605_);
v_a_611_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_607_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_619_; lean_object* v_body_620_; 
v_binderType_619_ = lean_ctor_get(v_e_478_, 1);
lean_inc_ref(v_binderType_619_);
v_body_620_ = lean_ctor_get(v_e_478_, 2);
lean_inc_ref(v_body_620_);
lean_dec_ref_known(v_e_478_, 3);
v_t_487_ = v_binderType_619_;
v_b_488_ = v_body_620_;
v___y_489_ = v_a_479_;
v___y_490_ = v_a_480_;
v___y_491_ = v_a_481_;
v___y_492_ = v_a_482_;
v___y_493_ = v_a_483_;
v___y_494_ = v_a_484_;
goto v___jp_486_;
}
case 7:
{
lean_object* v_binderType_621_; lean_object* v_body_622_; 
v_binderType_621_ = lean_ctor_get(v_e_478_, 1);
lean_inc_ref(v_binderType_621_);
v_body_622_ = lean_ctor_get(v_e_478_, 2);
lean_inc_ref(v_body_622_);
lean_dec_ref_known(v_e_478_, 3);
v_t_487_ = v_binderType_621_;
v_b_488_ = v_body_622_;
v___y_489_ = v_a_479_;
v___y_490_ = v_a_480_;
v___y_491_ = v_a_481_;
v___y_492_ = v_a_482_;
v___y_493_ = v_a_483_;
v___y_494_ = v_a_484_;
goto v___jp_486_;
}
case 8:
{
lean_object* v_value_623_; lean_object* v_body_624_; lean_object* v___x_625_; 
v_value_623_ = lean_ctor_get(v_e_478_, 2);
lean_inc_ref(v_value_623_);
v_body_624_ = lean_ctor_get(v_e_478_, 3);
lean_inc_ref(v_body_624_);
lean_dec_ref_known(v_e_478_, 4);
v___x_625_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_623_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_624_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_639_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_639_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_639_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_639_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_632_ = lean_unbox_uint64(v_a_626_);
lean_dec(v_a_626_);
v___x_633_ = lean_unbox_uint64(v_a_628_);
lean_dec(v_a_628_);
v___x_634_ = lean_uint64_mix_hash(v___x_632_, v___x_633_);
v___x_635_ = lean_box_uint64(v___x_634_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_635_);
v___x_637_ = v___x_630_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_dec(v_a_626_);
return v___x_627_;
}
}
else
{
lean_dec_ref(v_body_624_);
return v___x_625_;
}
}
case 10:
{
lean_object* v_expr_640_; lean_object* v___x_641_; 
v_expr_640_ = lean_ctor_get(v_e_478_, 1);
lean_inc_ref(v_expr_640_);
v___x_641_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_640_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; uint64_t v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = lean_unbox_uint64(v_a_642_);
lean_dec(v_a_642_);
v_key_518_ = v___x_643_;
v___y_519_ = v_a_480_;
goto v___jp_517_;
}
else
{
lean_dec_ref_known(v_e_478_, 2);
return v___x_641_;
}
}
case 11:
{
lean_object* v_idx_644_; lean_object* v_struct_645_; lean_object* v___x_646_; 
v_idx_644_ = lean_ctor_get(v_e_478_, 1);
lean_inc(v_idx_644_);
v_struct_645_ = lean_ctor_get(v_e_478_, 2);
lean_inc_ref(v_struct_645_);
lean_dec_ref_known(v_e_478_, 3);
v___x_646_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_645_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_658_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_658_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint64_t v___x_651_; uint64_t v___x_652_; uint64_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_651_ = lean_uint64_of_nat(v_idx_644_);
lean_dec(v_idx_644_);
v___x_652_ = lean_unbox_uint64(v_a_647_);
lean_dec(v_a_647_);
v___x_653_ = lean_uint64_mix_hash(v___x_651_, v___x_652_);
v___x_654_ = lean_box_uint64(v___x_653_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_654_);
v___x_656_ = v___x_649_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
else
{
lean_dec(v_idx_644_);
return v___x_646_;
}
}
default: 
{
uint64_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = l_Lean_Expr_hash(v_e_478_);
lean_dec_ref(v_e_478_);
v___x_660_ = lean_box_uint64(v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_478_ = stack[0].m_obj;
uint8_t v_a_479_ = stack[1].m_num;
lean_object* v_a_480_ = stack[2].m_obj;
lean_object* v_a_481_ = stack[3].m_obj;
lean_object* v_a_482_ = stack[4].m_obj;
lean_object* v_a_483_ = stack[5].m_obj;
lean_object* v_a_484_ = stack[6].m_obj;
lean_object* v_res_676_;
v_res_676_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
stack->m_obj
 = v_res_676_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(lean_object* v___x_677_, lean_object* v_e_678_, lean_object* v_upperBound_679_, lean_object* v_info_680_, lean_object* v_a_681_, uint64_t v_b_682_, uint8_t v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint64_t v_a_691_; uint8_t v___x_704_; 
v___x_704_ = lean_nat_dec_lt(v_a_681_, v_upperBound_679_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v_a_681_);
v___x_705_ = lean_box_uint64(v_b_682_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v_paramInfo_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_paramInfo_707_ = lean_ctor_get(v_info_680_, 0);
v___x_708_ = lean_array_get_size(v_paramInfo_707_);
v___x_709_ = lean_nat_dec_lt(v_a_681_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_710_ = lean_nat_sub(v___x_677_, v_a_681_);
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_sub(v___x_710_, v___x_711_);
lean_dec(v___x_710_);
v___x_713_ = l_Lean_Expr_getRevArg_x21(v_e_678_, v___x_712_);
v___x_714_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_713_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; uint64_t v___x_716_; uint64_t v___x_717_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_unbox_uint64(v_a_715_);
lean_dec(v_a_715_);
v___x_717_ = lean_uint64_mix_hash(v_b_682_, v___x_716_);
v_a_691_ = v___x_717_;
goto v___jp_690_;
}
else
{
lean_dec(v_a_681_);
return v___x_714_;
}
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_array_fget_borrowed(v_paramInfo_707_, v_a_681_);
v___x_719_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_718_);
if (v___x_719_ == 0)
{
if (v___x_719_ == 0)
{
v_a_691_ = v_b_682_;
goto v___jp_690_;
}
else
{
goto v___jp_695_;
}
}
else
{
uint8_t v_isProp_720_; 
v_isProp_720_ = lean_ctor_get_uint8(v___x_718_, sizeof(void*)*1 + 2);
if (v_isProp_720_ == 0)
{
goto v___jp_695_;
}
else
{
v_a_691_ = v_b_682_;
goto v___jp_690_;
}
}
}
}
v___jp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_a_681_, v___x_692_);
lean_dec(v_a_681_);
v_a_681_ = v___x_693_;
v_b_682_ = v_a_691_;
goto _start;
}
v___jp_695_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_696_ = lean_nat_sub(v___x_677_, v_a_681_);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_sub(v___x_696_, v___x_697_);
lean_dec(v___x_696_);
v___x_699_ = l_Lean_Expr_getRevArg_x21(v_e_678_, v___x_698_);
v___x_700_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_699_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; uint64_t v___x_702_; uint64_t v___x_703_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_unbox_uint64(v_a_701_);
lean_dec(v_a_701_);
v___x_703_ = lean_uint64_mix_hash(v_b_682_, v___x_702_);
v_a_691_ = v___x_703_;
goto v___jp_690_;
}
else
{
lean_dec(v_a_681_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_677_ = stack[0].m_obj;
lean_object* v_e_678_ = stack[1].m_obj;
lean_object* v_upperBound_679_ = stack[2].m_obj;
lean_object* v_info_680_ = stack[3].m_obj;
lean_object* v_a_681_ = stack[4].m_obj;
uint64_t v_b_682_ = stack[5].m_num;
uint8_t v___y_683_ = stack[6].m_num;
lean_object* v___y_684_ = stack[7].m_obj;
lean_object* v___y_685_ = stack[8].m_obj;
lean_object* v___y_686_ = stack[9].m_obj;
lean_object* v___y_687_ = stack[10].m_obj;
lean_object* v___y_688_ = stack[11].m_obj;
lean_object* v_res_721_;
v_res_721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_677_, v_e_678_, v_upperBound_679_, v_info_680_, v_a_681_, v_b_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
stack->m_obj
 = v_res_721_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg___boxed(lean_object* v___x_722_, lean_object* v_e_723_, lean_object* v_upperBound_724_, lean_object* v_info_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
uint64_t v_b_boxed_735_; uint8_t v___y_14015__boxed_736_; lean_object* v_res_737_; 
v_b_boxed_735_ = lean_unbox_uint64(v_b_727_);
lean_dec_ref(v_b_727_);
v___y_14015__boxed_736_ = lean_unbox(v___y_728_);
v_res_737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_722_, v_e_723_, v_upperBound_724_, v_info_725_, v_a_726_, v_b_boxed_735_, v___y_14015__boxed_736_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v_info_725_);
lean_dec(v_upperBound_724_);
lean_dec_ref(v_e_723_);
lean_dec(v___x_722_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* v_e_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
uint8_t v_a_boxed_746_; lean_object* v_res_747_; 
v_a_boxed_746_ = lean_unbox(v_a_739_);
v_res_747_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_738_, v_a_boxed_746_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* v_00_u03b2_748_, lean_object* v_m_749_, lean_object* v_a_750_, lean_object* v_b_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_m_749_, v_a_750_, v_b_751_);
return v___x_752_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(lean_object* v___x_753_, lean_object* v_e_754_, lean_object* v_upperBound_755_, lean_object* v_info_756_, lean_object* v_inst_757_, lean_object* v_R_758_, lean_object* v_a_759_, uint64_t v_b_760_, lean_object* v_c_761_, uint8_t v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_753_, v_e_754_, v_upperBound_755_, v_info_756_, v_a_759_, v_b_760_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
return v___x_769_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_753_ = stack[0].m_obj;
lean_object* v_e_754_ = stack[1].m_obj;
lean_object* v_upperBound_755_ = stack[2].m_obj;
lean_object* v_info_756_ = stack[3].m_obj;
lean_object* v_a_759_ = stack[6].m_obj;
uint64_t v_b_760_ = stack[7].m_num;
uint8_t v___y_762_ = stack[9].m_num;
lean_object* v___y_763_ = stack[10].m_obj;
lean_object* v___y_764_ = stack[11].m_obj;
lean_object* v___y_765_ = stack[12].m_obj;
lean_object* v___y_766_ = stack[13].m_obj;
lean_object* v___y_767_ = stack[14].m_obj;
lean_object* v_res_770_;
v_res_770_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(v___x_753_, v_e_754_, v_upperBound_755_, v_info_756_, lean_box(0), lean_box(0), v_a_759_, v_b_760_, lean_box(0), v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___boxed(lean_object* v___x_771_, lean_object* v_e_772_, lean_object* v_upperBound_773_, lean_object* v_info_774_, lean_object* v_inst_775_, lean_object* v_R_776_, lean_object* v_a_777_, lean_object* v_b_778_, lean_object* v_c_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint64_t v_b_boxed_787_; uint8_t v___y_14745__boxed_788_; lean_object* v_res_789_; 
v_b_boxed_787_ = lean_unbox_uint64(v_b_778_);
lean_dec_ref(v_b_778_);
v___y_14745__boxed_788_ = lean_unbox(v___y_780_);
v_res_789_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(v___x_771_, v_e_772_, v_upperBound_773_, v_info_774_, v_inst_775_, v_R_776_, v_a_777_, v_b_boxed_787_, v_c_779_, v___y_14745__boxed_788_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v_info_774_);
lean_dec(v_upperBound_773_);
lean_dec_ref(v_e_772_);
lean_dec(v___x_771_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(lean_object* v_00_u03b2_790_, lean_object* v_m_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_m_791_, v_a_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___boxed(lean_object* v_00_u03b2_794_, lean_object* v_m_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(v_00_u03b2_794_, v_m_795_, v_a_796_);
lean_dec_ref(v_a_796_);
lean_dec_ref(v_m_795_);
return v_res_797_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(lean_object* v_00_u03b2_798_, lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_799_ = stack[1].m_obj;
lean_object* v_x_800_ = stack[2].m_obj;
uint8_t v_res_802_;
v_res_802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(lean_box(0), v_a_799_, v_x_800_);
stack->m_num = v_res_802_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___boxed(lean_object* v_00_u03b2_803_, lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(v_00_u03b2_803_, v_a_804_, v_x_805_);
lean_dec(v_x_805_);
lean_dec_ref(v_a_804_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1(lean_object* v_00_u03b2_808_, lean_object* v_data_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(v_data_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2(lean_object* v_00_u03b2_811_, lean_object* v_a_812_, lean_object* v_b_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_812_, v_b_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(v_a_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___boxed(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6(v_00_u03b2_820_, v_a_821_, v_x_822_);
lean_dec(v_x_822_);
lean_dec_ref(v_a_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_824_, lean_object* v_i_825_, lean_object* v_source_826_, lean_object* v_target_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(v_i_825_, v_source_826_, v_target_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(v_x_830_, v_x_831_);
return v___x_832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_834_; lean_object* v___f_835_; 
v___x_834_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_835_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_835_, 0, v___x_834_);
return v___f_835_;
}
}
lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t v_k_836_, lean_object* v_____do__lift_837_){
_start:
{
lean_object* v_keyToExprs_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_keyToExprs_838_ = lean_ctor_get(v_____do__lift_837_, 1);
v___f_839_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0));
v___f_840_ = lean_obj_once(&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1, &l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1_once, _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1);
v___x_841_ = lean_box_uint64(v_k_836_);
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_840_, v___f_839_, v_keyToExprs_838_, v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_0interp(lean_interpreter_value* stack)
{
uint64_t v_k_836_ = stack[0].m_num;
lean_object* v_____do__lift_837_ = stack[1].m_obj;
lean_object* v_res_843_;
v_res_843_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v_k_836_, v_____do__lift_837_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* v_k_844_, lean_object* v_____do__lift_845_){
_start:
{
uint64_t v_k_boxed_846_; lean_object* v_res_847_; 
v_k_boxed_846_ = lean_unbox_uint64(v_k_844_);
lean_dec_ref(v_k_844_);
v_res_847_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v_k_boxed_846_, v_____do__lift_845_);
lean_dec_ref(v_____do__lift_845_);
return v_res_847_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(uint64_t v_a_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v_key_851_; lean_object* v_value_852_; lean_object* v_tail_853_; uint64_t v___x_854_; uint8_t v___x_855_; 
v_key_851_ = lean_ctor_get(v_x_849_, 0);
v_value_852_ = lean_ctor_get(v_x_849_, 1);
v_tail_853_ = lean_ctor_get(v_x_849_, 2);
v___x_854_ = lean_unbox_uint64(v_key_851_);
v___x_855_ = lean_uint64_dec_eq(v___x_854_, v_a_848_);
if (v___x_855_ == 0)
{
v_x_849_ = v_tail_853_;
goto _start;
}
else
{
lean_object* v___x_857_; 
lean_inc(v_value_852_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_value_852_);
return v___x_857_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_848_ = stack[0].m_num;
lean_object* v_x_849_ = stack[1].m_obj;
lean_object* v_res_858_;
v_res_858_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_848_, v_x_849_);
stack->m_obj
 = v_res_858_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg___boxed(lean_object* v_a_859_, lean_object* v_x_860_){
_start:
{
uint64_t v_a_boxed_861_; lean_object* v_res_862_; 
v_a_boxed_861_ = lean_unbox_uint64(v_a_859_);
lean_dec_ref(v_a_859_);
v_res_862_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_boxed_861_, v_x_860_);
lean_dec(v_x_860_);
return v_res_862_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object* v_m_863_, uint64_t v_a_864_){
_start:
{
lean_object* v_buckets_865_; lean_object* v___x_866_; uint64_t v___x_867_; uint64_t v___x_868_; uint64_t v_fold_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_buckets_865_ = lean_ctor_get(v_m_863_, 1);
v___x_866_ = lean_array_get_size(v_buckets_865_);
v___x_867_ = 32ULL;
v___x_868_ = lean_uint64_shift_right(v_a_864_, v___x_867_);
v_fold_869_ = lean_uint64_xor(v_a_864_, v___x_868_);
v___x_870_ = 16ULL;
v___x_871_ = lean_uint64_shift_right(v_fold_869_, v___x_870_);
v___x_872_ = lean_uint64_xor(v_fold_869_, v___x_871_);
v___x_873_ = lean_uint64_to_usize(v___x_872_);
v___x_874_ = lean_usize_of_nat(v___x_866_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_sub(v___x_874_, v___x_875_);
v___x_877_ = lean_usize_land(v___x_873_, v___x_876_);
v___x_878_ = lean_array_uget_borrowed(v_buckets_865_, v___x_877_);
v___x_879_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_864_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_863_ = stack[0].m_obj;
uint64_t v_a_864_ = stack[1].m_num;
lean_object* v_res_880_;
v_res_880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_863_, v_a_864_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* v_m_881_, lean_object* v_a_882_){
_start:
{
uint64_t v_a_boxed_883_; lean_object* v_res_884_; 
v_a_boxed_883_ = lean_unbox_uint64(v_a_882_);
lean_dec_ref(v_a_882_);
v_res_884_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_881_, v_a_boxed_883_);
lean_dec_ref(v_m_881_);
return v_res_884_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(uint64_t v_a_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
uint8_t v___x_887_; 
v___x_887_ = 0;
return v___x_887_;
}
else
{
lean_object* v_key_888_; lean_object* v_tail_889_; uint64_t v___x_890_; uint8_t v___x_891_; 
v_key_888_ = lean_ctor_get(v_x_886_, 0);
v_tail_889_ = lean_ctor_get(v_x_886_, 2);
v___x_890_ = lean_unbox_uint64(v_key_888_);
v___x_891_ = lean_uint64_dec_eq(v___x_890_, v_a_885_);
if (v___x_891_ == 0)
{
v_x_886_ = v_tail_889_;
goto _start;
}
else
{
return v___x_891_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_885_ = stack[0].m_num;
lean_object* v_x_886_ = stack[1].m_obj;
uint8_t v_res_893_;
v_res_893_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_885_, v_x_886_);
stack->m_num = v_res_893_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg___boxed(lean_object* v_a_894_, lean_object* v_x_895_){
_start:
{
uint64_t v_a_boxed_896_; uint8_t v_res_897_; lean_object* v_r_898_; 
v_a_boxed_896_ = lean_unbox_uint64(v_a_894_);
lean_dec_ref(v_a_894_);
v_res_897_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_boxed_896_, v_x_895_);
lean_dec(v_x_895_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(uint64_t v_a_899_, lean_object* v_b_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_dec(v_b_900_);
return v_x_901_;
}
else
{
lean_object* v_key_902_; lean_object* v_value_903_; lean_object* v_tail_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_918_; 
v_key_902_ = lean_ctor_get(v_x_901_, 0);
v_value_903_ = lean_ctor_get(v_x_901_, 1);
v_tail_904_ = lean_ctor_get(v_x_901_, 2);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_918_ == 0)
{
v___x_906_ = v_x_901_;
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_tail_904_);
lean_inc(v_value_903_);
lean_inc(v_key_902_);
lean_dec(v_x_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_918_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint64_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_unbox_uint64(v_key_902_);
v___x_909_ = lean_uint64_dec_eq(v___x_908_, v_a_899_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_899_, v_b_900_, v_tail_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_910_);
v___x_912_ = v___x_906_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_key_902_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_value_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_916_; 
lean_dec(v_value_903_);
lean_dec(v_key_902_);
v___x_914_ = lean_box_uint64(v_a_899_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_b_900_);
lean_ctor_set(v___x_906_, 0, v___x_914_);
v___x_916_ = v___x_906_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_b_900_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_tail_904_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_899_ = stack[0].m_num;
lean_object* v_b_900_ = stack[1].m_obj;
lean_object* v_x_901_ = stack[2].m_obj;
lean_object* v_res_919_;
v_res_919_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_899_, v_b_900_, v_x_901_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg___boxed(lean_object* v_a_920_, lean_object* v_b_921_, lean_object* v_x_922_){
_start:
{
uint64_t v_a_boxed_923_; lean_object* v_res_924_; 
v_a_boxed_923_ = lean_unbox_uint64(v_a_920_);
lean_dec_ref(v_a_920_);
v_res_924_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_boxed_923_, v_b_921_, v_x_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
return v_x_925_;
}
else
{
lean_object* v_key_927_; lean_object* v_value_928_; lean_object* v_tail_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_953_; 
v_key_927_ = lean_ctor_get(v_x_926_, 0);
v_value_928_ = lean_ctor_get(v_x_926_, 1);
v_tail_929_ = lean_ctor_get(v_x_926_, 2);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_926_);
if (v_isSharedCheck_953_ == 0)
{
v___x_931_ = v_x_926_;
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_tail_929_);
lean_inc(v_value_928_);
lean_inc(v_key_927_);
lean_dec(v_x_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v_fold_938_; uint64_t v___x_939_; uint64_t v___x_940_; uint64_t v___x_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; size_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_933_ = lean_array_get_size(v_x_925_);
v___x_934_ = 32ULL;
v___x_935_ = lean_unbox_uint64(v_key_927_);
v___x_936_ = lean_uint64_shift_right(v___x_935_, v___x_934_);
v___x_937_ = lean_unbox_uint64(v_key_927_);
v_fold_938_ = lean_uint64_xor(v___x_937_, v___x_936_);
v___x_939_ = 16ULL;
v___x_940_ = lean_uint64_shift_right(v_fold_938_, v___x_939_);
v___x_941_ = lean_uint64_xor(v_fold_938_, v___x_940_);
v___x_942_ = lean_uint64_to_usize(v___x_941_);
v___x_943_ = lean_usize_of_nat(v___x_933_);
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_sub(v___x_943_, v___x_944_);
v___x_946_ = lean_usize_land(v___x_942_, v___x_945_);
v___x_947_ = lean_array_uget_borrowed(v_x_925_, v___x_946_);
lean_inc(v___x_947_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v___x_947_);
v___x_949_ = v___x_931_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_key_927_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_value_928_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v___x_947_);
v___x_949_ = v_reuseFailAlloc_952_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_array_uset(v_x_925_, v___x_946_, v___x_949_);
v_x_925_ = v___x_950_;
v_x_926_ = v_tail_929_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(lean_object* v_i_954_, lean_object* v_source_955_, lean_object* v_target_956_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_array_get_size(v_source_955_);
v___x_958_ = lean_nat_dec_lt(v_i_954_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec_ref(v_source_955_);
lean_dec(v_i_954_);
return v_target_956_;
}
else
{
lean_object* v_es_959_; lean_object* v___x_960_; lean_object* v_source_961_; lean_object* v_target_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_es_959_ = lean_array_fget(v_source_955_, v_i_954_);
v___x_960_ = lean_box(0);
v_source_961_ = lean_array_fset(v_source_955_, v_i_954_, v___x_960_);
v_target_962_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(v_target_956_, v_es_959_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_nat_add(v_i_954_, v___x_963_);
lean_dec(v_i_954_);
v_i_954_ = v___x_964_;
v_source_955_ = v_source_961_;
v_target_956_ = v_target_962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(lean_object* v_data_966_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_nbuckets_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_967_ = lean_array_get_size(v_data_966_);
v___x_968_ = lean_unsigned_to_nat(2u);
v_nbuckets_969_ = lean_nat_mul(v___x_967_, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = lean_box(0);
v___x_972_ = lean_mk_array(v_nbuckets_969_, v___x_971_);
v___x_973_ = lean_array_propagate_mark(v_data_966_, v___x_972_);
v___x_974_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(v___x_970_, v_data_966_, v___x_973_);
return v___x_974_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(lean_object* v_m_975_, uint64_t v_a_976_, lean_object* v_b_977_){
_start:
{
lean_object* v_size_978_; lean_object* v_buckets_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1022_; 
v_size_978_ = lean_ctor_get(v_m_975_, 0);
v_buckets_979_ = lean_ctor_get(v_m_975_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_m_975_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_981_ = v_m_975_;
v_isShared_982_ = v_isSharedCheck_1022_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_buckets_979_);
lean_inc(v_size_978_);
lean_dec(v_m_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1022_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v_fold_986_; uint64_t v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; lean_object* v_bkt_995_; uint8_t v___x_996_; 
v___x_983_ = lean_array_get_size(v_buckets_979_);
v___x_984_ = 32ULL;
v___x_985_ = lean_uint64_shift_right(v_a_976_, v___x_984_);
v_fold_986_ = lean_uint64_xor(v_a_976_, v___x_985_);
v___x_987_ = 16ULL;
v___x_988_ = lean_uint64_shift_right(v_fold_986_, v___x_987_);
v___x_989_ = lean_uint64_xor(v_fold_986_, v___x_988_);
v___x_990_ = lean_uint64_to_usize(v___x_989_);
v___x_991_ = lean_usize_of_nat(v___x_983_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_sub(v___x_991_, v___x_992_);
v___x_994_ = lean_usize_land(v___x_990_, v___x_993_);
v_bkt_995_ = lean_array_uget_borrowed(v_buckets_979_, v___x_994_);
v___x_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_976_, v_bkt_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v_size_x27_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_buckets_x27_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v_size_x27_998_ = lean_nat_add(v_size_978_, v___x_997_);
lean_dec(v_size_978_);
v___x_999_ = lean_box_uint64(v_a_976_);
lean_inc(v_bkt_995_);
v___x_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v_b_977_);
lean_ctor_set(v___x_1000_, 2, v_bkt_995_);
v_buckets_x27_1001_ = lean_array_uset(v_buckets_979_, v___x_994_, v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(4u);
v___x_1003_ = lean_nat_mul(v_size_x27_998_, v___x_1002_);
v___x_1004_ = lean_unsigned_to_nat(3u);
v___x_1005_ = lean_nat_div(v___x_1003_, v___x_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_array_get_size(v_buckets_x27_1001_);
v___x_1007_ = lean_nat_dec_le(v___x_1005_, v___x_1006_);
lean_dec(v___x_1005_);
if (v___x_1007_ == 0)
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(v_buckets_x27_1001_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_val_1008_);
lean_ctor_set(v___x_981_, 0, v_size_x27_998_);
v___x_1010_ = v___x_981_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_size_x27_998_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_val_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v___x_1013_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_buckets_x27_1001_);
lean_ctor_set(v___x_981_, 0, v_size_x27_998_);
v___x_1013_ = v___x_981_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_size_x27_998_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_buckets_x27_1001_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v___x_1015_; lean_object* v_buckets_x27_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_inc(v_bkt_995_);
v___x_1015_ = lean_box(0);
v_buckets_x27_1016_ = lean_array_uset(v_buckets_979_, v___x_994_, v___x_1015_);
v___x_1017_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_976_, v_b_977_, v_bkt_995_);
v___x_1018_ = lean_array_uset(v_buckets_x27_1016_, v___x_994_, v___x_1017_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v___x_1018_);
v___x_1020_ = v___x_981_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_size_978_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_975_ = stack[0].m_obj;
uint64_t v_a_976_ = stack[1].m_num;
lean_object* v_b_977_ = stack[2].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_975_, v_a_976_, v_b_977_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg___boxed(lean_object* v_m_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_){
_start:
{
uint64_t v_a_boxed_1027_; lean_object* v_res_1028_; 
v_a_boxed_1027_ = lean_unbox_uint64(v_a_1025_);
lean_dec_ref(v_a_1025_);
v_res_1028_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1024_, v_a_boxed_1027_, v_b_1026_);
return v_res_1028_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* v_e_1032_, lean_object* v_as_x27_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
if (lean_obj_tag(v_as_x27_1033_) == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref(v_e_1032_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_b_1034_);
return v___x_1040_;
}
else
{
lean_object* v_head_1041_; lean_object* v_tail_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref(v_b_1034_);
v_head_1041_ = lean_ctor_get(v_as_x27_1033_, 0);
v_tail_1042_ = lean_ctor_get(v_as_x27_1033_, 1);
v___x_1043_ = lean_box(0);
v___x_1044_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
lean_inc(v_head_1041_);
lean_inc_ref(v_e_1032_);
v___x_1045_ = l_Lean_Meta_isExprDefEq(v_e_1032_, v_head_1041_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1057_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_unbox(v_a_1046_);
lean_dec(v_a_1046_);
if (v___x_1050_ == 0)
{
lean_del_object(v___x_1048_);
v_as_x27_1033_ = v_tail_1042_;
v_b_1034_ = v___x_1044_;
goto _start;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec_ref(v_e_1032_);
lean_inc(v_head_1041_);
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v_head_1041_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_1043_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1053_);
v___x_1055_ = v___x_1048_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v_e_1032_);
v_a_1058_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1045_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1045_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1032_ = stack[0].m_obj;
lean_object* v_as_x27_1033_ = stack[1].m_obj;
lean_object* v_b_1034_ = stack[2].m_obj;
lean_object* v___y_1035_ = stack[3].m_obj;
lean_object* v___y_1036_ = stack[4].m_obj;
lean_object* v___y_1037_ = stack[5].m_obj;
lean_object* v___y_1038_ = stack[6].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1032_, v_as_x27_1033_, v_b_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object* v_e_1067_, lean_object* v_as_x27_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1067_, v_as_x27_1068_, v_b_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v_as_x27_1068_);
return v_res_1075_;
}
}
lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* v_e_1076_, uint8_t v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1084_; 
lean_inc_ref(v_e_1076_);
v___x_1084_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1222_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1222_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1222_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v_keyToExprs_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1220_; 
v___x_1089_ = lean_st_ref_get(v_a_1078_);
v_keyToExprs_1090_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1221_);
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1220_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_keyToExprs_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1220_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
uint64_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_unbox_uint64(v_a_1085_);
v___x_1095_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_keyToExprs_1090_, v___x_1094_);
lean_dec_ref(v_keyToExprs_1090_);
if (lean_obj_tag(v___x_1095_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; uint8_t v_transparency_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
lean_del_object(v___x_1092_);
lean_del_object(v___x_1087_);
v_val_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = l_Lean_Meta_Context_config(v_a_1079_);
v_transparency_1098_ = lean_ctor_get_uint8(v___x_1097_, 9);
lean_dec_ref(v___x_1097_);
v___x_1099_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
v___x_1100_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1098_, v_a_1077_);
if (v___x_1100_ == 0)
{
lean_object* v_keyedConfig_1101_; uint8_t v_trackZetaDelta_1102_; lean_object* v_zetaDeltaSet_1103_; lean_object* v_lctx_1104_; lean_object* v_localInstances_1105_; lean_object* v_defEqCtx_x3f_1106_; lean_object* v_synthPendingDepth_1107_; lean_object* v_customCanUnfoldPredicate_x3f_1108_; uint8_t v_univApprox_1109_; uint8_t v_inTypeClassResolution_1110_; uint8_t v_cacheInferType_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_keyedConfig_1101_ = lean_ctor_get(v_a_1079_, 0);
v_trackZetaDelta_1102_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*7);
v_zetaDeltaSet_1103_ = lean_ctor_get(v_a_1079_, 1);
v_lctx_1104_ = lean_ctor_get(v_a_1079_, 2);
v_localInstances_1105_ = lean_ctor_get(v_a_1079_, 3);
v_defEqCtx_x3f_1106_ = lean_ctor_get(v_a_1079_, 4);
v_synthPendingDepth_1107_ = lean_ctor_get(v_a_1079_, 5);
v_customCanUnfoldPredicate_x3f_1108_ = lean_ctor_get(v_a_1079_, 6);
v_univApprox_1109_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1110_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*7 + 2);
v_cacheInferType_1111_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1101_);
v___x_1112_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_a_1077_, v_keyedConfig_1101_);
lean_inc(v_customCanUnfoldPredicate_x3f_1108_);
lean_inc(v_synthPendingDepth_1107_);
lean_inc(v_defEqCtx_x3f_1106_);
lean_inc_ref(v_localInstances_1105_);
lean_inc_ref(v_lctx_1104_);
lean_inc(v_zetaDeltaSet_1103_);
v___x_1113_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v_zetaDeltaSet_1103_);
lean_ctor_set(v___x_1113_, 2, v_lctx_1104_);
lean_ctor_set(v___x_1113_, 3, v_localInstances_1105_);
lean_ctor_set(v___x_1113_, 4, v_defEqCtx_x3f_1106_);
lean_ctor_set(v___x_1113_, 5, v_synthPendingDepth_1107_);
lean_ctor_set(v___x_1113_, 6, v_customCanUnfoldPredicate_x3f_1108_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*7, v_trackZetaDelta_1102_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*7 + 1, v_univApprox_1109_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1110_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*7 + 3, v_cacheInferType_1111_);
lean_inc_ref(v_e_1076_);
v___x_1114_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1076_, v_val_1096_, v___x_1099_, v___x_1113_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec_ref_known(v___x_1113_, 7);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1148_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1148_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1148_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_fst_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1146_; 
v_fst_1119_ = lean_ctor_get(v_a_1115_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_a_1115_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_a_1115_, 1);
lean_dec(v_unused_1147_);
v___x_1121_ = v_a_1115_;
v_isShared_1122_ = v_isSharedCheck_1146_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_fst_1119_);
lean_dec(v_a_1115_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1146_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
if (lean_obj_tag(v_fst_1119_) == 0)
{
lean_object* v___x_1123_; lean_object* v_cache_1124_; lean_object* v_keyToExprs_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1141_; 
v___x_1123_ = lean_st_ref_take(v_a_1078_);
v_cache_1124_ = lean_ctor_get(v___x_1123_, 0);
v_keyToExprs_1125_ = lean_ctor_get(v___x_1123_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1127_ = v___x_1123_;
v_isShared_1128_ = v_isSharedCheck_1141_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_keyToExprs_1125_);
lean_inc(v_cache_1124_);
lean_dec(v___x_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1141_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
lean_inc_ref(v_e_1076_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 1);
lean_ctor_set(v___x_1121_, 1, v_val_1096_);
lean_ctor_set(v___x_1121_, 0, v_e_1076_);
v___x_1130_ = v___x_1121_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_e_1076_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_val_1096_);
v___x_1130_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
uint64_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1131_ = lean_unbox_uint64(v_a_1085_);
lean_dec(v_a_1085_);
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1125_, v___x_1131_, v___x_1130_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v___x_1132_);
v___x_1134_ = v___x_1127_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_st_ref_put(v_a_1078_, v___x_1134_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v_e_1076_);
v___x_1137_ = v___x_1117_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_e_1076_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
else
{
lean_object* v_val_1142_; lean_object* v___x_1144_; 
lean_del_object(v___x_1121_);
lean_dec(v_val_1096_);
lean_dec(v_a_1085_);
lean_dec_ref(v_e_1076_);
v_val_1142_ = lean_ctor_get(v_fst_1119_, 0);
lean_inc(v_val_1142_);
lean_dec_ref_known(v_fst_1119_, 1);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v_val_1142_);
v___x_1144_ = v___x_1117_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_val_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_val_1096_);
lean_dec(v_a_1085_);
lean_dec_ref(v_e_1076_);
v_a_1149_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1114_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1114_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1157_; 
lean_inc_ref(v_e_1076_);
v___x_1157_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1076_, v_val_1096_, v___x_1099_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1191_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1191_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1191_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_fst_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1189_; 
v_fst_1162_ = lean_ctor_get(v_a_1158_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_a_1158_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v_a_1158_, 1);
lean_dec(v_unused_1190_);
v___x_1164_ = v_a_1158_;
v_isShared_1165_ = v_isSharedCheck_1189_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_fst_1162_);
lean_dec(v_a_1158_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1189_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
if (lean_obj_tag(v_fst_1162_) == 0)
{
lean_object* v___x_1166_; lean_object* v_cache_1167_; lean_object* v_keyToExprs_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1184_; 
v___x_1166_ = lean_st_ref_take(v_a_1078_);
v_cache_1167_ = lean_ctor_get(v___x_1166_, 0);
v_keyToExprs_1168_ = lean_ctor_get(v___x_1166_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1170_ = v___x_1166_;
v_isShared_1171_ = v_isSharedCheck_1184_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_keyToExprs_1168_);
lean_inc(v_cache_1167_);
lean_dec(v___x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1184_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
lean_inc_ref(v_e_1076_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 1);
lean_ctor_set(v___x_1164_, 1, v_val_1096_);
lean_ctor_set(v___x_1164_, 0, v_e_1076_);
v___x_1173_ = v___x_1164_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_e_1076_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_val_1096_);
v___x_1173_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
uint64_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = lean_unbox_uint64(v_a_1085_);
lean_dec(v_a_1085_);
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1168_, v___x_1174_, v___x_1173_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1175_);
v___x_1177_ = v___x_1170_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_cache_1167_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_st_ref_put(v_a_1078_, v___x_1177_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v_e_1076_);
v___x_1180_ = v___x_1160_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_e_1076_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_object* v_val_1185_; lean_object* v___x_1187_; 
lean_del_object(v___x_1164_);
lean_dec(v_val_1096_);
lean_dec(v_a_1085_);
lean_dec_ref(v_e_1076_);
v_val_1185_ = lean_ctor_get(v_fst_1162_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_fst_1162_, 1);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v_val_1185_);
v___x_1187_ = v___x_1160_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_val_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_val_1096_);
lean_dec(v_a_1085_);
lean_dec_ref(v_e_1076_);
v_a_1192_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1157_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1157_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
else
{
lean_object* v___x_1200_; lean_object* v_cache_1201_; lean_object* v_keyToExprs_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v___x_1095_);
v___x_1200_ = lean_st_ref_take(v_a_1078_);
v_cache_1201_ = lean_ctor_get(v___x_1200_, 0);
v_keyToExprs_1202_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1219_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_keyToExprs_1202_);
lean_inc(v_cache_1201_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1219_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_box(0);
lean_inc_ref(v_e_1076_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
lean_ctor_set(v___x_1092_, 1, v___x_1206_);
lean_ctor_set(v___x_1092_, 0, v_e_1076_);
v___x_1208_ = v___x_1092_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_e_1076_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
uint64_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1209_ = lean_unbox_uint64(v_a_1085_);
lean_dec(v_a_1085_);
v___x_1210_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1202_, v___x_1209_, v___x_1208_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1210_);
v___x_1212_ = v___x_1204_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_cache_1201_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_st_ref_put(v_a_1078_, v___x_1212_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_e_1076_);
v___x_1215_ = v___x_1087_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_e_1076_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
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
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_e_1076_);
v_a_1223_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1084_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1084_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Canonicalizer_canon_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1076_ = stack[0].m_obj;
uint8_t v_a_1077_ = stack[1].m_num;
lean_object* v_a_1078_ = stack[2].m_obj;
lean_object* v_a_1079_ = stack[3].m_obj;
lean_object* v_a_1080_ = stack[4].m_obj;
lean_object* v_a_1081_ = stack[5].m_obj;
lean_object* v_a_1082_ = stack[6].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l_Lean_Meta_Canonicalizer_canon(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* v_e_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
uint8_t v_a_boxed_1240_; lean_object* v_res_1241_; 
v_a_boxed_1240_ = lean_unbox(v_a_1233_);
v_res_1241_ = l_Lean_Meta_Canonicalizer_canon(v_e_1232_, v_a_boxed_1240_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
return v_res_1241_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object* v_00_u03b2_1242_, lean_object* v_m_1243_, uint64_t v_a_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_1243_, v_a_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1243_ = stack[1].m_obj;
uint64_t v_a_1244_ = stack[2].m_num;
lean_object* v_res_1246_;
v_res_1246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_box(0), v_m_1243_, v_a_1244_);
stack->m_obj
 = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* v_00_u03b2_1247_, lean_object* v_m_1248_, lean_object* v_a_1249_){
_start:
{
uint64_t v_a_boxed_1250_; lean_object* v_res_1251_; 
v_a_boxed_1250_ = lean_unbox_uint64(v_a_1249_);
lean_dec_ref(v_a_1249_);
v_res_1251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(v_00_u03b2_1247_, v_m_1248_, v_a_boxed_1250_);
lean_dec_ref(v_m_1248_);
return v_res_1251_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object* v_e_1252_, lean_object* v_as_1253_, lean_object* v_as_x27_1254_, lean_object* v_b_1255_, lean_object* v_a_1256_, uint8_t v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1252_, v_as_x27_1254_, v_b_1255_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1252_ = stack[0].m_obj;
lean_object* v_as_1253_ = stack[1].m_obj;
lean_object* v_as_x27_1254_ = stack[2].m_obj;
lean_object* v_b_1255_ = stack[3].m_obj;
uint8_t v___y_1257_ = stack[5].m_num;
lean_object* v___y_1258_ = stack[6].m_obj;
lean_object* v___y_1259_ = stack[7].m_obj;
lean_object* v___y_1260_ = stack[8].m_obj;
lean_object* v___y_1261_ = stack[9].m_obj;
lean_object* v___y_1262_ = stack[10].m_obj;
lean_object* v_res_1265_;
v_res_1265_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(v_e_1252_, v_as_1253_, v_as_x27_1254_, v_b_1255_, lean_box(0), v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object* v_e_1266_, lean_object* v_as_1267_, lean_object* v_as_x27_1268_, lean_object* v_b_1269_, lean_object* v_a_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v___y_11631__boxed_1278_; lean_object* v_res_1279_; 
v___y_11631__boxed_1278_ = lean_unbox(v___y_1271_);
v_res_1279_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(v_e_1266_, v_as_1267_, v_as_x27_1268_, v_b_1269_, v_a_1270_, v___y_11631__boxed_1278_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v_as_x27_1268_);
lean_dec(v_as_1267_);
return v_res_1279_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(lean_object* v_00_u03b2_1280_, lean_object* v_m_1281_, uint64_t v_a_1282_, lean_object* v_b_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1281_, v_a_1282_, v_b_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1281_ = stack[1].m_obj;
uint64_t v_a_1282_ = stack[2].m_num;
lean_object* v_b_1283_ = stack[3].m_obj;
lean_object* v_res_1285_;
v_res_1285_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(lean_box(0), v_m_1281_, v_a_1282_, v_b_1283_);
stack->m_obj
 = v_res_1285_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___boxed(lean_object* v_00_u03b2_1286_, lean_object* v_m_1287_, lean_object* v_a_1288_, lean_object* v_b_1289_){
_start:
{
uint64_t v_a_boxed_1290_; lean_object* v_res_1291_; 
v_a_boxed_1290_ = lean_unbox_uint64(v_a_1288_);
lean_dec_ref(v_a_1288_);
v_res_1291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(v_00_u03b2_1286_, v_m_1287_, v_a_boxed_1290_, v_b_1289_);
return v_res_1291_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(lean_object* v_00_u03b2_1292_, uint64_t v_a_1293_, lean_object* v_x_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_1293_, v_x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1293_ = stack[1].m_num;
lean_object* v_x_1294_ = stack[2].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(lean_box(0), v_a_1293_, v_x_1294_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_a_1298_, lean_object* v_x_1299_){
_start:
{
uint64_t v_a_boxed_1300_; lean_object* v_res_1301_; 
v_a_boxed_1300_ = lean_unbox_uint64(v_a_1298_);
lean_dec_ref(v_a_1298_);
v_res_1301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(v_00_u03b2_1297_, v_a_boxed_1300_, v_x_1299_);
lean_dec(v_x_1299_);
return v_res_1301_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(lean_object* v_00_u03b2_1302_, uint64_t v_a_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_1303_, v_x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1303_ = stack[1].m_num;
lean_object* v_x_1304_ = stack[2].m_obj;
uint8_t v_res_1306_;
v_res_1306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(lean_box(0), v_a_1303_, v_x_1304_);
stack->m_num = v_res_1306_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1307_, lean_object* v_a_1308_, lean_object* v_x_1309_){
_start:
{
uint64_t v_a_boxed_1310_; uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_a_boxed_1310_ = lean_unbox_uint64(v_a_1308_);
lean_dec_ref(v_a_1308_);
v_res_1311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(v_00_u03b2_1307_, v_a_boxed_1310_, v_x_1309_);
lean_dec(v_x_1309_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4(lean_object* v_00_u03b2_1313_, lean_object* v_data_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(v_data_1314_);
return v___x_1315_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(lean_object* v_00_u03b2_1316_, uint64_t v_a_1317_, lean_object* v_b_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_1317_, v_b_1318_, v_x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1317_ = stack[1].m_num;
lean_object* v_b_1318_ = stack[2].m_obj;
lean_object* v_x_1319_ = stack[3].m_obj;
lean_object* v_res_1321_;
v_res_1321_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(lean_box(0), v_a_1317_, v_b_1318_, v_x_1319_);
stack->m_obj
 = v_res_1321_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1322_, lean_object* v_a_1323_, lean_object* v_b_1324_, lean_object* v_x_1325_){
_start:
{
uint64_t v_a_boxed_1326_; lean_object* v_res_1327_; 
v_a_boxed_1326_ = lean_unbox_uint64(v_a_1323_);
lean_dec_ref(v_a_1323_);
v_res_1327_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(v_00_u03b2_1322_, v_a_boxed_1326_, v_b_1324_, v_x_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1328_, lean_object* v_i_1329_, lean_object* v_source_1330_, lean_object* v_target_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(v_i_1329_, v_source_1330_, v_target_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1334_, v_x_1335_);
return v___x_1336_;
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
