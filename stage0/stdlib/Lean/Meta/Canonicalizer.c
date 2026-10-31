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
lean_object* l_instDecidableEqUInt64___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0;
static const lean_closure_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1_value;
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
lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v_cache_174_; lean_object* v_keyToExprs_175_; lean_object* v_buckets_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___f_166_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_167_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_168_ = lean_st_ref_take(v_a_164_);
v_cache_174_ = lean_ctor_get(v___x_168_, 0);
v_keyToExprs_175_ = lean_ctor_get(v___x_168_, 1);
v_buckets_176_ = lean_ctor_get(v_cache_174_, 1);
v___x_177_ = lean_box(0);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_array_get_size(v_buckets_176_);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec_ref(v_e_162_);
v_fst_170_ = v___x_177_;
v_snd_171_ = v___x_168_;
goto v___jp_169_;
}
else
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_189_; 
lean_inc_ref(v_keyToExprs_175_);
lean_inc_ref(v_cache_174_);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_190_ = lean_ctor_get(v___x_168_, 1);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v___x_168_, 0);
lean_dec(v_unused_191_);
v___x_182_ = v___x_168_;
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
else
{
lean_dec(v___x_168_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_box_uint64(v_key_163_);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_166_, v___f_167_, v_cache_174_, v_e_162_, v___x_184_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_keyToExprs_175_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v_fst_170_ = v___x_177_;
v_snd_171_ = v___x_187_;
goto v___jp_169_;
}
}
}
v___jp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_st_ref_put(v_a_164_, v_snd_171_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_fst_170_);
return v___x_173_;
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
lean_object* v___f_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v_cache_215_; lean_object* v_keyToExprs_216_; lean_object* v_buckets_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___f_207_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___closed__0));
v___f_208_ = ((lean_object*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___closed__0));
v___x_209_ = lean_st_ref_take(v_a_201_);
v_cache_215_ = lean_ctor_get(v___x_209_, 0);
v_keyToExprs_216_ = lean_ctor_get(v___x_209_, 1);
v_buckets_217_ = lean_ctor_get(v_cache_215_, 1);
v___x_218_ = lean_box(0);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_array_get_size(v_buckets_217_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_e_198_);
v_fst_211_ = v___x_218_;
v_snd_212_ = v___x_209_;
goto v___jp_210_;
}
else
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_230_; 
lean_inc_ref(v_keyToExprs_216_);
lean_inc_ref(v_cache_215_);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_231_ = lean_ctor_get(v___x_209_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v___x_209_, 0);
lean_dec(v_unused_232_);
v___x_223_ = v___x_209_;
v_isShared_224_ = v_isSharedCheck_230_;
goto v_resetjp_222_;
}
else
{
lean_dec(v___x_209_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_230_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = lean_box_uint64(v_key_199_);
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_207_, v___f_208_, v_cache_215_, v_e_198_, v___x_225_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_keyToExprs_216_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v_fst_211_ = v___x_218_;
v_snd_212_ = v___x_228_;
goto v___jp_210_;
}
}
}
v___jp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_st_ref_put(v_a_201_, v_snd_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v_fst_211_);
return v___x_214_;
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
v___x_265_ = lean_st_ref_put(v___y_246_, v___x_264_);
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
uint8_t v___y_13549__boxed_291_; lean_object* v_res_292_; 
v___y_13549__boxed_291_ = lean_unbox(v___y_284_);
v_res_292_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v_e_283_, v___y_13549__boxed_291_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
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
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_nbuckets_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_371_ = lean_array_get_size(v_data_370_);
v___x_372_ = lean_unsigned_to_nat(2u);
v_nbuckets_373_ = lean_nat_mul(v___x_371_, v___x_372_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_box(0);
v___x_376_ = lean_mk_array(v_nbuckets_373_, v___x_375_);
v___x_377_ = lean_array_propagate_mark(v_data_370_, v___x_376_);
v___x_378_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(v___x_374_, v_data_370_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(lean_object* v_a_379_, lean_object* v_b_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_dec(v_b_380_);
lean_dec_ref(v_a_379_);
return v_x_381_;
}
else
{
lean_object* v_key_382_; lean_object* v_value_383_; lean_object* v_tail_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_398_; 
v_key_382_ = lean_ctor_get(v_x_381_, 0);
v_value_383_ = lean_ctor_get(v_x_381_, 1);
v_tail_384_ = lean_ctor_get(v_x_381_, 2);
v_isSharedCheck_398_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_386_ = v_x_381_;
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_tail_384_);
lean_inc(v_value_383_);
lean_inc(v_key_382_);
lean_dec(v_x_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
size_t v___x_388_; size_t v___x_389_; uint8_t v___x_390_; 
v___x_388_ = lean_ptr_addr(v_key_382_);
v___x_389_ = lean_ptr_addr(v_a_379_);
v___x_390_ = lean_usize_dec_eq(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_379_, v_b_380_, v_tail_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_391_);
v___x_393_ = v___x_386_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_key_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_value_383_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
else
{
lean_object* v___x_396_; 
lean_dec(v_value_383_);
lean_dec(v_key_382_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_b_380_);
lean_ctor_set(v___x_386_, 0, v_a_379_);
v___x_396_ = v___x_386_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_b_380_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_tail_384_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(lean_object* v_a_399_, lean_object* v_x_400_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
else
{
lean_object* v_key_402_; lean_object* v_tail_403_; size_t v___x_404_; size_t v___x_405_; uint8_t v___x_406_; 
v_key_402_ = lean_ctor_get(v_x_400_, 0);
v_tail_403_ = lean_ctor_get(v_x_400_, 2);
v___x_404_ = lean_ptr_addr(v_key_402_);
v___x_405_ = lean_ptr_addr(v_a_399_);
v___x_406_ = lean_usize_dec_eq(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
v_x_400_ = v_tail_403_;
goto _start;
}
else
{
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg___boxed(lean_object* v_a_408_, lean_object* v_x_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_408_, v_x_409_);
lean_dec(v_x_409_);
lean_dec_ref(v_a_408_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object* v_m_412_, lean_object* v_a_413_, lean_object* v_b_414_){
_start:
{
lean_object* v_size_415_; lean_object* v_buckets_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_460_; 
v_size_415_ = lean_ctor_get(v_m_412_, 0);
v_buckets_416_ = lean_ctor_get(v_m_412_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_m_412_);
if (v_isSharedCheck_460_ == 0)
{
v___x_418_ = v_m_412_;
v_isShared_419_ = v_isSharedCheck_460_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_buckets_416_);
lean_inc(v_size_415_);
lean_dec(v_m_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_460_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; size_t v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v_fold_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; lean_object* v_bkt_434_; uint8_t v___x_435_; 
v___x_420_ = lean_array_get_size(v_buckets_416_);
v___x_421_ = lean_ptr_addr(v_a_413_);
v___x_422_ = lean_usize_to_uint64(v___x_421_);
v___x_423_ = 32ULL;
v___x_424_ = lean_uint64_shift_right(v___x_422_, v___x_423_);
v_fold_425_ = lean_uint64_xor(v___x_422_, v___x_424_);
v___x_426_ = 16ULL;
v___x_427_ = lean_uint64_shift_right(v_fold_425_, v___x_426_);
v___x_428_ = lean_uint64_xor(v_fold_425_, v___x_427_);
v___x_429_ = lean_uint64_to_usize(v___x_428_);
v___x_430_ = lean_usize_of_nat(v___x_420_);
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_sub(v___x_430_, v___x_431_);
v___x_433_ = lean_usize_land(v___x_429_, v___x_432_);
v_bkt_434_ = lean_array_uget_borrowed(v_buckets_416_, v___x_433_);
v___x_435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_413_, v_bkt_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v_size_x27_437_; lean_object* v___x_438_; lean_object* v_buckets_x27_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v_size_x27_437_ = lean_nat_add(v_size_415_, v___x_436_);
lean_dec(v_size_415_);
lean_inc(v_bkt_434_);
v___x_438_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_438_, 0, v_a_413_);
lean_ctor_set(v___x_438_, 1, v_b_414_);
lean_ctor_set(v___x_438_, 2, v_bkt_434_);
v_buckets_x27_439_ = lean_array_uset(v_buckets_416_, v___x_433_, v___x_438_);
v___x_440_ = lean_unsigned_to_nat(4u);
v___x_441_ = lean_nat_mul(v_size_x27_437_, v___x_440_);
v___x_442_ = lean_unsigned_to_nat(3u);
v___x_443_ = lean_nat_div(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_array_get_size(v_buckets_x27_439_);
v___x_445_ = lean_nat_dec_le(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v_val_446_; lean_object* v___x_448_; 
v_val_446_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(v_buckets_x27_439_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_val_446_);
lean_ctor_set(v___x_418_, 0, v_size_x27_437_);
v___x_448_ = v___x_418_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_size_x27_437_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_val_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
lean_object* v___x_451_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_buckets_x27_439_);
lean_ctor_set(v___x_418_, 0, v_size_x27_437_);
v___x_451_ = v___x_418_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_size_x27_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_buckets_x27_439_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v___x_453_; lean_object* v_buckets_x27_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
lean_inc(v_bkt_434_);
v___x_453_ = lean_box(0);
v_buckets_x27_454_ = lean_array_uset(v_buckets_416_, v___x_433_, v___x_453_);
v___x_455_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_413_, v_b_414_, v_bkt_434_);
v___x_456_ = lean_array_uset(v_buckets_x27_454_, v___x_433_, v___x_455_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v___x_456_);
v___x_458_ = v___x_418_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_size_415_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* v_e_467_, uint8_t v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_t_476_; lean_object* v_b_477_; uint8_t v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; uint64_t v___y_500_; lean_object* v___y_501_; lean_object* v_snd_502_; uint64_t v_key_507_; lean_object* v___y_508_; lean_object* v___y_528_; lean_object* v_info_529_; uint8_t v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___x_563_; lean_object* v_cache_651_; lean_object* v_buckets_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_563_ = lean_st_ref_get(v_a_469_);
v_cache_651_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_cache_651_);
lean_dec(v___x_563_);
v_buckets_652_ = lean_ctor_get(v_cache_651_, 1);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_array_get_size(v_buckets_652_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_dec_ref(v_cache_651_);
goto v___jp_564_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_cache_651_, v_e_467_);
lean_dec_ref(v_cache_651_);
if (lean_obj_tag(v___x_656_) == 1)
{
lean_object* v_val_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_e_467_);
v_val_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_val_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 0);
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_val_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_dec(v___x_656_);
goto v___jp_564_;
}
}
v___jp_475_:
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_t_476_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_b_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_498_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_498_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_498_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_498_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint64_t v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_491_ = lean_unbox_uint64(v_a_485_);
lean_dec(v_a_485_);
v___x_492_ = lean_unbox_uint64(v_a_487_);
lean_dec(v_a_487_);
v___x_493_ = lean_uint64_mix_hash(v___x_491_, v___x_492_);
v___x_494_ = lean_box_uint64(v___x_493_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_494_);
v___x_496_ = v___x_489_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_dec(v_a_485_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_b_477_);
return v___x_484_;
}
}
v___jp_499_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_st_ref_put(v___y_501_, v_snd_502_);
v___x_504_ = lean_box_uint64(v___y_500_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
v___jp_506_:
{
lean_object* v___x_509_; lean_object* v_cache_510_; lean_object* v_keyToExprs_511_; lean_object* v_buckets_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_509_ = lean_st_ref_take(v___y_508_);
v_cache_510_ = lean_ctor_get(v___x_509_, 0);
v_keyToExprs_511_ = lean_ctor_get(v___x_509_, 1);
v_buckets_512_ = lean_ctor_get(v_cache_510_, 1);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_array_get_size(v_buckets_512_);
v___x_515_ = lean_nat_dec_lt(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_e_467_);
v___y_500_ = v_key_507_;
v___y_501_ = v___y_508_;
v_snd_502_ = v___x_509_;
goto v___jp_499_;
}
else
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
lean_inc_ref(v_keyToExprs_511_);
lean_inc_ref(v_cache_510_);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; lean_object* v_unused_526_; 
v_unused_525_ = lean_ctor_get(v___x_509_, 1);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v___x_509_, 0);
lean_dec(v_unused_526_);
v___x_517_ = v___x_509_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_dec(v___x_509_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_box_uint64(v_key_507_);
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_cache_510_, v_e_467_, v___x_519_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_keyToExprs_511_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v___y_500_ = v_key_507_;
v___y_501_ = v___y_508_;
v_snd_502_ = v___x_522_;
goto v___jp_499_;
}
}
}
}
v___jp_527_:
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___y_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint64_t v___x_540_; lean_object* v___x_541_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = l_Lean_Expr_getAppNumArgs(v_e_467_);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_unbox_uint64(v_a_537_);
lean_dec(v_a_537_);
v___x_541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v___x_538_, v_info_529_, v___x_538_, v_e_467_, v___x_539_, v___x_540_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec_ref(v_e_467_);
lean_dec_ref(v_info_529_);
lean_dec(v___x_538_);
return v___x_541_;
}
else
{
lean_dec_ref(v_info_529_);
lean_dec_ref(v_e_467_);
return v___x_536_;
}
}
v___jp_542_:
{
uint8_t v___x_550_; 
v___x_550_ = l_Lean_Expr_hasLooseBVars(v___y_543_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_box(0);
lean_inc_ref(v___y_543_);
v___x_552_ = l_Lean_Meta_getFunInfo(v___y_543_, v___x_551_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___y_528_ = v___y_543_;
v_info_529_ = v_a_553_;
v___y_530_ = v___y_544_;
v___y_531_ = v___y_545_;
v___y_532_ = v___y_546_;
v___y_533_ = v___y_547_;
v___y_534_ = v___y_548_;
v___y_535_ = v___y_549_;
goto v___jp_527_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v___y_543_);
lean_dec_ref(v_e_467_);
v_a_554_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1));
v___y_528_ = v___y_543_;
v_info_529_ = v___x_562_;
v___y_530_ = v___y_544_;
v___y_531_ = v___y_545_;
v___y_532_ = v___y_546_;
v___y_533_ = v___y_547_;
v___y_534_ = v___y_548_;
v___y_535_ = v___y_549_;
goto v___jp_527_;
}
}
v___jp_564_:
{
switch(lean_obj_tag(v_e_467_))
{
case 2:
{
lean_object* v___x_565_; 
lean_inc_ref(v_e_467_);
v___x_565_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_467_, v_a_471_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_579_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_579_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
uint8_t v___x_570_; 
v___x_570_ = lean_expr_eqv(v_a_566_, v_e_467_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_del_object(v___x_568_);
v___x_571_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_a_566_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; uint64_t v___x_573_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = lean_unbox_uint64(v_a_572_);
lean_dec(v_a_572_);
v_key_507_ = v___x_573_;
v___y_508_ = v_a_469_;
goto v___jp_506_;
}
else
{
lean_dec_ref_known(v_e_467_, 1);
return v___x_571_;
}
}
else
{
uint64_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
lean_dec(v_a_566_);
v___x_574_ = l_Lean_Expr_hash(v_e_467_);
lean_dec_ref_known(v_e_467_, 1);
v___x_575_ = lean_box_uint64(v___x_574_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_575_);
v___x_577_ = v___x_568_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref_known(v_e_467_, 1);
v_a_580_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_565_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_565_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
case 4:
{
lean_object* v_declName_588_; 
v_declName_588_ = lean_ctor_get(v_e_467_, 0);
lean_inc(v_declName_588_);
lean_dec_ref_known(v_e_467_, 2);
if (lean_obj_tag(v_declName_588_) == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1));
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
else
{
uint64_t v_hash_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_hash_591_ = lean_ctor_get_uint64(v_declName_588_, sizeof(void*)*2);
lean_dec(v_declName_588_);
v___x_592_ = lean_box_uint64(v_hash_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
case 5:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = l_Lean_Expr_getAppFn(v_e_467_);
v___x_595_ = l_Lean_Expr_isMVar(v___x_594_);
if (v___x_595_ == 0)
{
v___y_543_ = v___x_594_;
v___y_544_ = v_a_468_;
v___y_545_ = v_a_469_;
v___y_546_ = v_a_470_;
v___y_547_ = v_a_471_;
v___y_548_ = v_a_472_;
v___y_549_ = v_a_473_;
goto v___jp_542_;
}
else
{
lean_object* v___x_596_; 
lean_inc_ref(v_e_467_);
v___x_596_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v_e_467_, v_a_471_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; uint8_t v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = lean_expr_eqv(v_a_597_, v_e_467_);
if (v___x_598_ == 0)
{
lean_dec_ref(v___x_594_);
lean_dec_ref_known(v_e_467_, 2);
v_e_467_ = v_a_597_;
goto _start;
}
else
{
lean_dec(v_a_597_);
v___y_543_ = v___x_594_;
v___y_544_ = v_a_468_;
v___y_545_ = v_a_469_;
v___y_546_ = v_a_470_;
v___y_547_ = v_a_471_;
v___y_548_ = v_a_472_;
v___y_549_ = v_a_473_;
goto v___jp_542_;
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v___x_594_);
lean_dec_ref_known(v_e_467_, 2);
v_a_600_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_596_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_608_; lean_object* v_body_609_; 
v_binderType_608_ = lean_ctor_get(v_e_467_, 1);
lean_inc_ref(v_binderType_608_);
v_body_609_ = lean_ctor_get(v_e_467_, 2);
lean_inc_ref(v_body_609_);
lean_dec_ref_known(v_e_467_, 3);
v_t_476_ = v_binderType_608_;
v_b_477_ = v_body_609_;
v___y_478_ = v_a_468_;
v___y_479_ = v_a_469_;
v___y_480_ = v_a_470_;
v___y_481_ = v_a_471_;
v___y_482_ = v_a_472_;
v___y_483_ = v_a_473_;
goto v___jp_475_;
}
case 7:
{
lean_object* v_binderType_610_; lean_object* v_body_611_; 
v_binderType_610_ = lean_ctor_get(v_e_467_, 1);
lean_inc_ref(v_binderType_610_);
v_body_611_ = lean_ctor_get(v_e_467_, 2);
lean_inc_ref(v_body_611_);
lean_dec_ref_known(v_e_467_, 3);
v_t_476_ = v_binderType_610_;
v_b_477_ = v_body_611_;
v___y_478_ = v_a_468_;
v___y_479_ = v_a_469_;
v___y_480_ = v_a_470_;
v___y_481_ = v_a_471_;
v___y_482_ = v_a_472_;
v___y_483_ = v_a_473_;
goto v___jp_475_;
}
case 8:
{
lean_object* v_value_612_; lean_object* v_body_613_; lean_object* v___x_614_; 
v_value_612_ = lean_ctor_get(v_e_467_, 2);
lean_inc_ref(v_value_612_);
v_body_613_ = lean_ctor_get(v_e_467_, 3);
lean_inc_ref(v_body_613_);
lean_dec_ref_known(v_e_467_, 4);
v___x_614_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_612_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_613_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_628_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_628_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_628_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_628_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint64_t v___x_621_; uint64_t v___x_622_; uint64_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_621_ = lean_unbox_uint64(v_a_615_);
lean_dec(v_a_615_);
v___x_622_ = lean_unbox_uint64(v_a_617_);
lean_dec(v_a_617_);
v___x_623_ = lean_uint64_mix_hash(v___x_621_, v___x_622_);
v___x_624_ = lean_box_uint64(v___x_623_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_624_);
v___x_626_ = v___x_619_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_dec(v_a_615_);
return v___x_616_;
}
}
else
{
lean_dec_ref(v_body_613_);
return v___x_614_;
}
}
case 10:
{
lean_object* v_expr_629_; lean_object* v___x_630_; 
v_expr_629_ = lean_ctor_get(v_e_467_, 1);
lean_inc_ref(v_expr_629_);
v___x_630_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_629_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; uint64_t v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = lean_unbox_uint64(v_a_631_);
lean_dec(v_a_631_);
v_key_507_ = v___x_632_;
v___y_508_ = v_a_469_;
goto v___jp_506_;
}
else
{
lean_dec_ref_known(v_e_467_, 2);
return v___x_630_;
}
}
case 11:
{
lean_object* v_idx_633_; lean_object* v_struct_634_; lean_object* v___x_635_; 
v_idx_633_ = lean_ctor_get(v_e_467_, 1);
lean_inc(v_idx_633_);
v_struct_634_ = lean_ctor_get(v_e_467_, 2);
lean_inc_ref(v_struct_634_);
lean_dec_ref_known(v_e_467_, 3);
v___x_635_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_634_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_647_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_647_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_647_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_647_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint64_t v___x_640_; uint64_t v___x_641_; uint64_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_640_ = lean_uint64_of_nat(v_idx_633_);
lean_dec(v_idx_633_);
v___x_641_ = lean_unbox_uint64(v_a_636_);
lean_dec(v_a_636_);
v___x_642_ = lean_uint64_mix_hash(v___x_640_, v___x_641_);
v___x_643_ = lean_box_uint64(v___x_642_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_643_);
v___x_645_ = v___x_638_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_dec(v_idx_633_);
return v___x_635_;
}
}
default: 
{
uint64_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = l_Lean_Expr_hash(v_e_467_);
lean_dec_ref(v_e_467_);
v___x_649_ = lean_box_uint64(v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(lean_object* v_upperBound_665_, lean_object* v_info_666_, lean_object* v___x_667_, lean_object* v_e_668_, lean_object* v_a_669_, uint64_t v_b_670_, uint8_t v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint64_t v_a_679_; uint8_t v___x_683_; 
v___x_683_ = lean_nat_dec_lt(v_a_669_, v_upperBound_665_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec(v_a_669_);
v___x_684_ = lean_box_uint64(v_b_670_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
else
{
lean_object* v_paramInfo_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_paramInfo_686_ = lean_ctor_get(v_info_666_, 0);
v___x_687_ = lean_array_get_size(v_paramInfo_686_);
v___x_688_ = lean_nat_dec_lt(v_a_669_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = lean_nat_sub(v___x_667_, v_a_669_);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v___x_689_, v___x_690_);
lean_dec(v___x_689_);
v___x_692_ = l_Lean_Expr_getRevArg_x21(v_e_668_, v___x_691_);
v___x_693_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_692_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; uint64_t v___x_695_; uint64_t v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_unbox_uint64(v_a_694_);
lean_dec(v_a_694_);
v___x_696_ = lean_uint64_mix_hash(v_b_670_, v___x_695_);
v_a_679_ = v___x_696_;
goto v___jp_678_;
}
else
{
lean_dec(v_a_669_);
return v___x_693_;
}
}
else
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_array_fget_borrowed(v_paramInfo_686_, v_a_669_);
v___x_698_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_697_);
if (v___x_698_ == 0)
{
v_a_679_ = v_b_670_;
goto v___jp_678_;
}
else
{
uint8_t v_isProp_699_; 
v_isProp_699_ = lean_ctor_get_uint8(v___x_697_, sizeof(void*)*1 + 2);
if (v_isProp_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_700_ = lean_nat_sub(v___x_667_, v_a_669_);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_sub(v___x_700_, v___x_701_);
lean_dec(v___x_700_);
v___x_703_ = l_Lean_Expr_getRevArg_x21(v_e_668_, v___x_702_);
v___x_704_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_703_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; uint64_t v___x_706_; uint64_t v___x_707_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_unbox_uint64(v_a_705_);
lean_dec(v_a_705_);
v___x_707_ = lean_uint64_mix_hash(v_b_670_, v___x_706_);
v_a_679_ = v___x_707_;
goto v___jp_678_;
}
else
{
lean_dec(v_a_669_);
return v___x_704_;
}
}
else
{
v_a_679_ = v_b_670_;
goto v___jp_678_;
}
}
}
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_a_669_, v___x_680_);
lean_dec(v_a_669_);
v_a_669_ = v___x_681_;
v_b_670_ = v_a_679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg___boxed(lean_object* v_upperBound_708_, lean_object* v_info_709_, lean_object* v___x_710_, lean_object* v_e_711_, lean_object* v_a_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
uint64_t v_b_boxed_721_; uint8_t v___y_13851__boxed_722_; lean_object* v_res_723_; 
v_b_boxed_721_ = lean_unbox_uint64(v_b_713_);
lean_dec_ref(v_b_713_);
v___y_13851__boxed_722_ = lean_unbox(v___y_714_);
v_res_723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v_upperBound_708_, v_info_709_, v___x_710_, v_e_711_, v_a_712_, v_b_boxed_721_, v___y_13851__boxed_722_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v_e_711_);
lean_dec(v___x_710_);
lean_dec_ref(v_info_709_);
lean_dec(v_upperBound_708_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
uint8_t v_a_boxed_732_; lean_object* v_res_733_; 
v_a_boxed_732_ = lean_unbox(v_a_725_);
v_res_733_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_724_, v_a_boxed_732_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* v_00_u03b2_734_, lean_object* v_m_735_, lean_object* v_a_736_, lean_object* v_b_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_m_735_, v_a_736_, v_b_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(lean_object* v_upperBound_739_, lean_object* v_info_740_, lean_object* v___x_741_, lean_object* v_e_742_, lean_object* v_inst_743_, lean_object* v_R_744_, lean_object* v_a_745_, uint64_t v_b_746_, lean_object* v_c_747_, uint8_t v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___redArg(v_upperBound_739_, v_info_740_, v___x_741_, v_e_742_, v_a_745_, v_b_746_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2___boxed(lean_object* v_upperBound_756_, lean_object* v_info_757_, lean_object* v___x_758_, lean_object* v_e_759_, lean_object* v_inst_760_, lean_object* v_R_761_, lean_object* v_a_762_, lean_object* v_b_763_, lean_object* v_c_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
uint64_t v_b_boxed_772_; uint8_t v___y_14341__boxed_773_; lean_object* v_res_774_; 
v_b_boxed_772_ = lean_unbox_uint64(v_b_763_);
lean_dec_ref(v_b_763_);
v___y_14341__boxed_773_ = lean_unbox(v___y_765_);
v_res_774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__2(v_upperBound_756_, v_info_757_, v___x_758_, v_e_759_, v_inst_760_, v_R_761_, v_a_762_, v_b_boxed_772_, v_c_764_, v___y_14341__boxed_773_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v_e_759_);
lean_dec(v___x_758_);
lean_dec_ref(v_info_757_);
lean_dec(v_upperBound_756_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(lean_object* v_00_u03b2_775_, lean_object* v_m_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___redArg(v_m_776_, v_a_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3___boxed(lean_object* v_00_u03b2_779_, lean_object* v_m_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3(v_00_u03b2_779_, v_m_780_, v_a_781_);
lean_dec_ref(v_a_781_);
lean_dec_ref(v_m_780_);
return v_res_782_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(lean_object* v_00_u03b2_783_, lean_object* v_a_784_, lean_object* v_x_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___redArg(v_a_784_, v_x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0___boxed(lean_object* v_00_u03b2_787_, lean_object* v_a_788_, lean_object* v_x_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__0(v_00_u03b2_787_, v_a_788_, v_x_789_);
lean_dec(v_x_789_);
lean_dec_ref(v_a_788_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1(lean_object* v_00_u03b2_792_, lean_object* v_data_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1___redArg(v_data_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_b_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__2___redArg(v_a_796_, v_b_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6(lean_object* v_00_u03b2_800_, lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___redArg(v_a_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6___boxed(lean_object* v_00_u03b2_804_, lean_object* v_a_805_, lean_object* v_x_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__3_spec__6(v_00_u03b2_804_, v_a_805_, v_x_806_);
lean_dec(v_x_806_);
lean_dec_ref(v_a_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_808_, lean_object* v_i_809_, lean_object* v_source_810_, lean_object* v_target_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3___redArg(v_i_809_, v_source_810_, v_target_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0_spec__1_spec__3_spec__6___redArg(v_x_814_, v_x_815_);
return v___x_816_;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_817_; lean_object* v___f_818_; 
v___x_817_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_818_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_818_, 0, v___x_817_);
return v___f_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t v_k_820_, lean_object* v_____do__lift_821_){
_start:
{
lean_object* v_keyToExprs_822_; lean_object* v___f_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_keyToExprs_822_ = lean_ctor_get(v_____do__lift_821_, 1);
v___f_823_ = lean_obj_once(&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0, &l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__0);
v___f_824_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___closed__1));
v___x_825_ = lean_box_uint64(v_k_820_);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_823_, v___f_824_, v_keyToExprs_822_, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* v_k_827_, lean_object* v_____do__lift_828_){
_start:
{
uint64_t v_k_boxed_829_; lean_object* v_res_830_; 
v_k_boxed_829_ = lean_unbox_uint64(v_k_827_);
lean_dec_ref(v_k_827_);
v_res_830_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v_k_boxed_829_, v_____do__lift_828_);
lean_dec_ref(v_____do__lift_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(uint64_t v_a_831_, lean_object* v_x_832_){
_start:
{
if (lean_obj_tag(v_x_832_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = lean_box(0);
return v___x_833_;
}
else
{
lean_object* v_key_834_; lean_object* v_value_835_; lean_object* v_tail_836_; uint64_t v___x_837_; uint8_t v___x_838_; 
v_key_834_ = lean_ctor_get(v_x_832_, 0);
v_value_835_ = lean_ctor_get(v_x_832_, 1);
v_tail_836_ = lean_ctor_get(v_x_832_, 2);
v___x_837_ = lean_unbox_uint64(v_key_834_);
v___x_838_ = lean_uint64_dec_eq(v___x_837_, v_a_831_);
if (v___x_838_ == 0)
{
v_x_832_ = v_tail_836_;
goto _start;
}
else
{
lean_object* v___x_840_; 
lean_inc(v_value_835_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_value_835_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg___boxed(lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
uint64_t v_a_boxed_843_; lean_object* v_res_844_; 
v_a_boxed_843_ = lean_unbox_uint64(v_a_841_);
lean_dec_ref(v_a_841_);
v_res_844_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_boxed_843_, v_x_842_);
lean_dec(v_x_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object* v_m_845_, uint64_t v_a_846_){
_start:
{
lean_object* v_buckets_847_; lean_object* v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v_fold_851_; uint64_t v___x_852_; uint64_t v___x_853_; uint64_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_buckets_847_ = lean_ctor_get(v_m_845_, 1);
v___x_848_ = lean_array_get_size(v_buckets_847_);
v___x_849_ = 32ULL;
v___x_850_ = lean_uint64_shift_right(v_a_846_, v___x_849_);
v_fold_851_ = lean_uint64_xor(v_a_846_, v___x_850_);
v___x_852_ = 16ULL;
v___x_853_ = lean_uint64_shift_right(v_fold_851_, v___x_852_);
v___x_854_ = lean_uint64_xor(v_fold_851_, v___x_853_);
v___x_855_ = lean_uint64_to_usize(v___x_854_);
v___x_856_ = lean_usize_of_nat(v___x_848_);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_sub(v___x_856_, v___x_857_);
v___x_859_ = lean_usize_land(v___x_855_, v___x_858_);
v___x_860_ = lean_array_uget_borrowed(v_buckets_847_, v___x_859_);
v___x_861_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_846_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* v_m_862_, lean_object* v_a_863_){
_start:
{
uint64_t v_a_boxed_864_; lean_object* v_res_865_; 
v_a_boxed_864_ = lean_unbox_uint64(v_a_863_);
lean_dec_ref(v_a_863_);
v_res_865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_862_, v_a_boxed_864_);
lean_dec_ref(v_m_862_);
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(uint64_t v_a_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_867_) == 0)
{
uint8_t v___x_868_; 
v___x_868_ = 0;
return v___x_868_;
}
else
{
lean_object* v_key_869_; lean_object* v_tail_870_; uint64_t v___x_871_; uint8_t v___x_872_; 
v_key_869_ = lean_ctor_get(v_x_867_, 0);
v_tail_870_ = lean_ctor_get(v_x_867_, 2);
v___x_871_ = lean_unbox_uint64(v_key_869_);
v___x_872_ = lean_uint64_dec_eq(v___x_871_, v_a_866_);
if (v___x_872_ == 0)
{
v_x_867_ = v_tail_870_;
goto _start;
}
else
{
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg___boxed(lean_object* v_a_874_, lean_object* v_x_875_){
_start:
{
uint64_t v_a_boxed_876_; uint8_t v_res_877_; lean_object* v_r_878_; 
v_a_boxed_876_ = lean_unbox_uint64(v_a_874_);
lean_dec_ref(v_a_874_);
v_res_877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_boxed_876_, v_x_875_);
lean_dec(v_x_875_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(uint64_t v_a_879_, lean_object* v_b_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_dec(v_b_880_);
return v_x_881_;
}
else
{
lean_object* v_key_882_; lean_object* v_value_883_; lean_object* v_tail_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_898_; 
v_key_882_ = lean_ctor_get(v_x_881_, 0);
v_value_883_ = lean_ctor_get(v_x_881_, 1);
v_tail_884_ = lean_ctor_get(v_x_881_, 2);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_898_ == 0)
{
v___x_886_ = v_x_881_;
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_tail_884_);
lean_inc(v_value_883_);
lean_inc(v_key_882_);
lean_dec(v_x_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
uint64_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_unbox_uint64(v_key_882_);
v___x_889_ = lean_uint64_dec_eq(v___x_888_, v_a_879_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_879_, v_b_880_, v_tail_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 2, v___x_890_);
v___x_892_ = v___x_886_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_key_882_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_value_883_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_896_; 
lean_dec(v_value_883_);
lean_dec(v_key_882_);
v___x_894_ = lean_box_uint64(v_a_879_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v_b_880_);
lean_ctor_set(v___x_886_, 0, v___x_894_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_b_880_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_tail_884_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg___boxed(lean_object* v_a_899_, lean_object* v_b_900_, lean_object* v_x_901_){
_start:
{
uint64_t v_a_boxed_902_; lean_object* v_res_903_; 
v_a_boxed_902_ = lean_unbox_uint64(v_a_899_);
lean_dec_ref(v_a_899_);
v_res_903_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_boxed_902_, v_b_900_, v_x_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
return v_x_904_;
}
else
{
lean_object* v_key_906_; lean_object* v_value_907_; lean_object* v_tail_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_932_; 
v_key_906_ = lean_ctor_get(v_x_905_, 0);
v_value_907_ = lean_ctor_get(v_x_905_, 1);
v_tail_908_ = lean_ctor_get(v_x_905_, 2);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_905_);
if (v_isSharedCheck_932_ == 0)
{
v___x_910_ = v_x_905_;
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_tail_908_);
lean_inc(v_value_907_);
lean_inc(v_key_906_);
lean_dec(v_x_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v_fold_917_; uint64_t v___x_918_; uint64_t v___x_919_; uint64_t v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_912_ = lean_array_get_size(v_x_904_);
v___x_913_ = 32ULL;
v___x_914_ = lean_unbox_uint64(v_key_906_);
v___x_915_ = lean_uint64_shift_right(v___x_914_, v___x_913_);
v___x_916_ = lean_unbox_uint64(v_key_906_);
v_fold_917_ = lean_uint64_xor(v___x_916_, v___x_915_);
v___x_918_ = 16ULL;
v___x_919_ = lean_uint64_shift_right(v_fold_917_, v___x_918_);
v___x_920_ = lean_uint64_xor(v_fold_917_, v___x_919_);
v___x_921_ = lean_uint64_to_usize(v___x_920_);
v___x_922_ = lean_usize_of_nat(v___x_912_);
v___x_923_ = ((size_t)1ULL);
v___x_924_ = lean_usize_sub(v___x_922_, v___x_923_);
v___x_925_ = lean_usize_land(v___x_921_, v___x_924_);
v___x_926_ = lean_array_uget_borrowed(v_x_904_, v___x_925_);
lean_inc(v___x_926_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 2, v___x_926_);
v___x_928_ = v___x_910_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_key_906_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_value_907_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v___x_926_);
v___x_928_ = v_reuseFailAlloc_931_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = lean_array_uset(v_x_904_, v___x_925_, v___x_928_);
v_x_904_ = v___x_929_;
v_x_905_ = v_tail_908_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(lean_object* v_i_933_, lean_object* v_source_934_, lean_object* v_target_935_){
_start:
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = lean_array_get_size(v_source_934_);
v___x_937_ = lean_nat_dec_lt(v_i_933_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v_source_934_);
lean_dec(v_i_933_);
return v_target_935_;
}
else
{
lean_object* v_es_938_; lean_object* v___x_939_; lean_object* v_source_940_; lean_object* v_target_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_es_938_ = lean_array_fget(v_source_934_, v_i_933_);
v___x_939_ = lean_box(0);
v_source_940_ = lean_array_fset(v_source_934_, v_i_933_, v___x_939_);
v_target_941_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(v_target_935_, v_es_938_);
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_i_933_, v___x_942_);
lean_dec(v_i_933_);
v_i_933_ = v___x_943_;
v_source_934_ = v_source_940_;
v_target_935_ = v_target_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(lean_object* v_data_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_nbuckets_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_946_ = lean_array_get_size(v_data_945_);
v___x_947_ = lean_unsigned_to_nat(2u);
v_nbuckets_948_ = lean_nat_mul(v___x_946_, v___x_947_);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_box(0);
v___x_951_ = lean_mk_array(v_nbuckets_948_, v___x_950_);
v___x_952_ = lean_array_propagate_mark(v_data_945_, v___x_951_);
v___x_953_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(v___x_949_, v_data_945_, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(lean_object* v_m_954_, uint64_t v_a_955_, lean_object* v_b_956_){
_start:
{
lean_object* v_size_957_; lean_object* v_buckets_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1001_; 
v_size_957_ = lean_ctor_get(v_m_954_, 0);
v_buckets_958_ = lean_ctor_get(v_m_954_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_m_954_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_960_ = v_m_954_;
v_isShared_961_ = v_isSharedCheck_1001_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_buckets_958_);
lean_inc(v_size_957_);
lean_dec(v_m_954_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1001_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v_fold_965_; uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; lean_object* v_bkt_974_; uint8_t v___x_975_; 
v___x_962_ = lean_array_get_size(v_buckets_958_);
v___x_963_ = 32ULL;
v___x_964_ = lean_uint64_shift_right(v_a_955_, v___x_963_);
v_fold_965_ = lean_uint64_xor(v_a_955_, v___x_964_);
v___x_966_ = 16ULL;
v___x_967_ = lean_uint64_shift_right(v_fold_965_, v___x_966_);
v___x_968_ = lean_uint64_xor(v_fold_965_, v___x_967_);
v___x_969_ = lean_uint64_to_usize(v___x_968_);
v___x_970_ = lean_usize_of_nat(v___x_962_);
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_sub(v___x_970_, v___x_971_);
v___x_973_ = lean_usize_land(v___x_969_, v___x_972_);
v_bkt_974_ = lean_array_uget_borrowed(v_buckets_958_, v___x_973_);
v___x_975_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_955_, v_bkt_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v_size_x27_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_buckets_x27_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_976_ = lean_unsigned_to_nat(1u);
v_size_x27_977_ = lean_nat_add(v_size_957_, v___x_976_);
lean_dec(v_size_957_);
v___x_978_ = lean_box_uint64(v_a_955_);
lean_inc(v_bkt_974_);
v___x_979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_b_956_);
lean_ctor_set(v___x_979_, 2, v_bkt_974_);
v_buckets_x27_980_ = lean_array_uset(v_buckets_958_, v___x_973_, v___x_979_);
v___x_981_ = lean_unsigned_to_nat(4u);
v___x_982_ = lean_nat_mul(v_size_x27_977_, v___x_981_);
v___x_983_ = lean_unsigned_to_nat(3u);
v___x_984_ = lean_nat_div(v___x_982_, v___x_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_array_get_size(v_buckets_x27_980_);
v___x_986_ = lean_nat_dec_le(v___x_984_, v___x_985_);
lean_dec(v___x_984_);
if (v___x_986_ == 0)
{
lean_object* v_val_987_; lean_object* v___x_989_; 
v_val_987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(v_buckets_x27_980_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_val_987_);
lean_ctor_set(v___x_960_, 0, v_size_x27_977_);
v___x_989_ = v___x_960_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_size_x27_977_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_val_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
else
{
lean_object* v___x_992_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_buckets_x27_980_);
lean_ctor_set(v___x_960_, 0, v_size_x27_977_);
v___x_992_ = v___x_960_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_size_x27_977_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_buckets_x27_980_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v___x_994_; lean_object* v_buckets_x27_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_inc(v_bkt_974_);
v___x_994_ = lean_box(0);
v_buckets_x27_995_ = lean_array_uset(v_buckets_958_, v___x_973_, v___x_994_);
v___x_996_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_955_, v_b_956_, v_bkt_974_);
v___x_997_ = lean_array_uset(v_buckets_x27_995_, v___x_973_, v___x_996_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___x_997_);
v___x_999_ = v___x_960_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_size_957_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg___boxed(lean_object* v_m_1002_, lean_object* v_a_1003_, lean_object* v_b_1004_){
_start:
{
uint64_t v_a_boxed_1005_; lean_object* v_res_1006_; 
v_a_boxed_1005_ = lean_unbox_uint64(v_a_1003_);
lean_dec_ref(v_a_1003_);
v_res_1006_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1002_, v_a_boxed_1005_, v_b_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* v_e_1010_, lean_object* v_as_x27_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
if (lean_obj_tag(v_as_x27_1011_) == 0)
{
lean_object* v___x_1018_; 
lean_dec_ref(v_e_1010_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1012_);
return v___x_1018_;
}
else
{
lean_object* v_head_1019_; lean_object* v_tail_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec_ref(v_b_1012_);
v_head_1019_ = lean_ctor_get(v_as_x27_1011_, 0);
v_tail_1020_ = lean_ctor_get(v_as_x27_1011_, 1);
v___x_1021_ = lean_box(0);
v___x_1022_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
lean_inc(v_head_1019_);
lean_inc_ref(v_e_1010_);
v___x_1023_ = l_Lean_Meta_isExprDefEq(v_e_1010_, v_head_1019_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1035_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
uint8_t v___x_1028_; 
v___x_1028_ = lean_unbox(v_a_1024_);
lean_dec(v_a_1024_);
if (v___x_1028_ == 0)
{
lean_del_object(v___x_1026_);
v_as_x27_1011_ = v_tail_1020_;
v_b_1012_ = v___x_1022_;
goto _start;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec_ref(v_e_1010_);
lean_inc(v_head_1019_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_head_1019_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1021_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1031_);
v___x_1033_ = v___x_1026_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_e_1010_);
v_a_1036_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1023_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1023_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object* v_e_1044_, lean_object* v_as_x27_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1044_, v_as_x27_1045_, v_b_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_as_x27_1045_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* v_e_1053_, uint8_t v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
lean_inc_ref(v_e_1053_);
v___x_1061_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1199_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1199_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1199_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v_keyToExprs_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1197_; 
v___x_1066_ = lean_st_ref_get(v_a_1055_);
v_keyToExprs_1067_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1066_, 0);
lean_dec(v_unused_1198_);
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1197_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_keyToExprs_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1197_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
uint64_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unbox_uint64(v_a_1062_);
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_keyToExprs_1067_, v___x_1071_);
lean_dec_ref(v_keyToExprs_1067_);
if (lean_obj_tag(v___x_1072_) == 1)
{
lean_object* v_val_1073_; lean_object* v___x_1074_; uint8_t v_transparency_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
lean_del_object(v___x_1069_);
lean_del_object(v___x_1064_);
v_val_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = l_Lean_Meta_Context_config(v_a_1056_);
v_transparency_1075_ = lean_ctor_get_uint8(v___x_1074_, 9);
lean_dec_ref(v___x_1074_);
v___x_1076_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___closed__0));
v___x_1077_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1075_, v_a_1054_);
if (v___x_1077_ == 0)
{
lean_object* v_keyedConfig_1078_; uint8_t v_trackZetaDelta_1079_; lean_object* v_zetaDeltaSet_1080_; lean_object* v_lctx_1081_; lean_object* v_localInstances_1082_; lean_object* v_defEqCtx_x3f_1083_; lean_object* v_synthPendingDepth_1084_; lean_object* v_customCanUnfoldPredicate_x3f_1085_; uint8_t v_univApprox_1086_; uint8_t v_inTypeClassResolution_1087_; uint8_t v_cacheInferType_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_keyedConfig_1078_ = lean_ctor_get(v_a_1056_, 0);
v_trackZetaDelta_1079_ = lean_ctor_get_uint8(v_a_1056_, sizeof(void*)*7);
v_zetaDeltaSet_1080_ = lean_ctor_get(v_a_1056_, 1);
v_lctx_1081_ = lean_ctor_get(v_a_1056_, 2);
v_localInstances_1082_ = lean_ctor_get(v_a_1056_, 3);
v_defEqCtx_x3f_1083_ = lean_ctor_get(v_a_1056_, 4);
v_synthPendingDepth_1084_ = lean_ctor_get(v_a_1056_, 5);
v_customCanUnfoldPredicate_x3f_1085_ = lean_ctor_get(v_a_1056_, 6);
v_univApprox_1086_ = lean_ctor_get_uint8(v_a_1056_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1087_ = lean_ctor_get_uint8(v_a_1056_, sizeof(void*)*7 + 2);
v_cacheInferType_1088_ = lean_ctor_get_uint8(v_a_1056_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1078_);
v___x_1089_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_a_1054_, v_keyedConfig_1078_);
lean_inc(v_customCanUnfoldPredicate_x3f_1085_);
lean_inc(v_synthPendingDepth_1084_);
lean_inc(v_defEqCtx_x3f_1083_);
lean_inc_ref(v_localInstances_1082_);
lean_inc_ref(v_lctx_1081_);
lean_inc(v_zetaDeltaSet_1080_);
v___x_1090_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_zetaDeltaSet_1080_);
lean_ctor_set(v___x_1090_, 2, v_lctx_1081_);
lean_ctor_set(v___x_1090_, 3, v_localInstances_1082_);
lean_ctor_set(v___x_1090_, 4, v_defEqCtx_x3f_1083_);
lean_ctor_set(v___x_1090_, 5, v_synthPendingDepth_1084_);
lean_ctor_set(v___x_1090_, 6, v_customCanUnfoldPredicate_x3f_1085_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7, v_trackZetaDelta_1079_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7 + 1, v_univApprox_1086_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1087_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*7 + 3, v_cacheInferType_1088_);
lean_inc_ref(v_e_1053_);
v___x_1091_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1053_, v_val_1073_, v___x_1076_, v___x_1090_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec_ref_known(v___x_1090_, 7);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1125_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1125_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1125_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_fst_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1123_; 
v_fst_1096_ = lean_ctor_get(v_a_1092_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_a_1092_, 1);
lean_dec(v_unused_1124_);
v___x_1098_ = v_a_1092_;
v_isShared_1099_ = v_isSharedCheck_1123_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_fst_1096_);
lean_dec(v_a_1092_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1123_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
if (lean_obj_tag(v_fst_1096_) == 0)
{
lean_object* v___x_1100_; lean_object* v_cache_1101_; lean_object* v_keyToExprs_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1118_; 
v___x_1100_ = lean_st_ref_take(v_a_1055_);
v_cache_1101_ = lean_ctor_get(v___x_1100_, 0);
v_keyToExprs_1102_ = lean_ctor_get(v___x_1100_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1104_ = v___x_1100_;
v_isShared_1105_ = v_isSharedCheck_1118_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_keyToExprs_1102_);
lean_inc(v_cache_1101_);
lean_dec(v___x_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1118_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
lean_inc_ref(v_e_1053_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 1);
lean_ctor_set(v___x_1098_, 1, v_val_1073_);
lean_ctor_set(v___x_1098_, 0, v_e_1053_);
v___x_1107_ = v___x_1098_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_e_1053_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_val_1073_);
v___x_1107_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
uint64_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = lean_unbox_uint64(v_a_1062_);
lean_dec(v_a_1062_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1102_, v___x_1108_, v___x_1107_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v___x_1109_);
v___x_1111_ = v___x_1104_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_cache_1101_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_st_ref_put(v_a_1055_, v___x_1111_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_e_1053_);
v___x_1114_ = v___x_1094_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_e_1053_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
else
{
lean_object* v_val_1119_; lean_object* v___x_1121_; 
lean_del_object(v___x_1098_);
lean_dec(v_val_1073_);
lean_dec(v_a_1062_);
lean_dec_ref(v_e_1053_);
v_val_1119_ = lean_ctor_get(v_fst_1096_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v_fst_1096_, 1);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_val_1119_);
v___x_1121_ = v___x_1094_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_val_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_val_1073_);
lean_dec(v_a_1062_);
lean_dec_ref(v_e_1053_);
v_a_1126_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1091_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1091_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___x_1134_; 
lean_inc_ref(v_e_1053_);
v___x_1134_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1053_, v_val_1073_, v___x_1076_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1168_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1168_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1168_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_fst_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1166_; 
v_fst_1139_ = lean_ctor_get(v_a_1135_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_a_1135_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v_a_1135_, 1);
lean_dec(v_unused_1167_);
v___x_1141_ = v_a_1135_;
v_isShared_1142_ = v_isSharedCheck_1166_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_fst_1139_);
lean_dec(v_a_1135_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1166_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
if (lean_obj_tag(v_fst_1139_) == 0)
{
lean_object* v___x_1143_; lean_object* v_cache_1144_; lean_object* v_keyToExprs_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1161_; 
v___x_1143_ = lean_st_ref_take(v_a_1055_);
v_cache_1144_ = lean_ctor_get(v___x_1143_, 0);
v_keyToExprs_1145_ = lean_ctor_get(v___x_1143_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1161_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_keyToExprs_1145_);
lean_inc(v_cache_1144_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1161_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
lean_inc_ref(v_e_1053_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 1, v_val_1073_);
lean_ctor_set(v___x_1141_, 0, v_e_1053_);
v___x_1150_ = v___x_1141_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_e_1053_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_val_1073_);
v___x_1150_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
uint64_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1151_ = lean_unbox_uint64(v_a_1062_);
lean_dec(v_a_1062_);
v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1145_, v___x_1151_, v___x_1150_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1152_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_cache_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_st_ref_put(v_a_1055_, v___x_1154_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_e_1053_);
v___x_1157_ = v___x_1137_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_e_1053_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
else
{
lean_object* v_val_1162_; lean_object* v___x_1164_; 
lean_del_object(v___x_1141_);
lean_dec(v_val_1073_);
lean_dec(v_a_1062_);
lean_dec_ref(v_e_1053_);
v_val_1162_ = lean_ctor_get(v_fst_1139_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v_fst_1139_, 1);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_val_1162_);
v___x_1164_ = v___x_1137_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_val_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_val_1073_);
lean_dec(v_a_1062_);
lean_dec_ref(v_e_1053_);
v_a_1169_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1134_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1134_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v_cache_1178_; lean_object* v_keyToExprs_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v___x_1072_);
v___x_1177_ = lean_st_ref_take(v_a_1055_);
v_cache_1178_ = lean_ctor_get(v___x_1177_, 0);
v_keyToExprs_1179_ = lean_ctor_get(v___x_1177_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1181_ = v___x_1177_;
v_isShared_1182_ = v_isSharedCheck_1196_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_keyToExprs_1179_);
lean_inc(v_cache_1178_);
lean_dec(v___x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1196_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_box(0);
lean_inc_ref(v_e_1053_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 1);
lean_ctor_set(v___x_1069_, 1, v___x_1183_);
lean_ctor_set(v___x_1069_, 0, v_e_1053_);
v___x_1185_ = v___x_1069_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_e_1053_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
uint64_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1186_ = lean_unbox_uint64(v_a_1062_);
lean_dec(v_a_1062_);
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_keyToExprs_1179_, v___x_1186_, v___x_1185_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1187_);
v___x_1189_ = v___x_1181_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_cache_1178_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_st_ref_put(v_a_1055_, v___x_1189_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v_e_1053_);
v___x_1192_ = v___x_1064_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_e_1053_);
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
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_e_1053_);
v_a_1200_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1061_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1061_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* v_e_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
uint8_t v_a_boxed_1216_; lean_object* v_res_1217_; 
v_a_boxed_1216_ = lean_unbox(v_a_1209_);
v_res_1217_ = l_Lean_Meta_Canonicalizer_canon(v_e_1208_, v_a_boxed_1216_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object* v_00_u03b2_1218_, lean_object* v_m_1219_, uint64_t v_a_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_m_1219_, v_a_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* v_00_u03b2_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
uint64_t v_a_boxed_1225_; lean_object* v_res_1226_; 
v_a_boxed_1225_ = lean_unbox_uint64(v_a_1224_);
lean_dec_ref(v_a_1224_);
v_res_1226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0(v_00_u03b2_1222_, v_m_1223_, v_a_boxed_1225_);
lean_dec_ref(v_m_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object* v_e_1227_, lean_object* v_as_1228_, lean_object* v_as_x27_1229_, lean_object* v_b_1230_, lean_object* v_a_1231_, uint8_t v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_e_1227_, v_as_x27_1229_, v_b_1230_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object* v_e_1240_, lean_object* v_as_1241_, lean_object* v_as_x27_1242_, lean_object* v_b_1243_, lean_object* v_a_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v___y_11178__boxed_1252_; lean_object* v_res_1253_; 
v___y_11178__boxed_1252_ = lean_unbox(v___y_1245_);
v_res_1253_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__1(v_e_1240_, v_as_1241_, v_as_x27_1242_, v_b_1243_, v_a_1244_, v___y_11178__boxed_1252_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v_as_x27_1242_);
lean_dec(v_as_1241_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(lean_object* v_00_u03b2_1254_, lean_object* v_m_1255_, uint64_t v_a_1256_, lean_object* v_b_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___redArg(v_m_1255_, v_a_1256_, v_b_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2___boxed(lean_object* v_00_u03b2_1259_, lean_object* v_m_1260_, lean_object* v_a_1261_, lean_object* v_b_1262_){
_start:
{
uint64_t v_a_boxed_1263_; lean_object* v_res_1264_; 
v_a_boxed_1263_ = lean_unbox_uint64(v_a_1261_);
lean_dec_ref(v_a_1261_);
v_res_1264_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2(v_00_u03b2_1259_, v_m_1260_, v_a_boxed_1263_, v_b_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(lean_object* v_00_u03b2_1265_, uint64_t v_a_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___redArg(v_a_1266_, v_x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1269_, lean_object* v_a_1270_, lean_object* v_x_1271_){
_start:
{
uint64_t v_a_boxed_1272_; lean_object* v_res_1273_; 
v_a_boxed_1272_ = lean_unbox_uint64(v_a_1270_);
lean_dec_ref(v_a_1270_);
v_res_1273_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Canonicalizer_canon_spec__0_spec__0(v_00_u03b2_1269_, v_a_boxed_1272_, v_x_1271_);
lean_dec(v_x_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(lean_object* v_00_u03b2_1274_, uint64_t v_a_1275_, lean_object* v_x_1276_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___redArg(v_a_1275_, v_x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1278_, lean_object* v_a_1279_, lean_object* v_x_1280_){
_start:
{
uint64_t v_a_boxed_1281_; uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_a_boxed_1281_ = lean_unbox_uint64(v_a_1279_);
lean_dec_ref(v_a_1279_);
v_res_1282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__3(v_00_u03b2_1278_, v_a_boxed_1281_, v_x_1280_);
lean_dec(v_x_1280_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4(lean_object* v_00_u03b2_1284_, lean_object* v_data_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4___redArg(v_data_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(lean_object* v_00_u03b2_1287_, uint64_t v_a_1288_, lean_object* v_b_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___redArg(v_a_1288_, v_b_1289_, v_x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1292_, lean_object* v_a_1293_, lean_object* v_b_1294_, lean_object* v_x_1295_){
_start:
{
uint64_t v_a_boxed_1296_; lean_object* v_res_1297_; 
v_a_boxed_1296_ = lean_unbox_uint64(v_a_1293_);
lean_dec_ref(v_a_1293_);
v_res_1297_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__5(v_00_u03b2_1292_, v_a_boxed_1296_, v_b_1294_, v_x_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1298_, lean_object* v_i_1299_, lean_object* v_source_1300_, lean_object* v_target_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5___redArg(v_i_1299_, v_source_1300_, v_target_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1304_, v_x_1305_);
return v___x_1306_;
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
