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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
static const lean_array_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value),((lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2 = (const lean_object*)&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(lean_object* v_a_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_box(0);
return v___x_150_;
}
else
{
lean_object* v_key_151_; lean_object* v_value_152_; lean_object* v_tail_153_; size_t v___x_154_; size_t v___x_155_; uint8_t v___x_156_; 
v_key_151_ = lean_ctor_get(v_x_149_, 0);
v_value_152_ = lean_ctor_get(v_x_149_, 1);
v_tail_153_ = lean_ctor_get(v_x_149_, 2);
v___x_154_ = lean_ptr_addr(v_key_151_);
v___x_155_ = lean_ptr_addr(v_a_148_);
v___x_156_ = lean_usize_dec_eq(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
v_x_149_ = v_tail_153_;
goto _start;
}
else
{
lean_object* v___x_158_; 
lean_inc(v_value_152_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v_value_152_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* v_a_159_, lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_159_, v_x_160_);
lean_dec(v_x_160_);
lean_dec_ref(v_a_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(lean_object* v_m_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_buckets_164_; lean_object* v___x_165_; size_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v_fold_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_buckets_164_ = lean_ctor_get(v_m_162_, 1);
v___x_165_ = lean_array_get_size(v_buckets_164_);
v___x_166_ = lean_ptr_addr(v_a_163_);
v___x_167_ = lean_usize_to_uint64(v___x_166_);
v___x_168_ = 32ULL;
v___x_169_ = lean_uint64_shift_right(v___x_167_, v___x_168_);
v_fold_170_ = lean_uint64_xor(v___x_167_, v___x_169_);
v___x_171_ = 16ULL;
v___x_172_ = lean_uint64_shift_right(v_fold_170_, v___x_171_);
v___x_173_ = lean_uint64_xor(v_fold_170_, v___x_172_);
v___x_174_ = lean_uint64_to_usize(v___x_173_);
v___x_175_ = lean_usize_of_nat(v___x_165_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_sub(v___x_175_, v___x_176_);
v___x_178_ = lean_usize_land(v___x_174_, v___x_177_);
v___x_179_ = lean_array_uget_borrowed(v_buckets_164_, v___x_178_);
v___x_180_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_163_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg___boxed(lean_object* v_m_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_181_, v_a_182_);
lean_dec_ref(v_a_182_);
lean_dec_ref(v_m_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object* v_e_184_, lean_object* v_____do__lift_185_){
_start:
{
lean_object* v_cache_186_; lean_object* v_buckets_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_cache_186_ = lean_ctor_get(v_____do__lift_185_, 0);
v_buckets_187_ = lean_ctor_get(v_cache_186_, 1);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_array_get_size(v_buckets_187_);
v___x_190_ = lean_nat_dec_lt(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_cache_186_, v_e_184_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object* v_e_193_, lean_object* v_____do__lift_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(v_e_193_, v_____do__lift_194_);
lean_dec_ref(v_____do__lift_194_);
lean_dec_ref(v_e_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(lean_object* v_00_u03b2_196_, lean_object* v_m_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(v_m_197_, v_a_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(lean_object* v_00_u03b2_200_, lean_object* v_m_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(v_00_u03b2_200_, v_m_201_, v_a_202_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_m_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(lean_object* v_00_u03b2_204_, lean_object* v_a_205_, lean_object* v_x_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___redArg(v_a_205_, v_x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_208_, lean_object* v_a_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0_spec__0(v_00_u03b2_208_, v_a_209_, v_x_210_);
lean_dec(v_x_210_);
lean_dec_ref(v_a_209_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(lean_object* v_a_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
uint8_t v___x_214_; 
v___x_214_ = 0;
return v___x_214_;
}
else
{
lean_object* v_key_215_; lean_object* v_tail_216_; size_t v___x_217_; size_t v___x_218_; uint8_t v___x_219_; 
v_key_215_ = lean_ctor_get(v_x_213_, 0);
v_tail_216_ = lean_ctor_get(v_x_213_, 2);
v___x_217_ = lean_ptr_addr(v_key_215_);
v___x_218_ = lean_ptr_addr(v_a_212_);
v___x_219_ = lean_usize_dec_eq(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
v_x_213_ = v_tail_216_;
goto _start;
}
else
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg___boxed(lean_object* v_a_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_221_, v_x_222_);
lean_dec(v_x_222_);
lean_dec_ref(v_a_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
return v_x_225_;
}
else
{
lean_object* v_key_227_; lean_object* v_value_228_; lean_object* v_tail_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_253_; 
v_key_227_ = lean_ctor_get(v_x_226_, 0);
v_value_228_ = lean_ctor_get(v_x_226_, 1);
v_tail_229_ = lean_ctor_get(v_x_226_, 2);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_253_ == 0)
{
v___x_231_ = v_x_226_;
v_isShared_232_ = v_isSharedCheck_253_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_tail_229_);
lean_inc(v_value_228_);
lean_inc(v_key_227_);
lean_dec(v_x_226_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_253_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; size_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v_fold_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_233_ = lean_array_get_size(v_x_225_);
v___x_234_ = lean_ptr_addr(v_key_227_);
v___x_235_ = lean_usize_to_uint64(v___x_234_);
v___x_236_ = 32ULL;
v___x_237_ = lean_uint64_shift_right(v___x_235_, v___x_236_);
v_fold_238_ = lean_uint64_xor(v___x_235_, v___x_237_);
v___x_239_ = 16ULL;
v___x_240_ = lean_uint64_shift_right(v_fold_238_, v___x_239_);
v___x_241_ = lean_uint64_xor(v_fold_238_, v___x_240_);
v___x_242_ = lean_uint64_to_usize(v___x_241_);
v___x_243_ = lean_usize_of_nat(v___x_233_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_sub(v___x_243_, v___x_244_);
v___x_246_ = lean_usize_land(v___x_242_, v___x_245_);
v___x_247_ = lean_array_uget_borrowed(v_x_225_, v___x_246_);
lean_inc(v___x_247_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 2, v___x_247_);
v___x_249_ = v___x_231_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_key_227_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_value_228_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v___x_247_);
v___x_249_ = v_reuseFailAlloc_252_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_array_uset(v_x_225_, v___x_246_, v___x_249_);
v_x_225_ = v___x_250_;
v_x_226_ = v_tail_229_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(lean_object* v_i_254_, lean_object* v_source_255_, lean_object* v_target_256_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_source_255_);
v___x_258_ = lean_nat_dec_lt(v_i_254_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec_ref(v_source_255_);
lean_dec(v_i_254_);
return v_target_256_;
}
else
{
lean_object* v_es_259_; lean_object* v___x_260_; lean_object* v_source_261_; lean_object* v_target_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_es_259_ = lean_array_fget(v_source_255_, v_i_254_);
v___x_260_ = lean_box(0);
v_source_261_ = lean_array_fset(v_source_255_, v_i_254_, v___x_260_);
v_target_262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_target_256_, v_es_259_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_i_254_, v___x_263_);
lean_dec(v_i_254_);
v_i_254_ = v___x_264_;
v_source_255_ = v_source_261_;
v_target_256_ = v_target_262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(lean_object* v_data_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_nbuckets_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_array_get_size(v_data_266_);
v___x_268_ = lean_unsigned_to_nat(2u);
v_nbuckets_269_ = lean_nat_mul(v___x_267_, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_box(0);
v___x_272_ = lean_mk_array(v_nbuckets_269_, v___x_271_);
v___x_273_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v___x_270_, v_data_266_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(lean_object* v_a_274_, lean_object* v_b_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_dec(v_b_275_);
lean_dec_ref(v_a_274_);
return v_x_276_;
}
else
{
lean_object* v_key_277_; lean_object* v_value_278_; lean_object* v_tail_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_293_; 
v_key_277_ = lean_ctor_get(v_x_276_, 0);
v_value_278_ = lean_ctor_get(v_x_276_, 1);
v_tail_279_ = lean_ctor_get(v_x_276_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_293_ == 0)
{
v___x_281_ = v_x_276_;
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_tail_279_);
lean_inc(v_value_278_);
lean_inc(v_key_277_);
lean_dec(v_x_276_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
size_t v___x_283_; size_t v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_ptr_addr(v_key_277_);
v___x_284_ = lean_ptr_addr(v_a_274_);
v___x_285_ = lean_usize_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_274_, v_b_275_, v_tail_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 2, v___x_286_);
v___x_288_ = v___x_281_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_key_277_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_value_278_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
else
{
lean_object* v___x_291_; 
lean_dec(v_value_278_);
lean_dec(v_key_277_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_b_275_);
lean_ctor_set(v___x_281_, 0, v_a_274_);
v___x_291_ = v___x_281_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_274_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_b_275_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_tail_279_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(lean_object* v_m_294_, lean_object* v_a_295_, lean_object* v_b_296_){
_start:
{
lean_object* v_size_297_; lean_object* v_buckets_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_342_; 
v_size_297_ = lean_ctor_get(v_m_294_, 0);
v_buckets_298_ = lean_ctor_get(v_m_294_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_m_294_);
if (v_isSharedCheck_342_ == 0)
{
v___x_300_ = v_m_294_;
v_isShared_301_ = v_isSharedCheck_342_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_buckets_298_);
lean_inc(v_size_297_);
lean_dec(v_m_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_342_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; size_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v_fold_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v_bkt_316_; uint8_t v___x_317_; 
v___x_302_ = lean_array_get_size(v_buckets_298_);
v___x_303_ = lean_ptr_addr(v_a_295_);
v___x_304_ = lean_usize_to_uint64(v___x_303_);
v___x_305_ = 32ULL;
v___x_306_ = lean_uint64_shift_right(v___x_304_, v___x_305_);
v_fold_307_ = lean_uint64_xor(v___x_304_, v___x_306_);
v___x_308_ = 16ULL;
v___x_309_ = lean_uint64_shift_right(v_fold_307_, v___x_308_);
v___x_310_ = lean_uint64_xor(v_fold_307_, v___x_309_);
v___x_311_ = lean_uint64_to_usize(v___x_310_);
v___x_312_ = lean_usize_of_nat(v___x_302_);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_sub(v___x_312_, v___x_313_);
v___x_315_ = lean_usize_land(v___x_311_, v___x_314_);
v_bkt_316_ = lean_array_uget_borrowed(v_buckets_298_, v___x_315_);
v___x_317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_295_, v_bkt_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v_size_x27_319_; lean_object* v___x_320_; lean_object* v_buckets_x27_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v_size_x27_319_ = lean_nat_add(v_size_297_, v___x_318_);
lean_dec(v_size_297_);
lean_inc(v_bkt_316_);
v___x_320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_320_, 0, v_a_295_);
lean_ctor_set(v___x_320_, 1, v_b_296_);
lean_ctor_set(v___x_320_, 2, v_bkt_316_);
v_buckets_x27_321_ = lean_array_uset(v_buckets_298_, v___x_315_, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(4u);
v___x_323_ = lean_nat_mul(v_size_x27_319_, v___x_322_);
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_nat_div(v___x_323_, v___x_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_array_get_size(v_buckets_x27_321_);
v___x_327_ = lean_nat_dec_le(v___x_325_, v___x_326_);
lean_dec(v___x_325_);
if (v___x_327_ == 0)
{
lean_object* v_val_328_; lean_object* v___x_330_; 
v_val_328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_buckets_x27_321_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_val_328_);
lean_ctor_set(v___x_300_, 0, v_size_x27_319_);
v___x_330_ = v___x_300_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_size_x27_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_val_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
else
{
lean_object* v___x_333_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_buckets_x27_321_);
lean_ctor_set(v___x_300_, 0, v_size_x27_319_);
v___x_333_ = v___x_300_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_size_x27_319_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_buckets_x27_321_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
lean_object* v___x_335_; lean_object* v_buckets_x27_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_inc(v_bkt_316_);
v___x_335_ = lean_box(0);
v_buckets_x27_336_ = lean_array_uset(v_buckets_298_, v___x_315_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_295_, v_b_296_, v_bkt_316_);
v___x_338_ = lean_array_uset(v_buckets_x27_336_, v___x_315_, v___x_337_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_338_);
v___x_340_ = v___x_300_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_297_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object* v_e_343_, uint64_t v_key_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; lean_object* v_fst_349_; lean_object* v_snd_350_; lean_object* v_cache_353_; lean_object* v_keyToExprs_354_; lean_object* v_buckets_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_347_ = lean_st_ref_take(v_a_345_);
v_cache_353_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_cache_353_);
v_keyToExprs_354_ = lean_ctor_get(v___x_347_, 1);
lean_inc_ref(v_keyToExprs_354_);
v_buckets_355_ = lean_ctor_get(v_cache_353_, 1);
v___x_356_ = lean_box(0);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_array_get_size(v_buckets_355_);
v___x_359_ = lean_nat_dec_lt(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_dec_ref(v_keyToExprs_354_);
lean_dec_ref(v_cache_353_);
lean_dec_ref(v_e_343_);
v_fst_349_ = v___x_356_;
v_snd_350_ = v___x_347_;
goto v___jp_348_;
}
else
{
lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; 
v_unused_369_ = lean_ctor_get(v___x_347_, 1);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v___x_347_, 0);
lean_dec(v_unused_370_);
v___x_361_ = v___x_347_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_dec(v___x_347_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_box_uint64(v_key_344_);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_cache_353_, v_e_343_, v___x_363_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_keyToExprs_354_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v_fst_349_ = v___x_356_;
v_snd_350_ = v___x_366_;
goto v___jp_348_;
}
}
}
v___jp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_st_ref_set(v_a_345_, v_snd_350_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v_fst_349_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object* v_e_371_, lean_object* v_key_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
uint64_t v_key_boxed_375_; lean_object* v_res_376_; 
v_key_boxed_375_ = lean_unbox_uint64(v_key_372_);
lean_dec_ref(v_key_372_);
v_res_376_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_371_, v_key_boxed_375_, v_a_373_);
lean_dec(v_a_373_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object* v_e_377_, uint64_t v_key_378_, uint8_t v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_377_, v_key_378_, v_a_380_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object* v_e_387_, lean_object* v_key_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
uint64_t v_key_boxed_396_; uint8_t v_a_boxed_397_; lean_object* v_res_398_; 
v_key_boxed_396_ = lean_unbox_uint64(v_key_388_);
lean_dec_ref(v_key_388_);
v_a_boxed_397_ = lean_unbox(v_a_389_);
v_res_398_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(v_e_387_, v_key_boxed_396_, v_a_boxed_397_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(lean_object* v_00_u03b2_399_, lean_object* v_m_400_, lean_object* v_a_401_, lean_object* v_b_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(v_m_400_, v_a_401_, v_b_402_);
return v___x_403_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(lean_object* v_00_u03b2_404_, lean_object* v_a_405_, lean_object* v_x_406_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___redArg(v_a_405_, v_x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0___boxed(lean_object* v_00_u03b2_408_, lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
uint8_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__0(v_00_u03b2_408_, v_a_409_, v_x_410_);
lean_dec(v_x_410_);
lean_dec_ref(v_a_409_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1(lean_object* v_00_u03b2_413_, lean_object* v_data_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1___redArg(v_data_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2(lean_object* v_00_u03b2_416_, lean_object* v_a_417_, lean_object* v_b_418_, lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__2___redArg(v_a_417_, v_b_418_, v_x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_421_, lean_object* v_i_422_, lean_object* v_source_423_, lean_object* v_target_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2___redArg(v_i_422_, v_source_423_, v_target_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0_spec__1_spec__2_spec__3___redArg(v_x_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object* v_e_430_, lean_object* v___y_431_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = l_Lean_Expr_hasMVar(v_e_430_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_e_430_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v_mctx_436_; lean_object* v___x_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_440_; lean_object* v_cache_441_; lean_object* v_zetaDeltaFVarIds_442_; lean_object* v_postponed_443_; lean_object* v_diag_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_453_; 
v___x_435_ = lean_st_ref_get(v___y_431_);
v_mctx_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_mctx_436_);
lean_dec(v___x_435_);
v___x_437_ = l_Lean_instantiateMVarsCore(v_mctx_436_, v_e_430_);
v_fst_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_fst_438_);
v_snd_439_ = lean_ctor_get(v___x_437_, 1);
lean_inc(v_snd_439_);
lean_dec_ref(v___x_437_);
v___x_440_ = lean_st_ref_take(v___y_431_);
v_cache_441_ = lean_ctor_get(v___x_440_, 1);
v_zetaDeltaFVarIds_442_ = lean_ctor_get(v___x_440_, 2);
v_postponed_443_ = lean_ctor_get(v___x_440_, 3);
v_diag_444_ = lean_ctor_get(v___x_440_, 4);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v___x_440_, 0);
lean_dec(v_unused_454_);
v___x_446_ = v___x_440_;
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_diag_444_);
lean_inc(v_postponed_443_);
lean_inc(v_zetaDeltaFVarIds_442_);
lean_inc(v_cache_441_);
lean_dec(v___x_440_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_snd_439_);
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_snd_439_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_cache_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_zetaDeltaFVarIds_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_postponed_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_diag_444_);
v___x_449_ = v_reuseFailAlloc_452_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_st_ref_set(v___y_431_, v___x_449_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v_fst_438_);
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object* v_e_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_455_, v___y_456_);
lean_dec(v___y_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* v_e_459_, uint8_t v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_459_, v___y_463_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object* v_e_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
uint8_t v___y_13171__boxed_476_; lean_object* v_res_477_; 
v___y_13171__boxed_476_ = lean_unbox(v___y_469_);
v_res_477_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(v_e_468_, v___y_13171__boxed_476_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
return v_res_477_;
}
}
static uint64_t _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0(void){
_start:
{
lean_object* v___x_478_; uint64_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(1723u);
v___x_479_ = lean_uint64_of_nat(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1(void){
_start:
{
uint64_t v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_uint64_once(&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0, &l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once, _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0);
v___x_481_ = lean_box_uint64(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* v_e_486_, uint8_t v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_t_495_; lean_object* v_b_496_; uint8_t v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; uint64_t v_key_519_; lean_object* v___y_520_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_get(v_a_488_);
v___x_540_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(v_e_486_, v___x_539_);
lean_dec(v___x_539_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_e_486_);
v_val_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_val_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_dec(v___x_540_);
switch(lean_obj_tag(v_e_486_))
{
case 2:
{
lean_object* v___x_549_; 
lean_inc_ref(v_e_486_);
v___x_549_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_486_, v_a_490_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_563_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_563_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_expr_eqv(v_a_550_, v_e_486_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_del_object(v___x_552_);
v___x_555_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_a_550_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; uint64_t v___x_557_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v___x_555_);
v___x_557_ = lean_unbox_uint64(v_a_556_);
lean_dec(v_a_556_);
v_key_519_ = v___x_557_;
v___y_520_ = v_a_488_;
goto v___jp_518_;
}
else
{
lean_dec_ref(v_e_486_);
return v___x_555_;
}
}
else
{
uint64_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec(v_a_550_);
v___x_558_ = l_Lean_Expr_hash(v_e_486_);
lean_dec_ref(v_e_486_);
v___x_559_ = lean_box_uint64(v___x_558_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_559_);
v___x_561_ = v___x_552_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v_e_486_);
v_a_564_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_549_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_549_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
case 4:
{
lean_object* v_declName_572_; 
v_declName_572_ = lean_ctor_get(v_e_486_, 0);
lean_inc(v_declName_572_);
lean_dec_ref(v_e_486_);
if (lean_obj_tag(v_declName_572_) == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
else
{
uint64_t v_hash_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_hash_575_ = lean_ctor_get_uint64(v_declName_572_, sizeof(void*)*2);
lean_dec(v_declName_572_);
v___x_576_ = lean_box_uint64(v_hash_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
case 5:
{
lean_object* v___x_578_; lean_object* v_info_580_; uint8_t v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; uint8_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; uint8_t v___x_613_; 
v___x_578_ = l_Lean_Expr_getAppFn(v_e_486_);
v___x_613_ = l_Lean_Expr_isMVar(v___x_578_);
if (v___x_613_ == 0)
{
v___y_594_ = v_a_487_;
v___y_595_ = v_a_488_;
v___y_596_ = v_a_489_;
v___y_597_ = v_a_490_;
v___y_598_ = v_a_491_;
v___y_599_ = v_a_492_;
goto v___jp_593_;
}
else
{
lean_object* v___x_614_; 
lean_inc_ref(v_e_486_);
v___x_614_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_486_, v_a_490_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; uint8_t v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref(v___x_614_);
v___x_616_ = lean_expr_eqv(v_a_615_, v_e_486_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_578_);
lean_dec_ref(v_e_486_);
v_e_486_ = v_a_615_;
goto _start;
}
else
{
lean_dec(v_a_615_);
v___y_594_ = v_a_487_;
v___y_595_ = v_a_488_;
v___y_596_ = v_a_489_;
v___y_597_ = v_a_490_;
v___y_598_ = v_a_491_;
v___y_599_ = v_a_492_;
goto v___jp_593_;
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v___x_578_);
lean_dec_ref(v_e_486_);
v_a_618_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_614_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_614_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
v___jp_579_:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_578_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint64_t v___x_591_; lean_object* v___x_592_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_587_);
v___x_589_ = l_Lean_Expr_getAppNumArgs(v_e_486_);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_unbox_uint64(v_a_588_);
lean_dec(v_a_588_);
v___x_592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_589_, v_e_486_, v___x_589_, v_info_580_, v___x_590_, v___x_591_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec_ref(v_info_580_);
lean_dec_ref(v_e_486_);
lean_dec(v___x_589_);
return v___x_592_;
}
else
{
lean_dec_ref(v_info_580_);
lean_dec_ref(v_e_486_);
return v___x_587_;
}
}
v___jp_593_:
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_Expr_hasLooseBVars(v___x_578_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_box(0);
lean_inc_ref(v___x_578_);
v___x_602_ = l_Lean_Meta_getFunInfo(v___x_578_, v___x_601_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_602_);
v_info_580_ = v_a_603_;
v___y_581_ = v___y_594_;
v___y_582_ = v___y_595_;
v___y_583_ = v___y_596_;
v___y_584_ = v___y_597_;
v___y_585_ = v___y_598_;
v___y_586_ = v___y_599_;
goto v___jp_579_;
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v___x_578_);
lean_dec_ref(v_e_486_);
v_a_604_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_602_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2));
v_info_580_ = v___x_612_;
v___y_581_ = v___y_594_;
v___y_582_ = v___y_595_;
v___y_583_ = v___y_596_;
v___y_584_ = v___y_597_;
v___y_585_ = v___y_598_;
v___y_586_ = v___y_599_;
goto v___jp_579_;
}
}
}
case 6:
{
lean_object* v_binderType_626_; lean_object* v_body_627_; 
v_binderType_626_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_binderType_626_);
v_body_627_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_body_627_);
lean_dec_ref(v_e_486_);
v_t_495_ = v_binderType_626_;
v_b_496_ = v_body_627_;
v___y_497_ = v_a_487_;
v___y_498_ = v_a_488_;
v___y_499_ = v_a_489_;
v___y_500_ = v_a_490_;
v___y_501_ = v_a_491_;
v___y_502_ = v_a_492_;
goto v___jp_494_;
}
case 7:
{
lean_object* v_binderType_628_; lean_object* v_body_629_; 
v_binderType_628_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_binderType_628_);
v_body_629_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_body_629_);
lean_dec_ref(v_e_486_);
v_t_495_ = v_binderType_628_;
v_b_496_ = v_body_629_;
v___y_497_ = v_a_487_;
v___y_498_ = v_a_488_;
v___y_499_ = v_a_489_;
v___y_500_ = v_a_490_;
v___y_501_ = v_a_491_;
v___y_502_ = v_a_492_;
goto v___jp_494_;
}
case 8:
{
lean_object* v_value_630_; lean_object* v_body_631_; lean_object* v___x_632_; 
v_value_630_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_value_630_);
v_body_631_ = lean_ctor_get(v_e_486_, 3);
lean_inc_ref(v_body_631_);
lean_dec_ref(v_e_486_);
v___x_632_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_630_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_631_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_646_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_646_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_646_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_646_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_639_ = lean_unbox_uint64(v_a_633_);
lean_dec(v_a_633_);
v___x_640_ = lean_unbox_uint64(v_a_635_);
lean_dec(v_a_635_);
v___x_641_ = lean_uint64_mix_hash(v___x_639_, v___x_640_);
v___x_642_ = lean_box_uint64(v___x_641_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_642_);
v___x_644_ = v___x_637_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_dec(v_a_633_);
return v___x_634_;
}
}
else
{
lean_dec_ref(v_body_631_);
return v___x_632_;
}
}
case 10:
{
lean_object* v_expr_647_; lean_object* v___x_648_; 
v_expr_647_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_expr_647_);
v___x_648_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_647_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; uint64_t v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = lean_unbox_uint64(v_a_649_);
lean_dec(v_a_649_);
v_key_519_ = v___x_650_;
v___y_520_ = v_a_488_;
goto v___jp_518_;
}
else
{
lean_dec_ref(v_e_486_);
return v___x_648_;
}
}
case 11:
{
lean_object* v_idx_651_; lean_object* v_struct_652_; lean_object* v___x_653_; 
v_idx_651_ = lean_ctor_get(v_e_486_, 1);
lean_inc(v_idx_651_);
v_struct_652_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_struct_652_);
lean_dec_ref(v_e_486_);
v___x_653_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_652_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_665_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_665_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_658_ = lean_uint64_of_nat(v_idx_651_);
lean_dec(v_idx_651_);
v___x_659_ = lean_unbox_uint64(v_a_654_);
lean_dec(v_a_654_);
v___x_660_ = lean_uint64_mix_hash(v___x_658_, v___x_659_);
v___x_661_ = lean_box_uint64(v___x_660_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_661_);
v___x_663_ = v___x_656_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
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
lean_dec(v_idx_651_);
return v___x_653_;
}
}
default: 
{
uint64_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = l_Lean_Expr_hash(v_e_486_);
lean_dec_ref(v_e_486_);
v___x_667_ = lean_box_uint64(v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
}
v___jp_494_:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_t_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_b_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_517_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_517_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_510_ = lean_unbox_uint64(v_a_504_);
lean_dec(v_a_504_);
v___x_511_ = lean_unbox_uint64(v_a_506_);
lean_dec(v_a_506_);
v___x_512_ = lean_uint64_mix_hash(v___x_510_, v___x_511_);
v___x_513_ = lean_box_uint64(v___x_512_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_513_);
v___x_515_ = v___x_508_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_dec(v_a_504_);
return v___x_505_;
}
}
else
{
lean_dec_ref(v_b_496_);
return v___x_503_;
}
}
v___jp_518_:
{
lean_object* v___x_521_; 
v___x_521_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_486_, v_key_519_, v___y_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_529_; 
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v___x_521_, 0);
lean_dec(v_unused_530_);
v___x_523_ = v___x_521_;
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
else
{
lean_dec(v___x_521_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = lean_box_uint64(v_key_519_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_a_531_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_521_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_521_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object* v___x_669_, lean_object* v_e_670_, lean_object* v_upperBound_671_, lean_object* v_info_672_, lean_object* v_a_673_, uint64_t v_b_674_, uint8_t v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
uint64_t v_a_683_; uint8_t v___y_688_; uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_lt(v_a_673_, v_upperBound_671_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v_a_673_);
v___x_698_ = lean_box_uint64(v_b_674_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v_paramInfo_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_paramInfo_700_ = lean_ctor_get(v_info_672_, 0);
v___x_701_ = lean_array_get_size(v_paramInfo_700_);
v___x_702_ = lean_nat_dec_lt(v_a_673_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_703_ = lean_nat_sub(v___x_669_, v_a_673_);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_sub(v___x_703_, v___x_704_);
lean_dec(v___x_703_);
v___x_706_ = l_Lean_Expr_getRevArg_x21(v_e_670_, v___x_705_);
v___x_707_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_706_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; uint64_t v___x_709_; uint64_t v___x_710_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_unbox_uint64(v_a_708_);
lean_dec(v_a_708_);
v___x_710_ = lean_uint64_mix_hash(v_b_674_, v___x_709_);
v_a_683_ = v___x_710_;
goto v___jp_682_;
}
else
{
lean_dec(v_a_673_);
return v___x_707_;
}
}
else
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_array_fget_borrowed(v_paramInfo_700_, v_a_673_);
v___x_712_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_711_);
if (v___x_712_ == 0)
{
v___y_688_ = v___x_712_;
goto v___jp_687_;
}
else
{
uint8_t v_isProp_713_; 
v_isProp_713_ = lean_ctor_get_uint8(v___x_711_, sizeof(void*)*1 + 2);
if (v_isProp_713_ == 0)
{
v___y_688_ = v___x_712_;
goto v___jp_687_;
}
else
{
v_a_683_ = v_b_674_;
goto v___jp_682_;
}
}
}
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_add(v_a_673_, v___x_684_);
lean_dec(v_a_673_);
v_a_673_ = v___x_685_;
v_b_674_ = v_a_683_;
goto _start;
}
v___jp_687_:
{
if (v___y_688_ == 0)
{
v_a_683_ = v_b_674_;
goto v___jp_682_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = lean_nat_sub(v___x_669_, v_a_673_);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v___x_689_, v___x_690_);
lean_dec(v___x_689_);
v___x_692_ = l_Lean_Expr_getRevArg_x21(v_e_670_, v___x_691_);
v___x_693_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_692_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; uint64_t v___x_695_; uint64_t v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref(v___x_693_);
v___x_695_ = lean_unbox_uint64(v_a_694_);
lean_dec(v_a_694_);
v___x_696_ = lean_uint64_mix_hash(v_b_674_, v___x_695_);
v_a_683_ = v___x_696_;
goto v___jp_682_;
}
else
{
lean_dec(v_a_673_);
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object* v___x_714_, lean_object* v_e_715_, lean_object* v_upperBound_716_, lean_object* v_info_717_, lean_object* v_a_718_, lean_object* v_b_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint64_t v_b_boxed_727_; uint8_t v___y_13203__boxed_728_; lean_object* v_res_729_; 
v_b_boxed_727_ = lean_unbox_uint64(v_b_719_);
lean_dec_ref(v_b_719_);
v___y_13203__boxed_728_ = lean_unbox(v___y_720_);
v_res_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_714_, v_e_715_, v_upperBound_716_, v_info_717_, v_a_718_, v_b_boxed_727_, v___y_13203__boxed_728_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v_info_717_);
lean_dec(v_upperBound_716_);
lean_dec_ref(v_e_715_);
lean_dec(v___x_714_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* v_e_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
uint8_t v_a_boxed_738_; lean_object* v_res_739_; 
v_a_boxed_738_ = lean_unbox(v_a_731_);
v_res_739_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_730_, v_a_boxed_738_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object* v___x_740_, lean_object* v_e_741_, lean_object* v_upperBound_742_, lean_object* v_info_743_, lean_object* v_inst_744_, lean_object* v_R_745_, lean_object* v_a_746_, uint64_t v_b_747_, lean_object* v_c_748_, uint8_t v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_740_, v_e_741_, v_upperBound_742_, v_info_743_, v_a_746_, v_b_747_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object* v___x_757_, lean_object* v_e_758_, lean_object* v_upperBound_759_, lean_object* v_info_760_, lean_object* v_inst_761_, lean_object* v_R_762_, lean_object* v_a_763_, lean_object* v_b_764_, lean_object* v_c_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint64_t v_b_boxed_773_; uint8_t v___y_13676__boxed_774_; lean_object* v_res_775_; 
v_b_boxed_773_ = lean_unbox_uint64(v_b_764_);
lean_dec_ref(v_b_764_);
v___y_13676__boxed_774_ = lean_unbox(v___y_766_);
v_res_775_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v___x_757_, v_e_758_, v_upperBound_759_, v_info_760_, v_inst_761_, v_R_762_, v_a_763_, v_b_boxed_773_, v_c_765_, v___y_13676__boxed_774_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v_info_760_);
lean_dec(v_upperBound_759_);
lean_dec_ref(v_e_758_);
lean_dec(v___x_757_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(uint64_t v_a_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v___x_778_; 
v___x_778_ = lean_box(0);
return v___x_778_;
}
else
{
lean_object* v_key_779_; lean_object* v_value_780_; lean_object* v_tail_781_; uint64_t v___x_782_; uint8_t v___x_783_; 
v_key_779_ = lean_ctor_get(v_x_777_, 0);
v_value_780_ = lean_ctor_get(v_x_777_, 1);
v_tail_781_ = lean_ctor_get(v_x_777_, 2);
v___x_782_ = lean_unbox_uint64(v_key_779_);
v___x_783_ = lean_uint64_dec_eq(v___x_782_, v_a_776_);
if (v___x_783_ == 0)
{
v_x_777_ = v_tail_781_;
goto _start;
}
else
{
lean_object* v___x_785_; 
lean_inc(v_value_780_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v_value_780_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
uint64_t v_a_boxed_788_; lean_object* v_res_789_; 
v_a_boxed_788_ = lean_unbox_uint64(v_a_786_);
lean_dec_ref(v_a_786_);
v_res_789_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_boxed_788_, v_x_787_);
lean_dec(v_x_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(lean_object* v_m_790_, uint64_t v_a_791_){
_start:
{
lean_object* v_buckets_792_; lean_object* v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v_fold_796_; uint64_t v___x_797_; uint64_t v___x_798_; uint64_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_buckets_792_ = lean_ctor_get(v_m_790_, 1);
v___x_793_ = lean_array_get_size(v_buckets_792_);
v___x_794_ = 32ULL;
v___x_795_ = lean_uint64_shift_right(v_a_791_, v___x_794_);
v_fold_796_ = lean_uint64_xor(v_a_791_, v___x_795_);
v___x_797_ = 16ULL;
v___x_798_ = lean_uint64_shift_right(v_fold_796_, v___x_797_);
v___x_799_ = lean_uint64_xor(v_fold_796_, v___x_798_);
v___x_800_ = lean_uint64_to_usize(v___x_799_);
v___x_801_ = lean_usize_of_nat(v___x_793_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_sub(v___x_801_, v___x_802_);
v___x_804_ = lean_usize_land(v___x_800_, v___x_803_);
v___x_805_ = lean_array_uget_borrowed(v_buckets_792_, v___x_804_);
v___x_806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_791_, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(lean_object* v_m_807_, lean_object* v_a_808_){
_start:
{
uint64_t v_a_boxed_809_; lean_object* v_res_810_; 
v_a_boxed_809_ = lean_unbox_uint64(v_a_808_);
lean_dec_ref(v_a_808_);
v_res_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_807_, v_a_boxed_809_);
lean_dec_ref(v_m_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t v_k_811_, lean_object* v_____do__lift_812_){
_start:
{
lean_object* v_keyToExprs_813_; lean_object* v___x_814_; 
v_keyToExprs_813_ = lean_ctor_get(v_____do__lift_812_, 1);
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_keyToExprs_813_, v_k_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* v_k_815_, lean_object* v_____do__lift_816_){
_start:
{
uint64_t v_k_boxed_817_; lean_object* v_res_818_; 
v_k_boxed_817_ = lean_unbox_uint64(v_k_815_);
lean_dec_ref(v_k_815_);
v_res_818_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v_k_boxed_817_, v_____do__lift_816_);
lean_dec_ref(v_____do__lift_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(lean_object* v_00_u03b2_819_, lean_object* v_m_820_, uint64_t v_a_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_820_, v_a_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(lean_object* v_00_u03b2_823_, lean_object* v_m_824_, lean_object* v_a_825_){
_start:
{
uint64_t v_a_boxed_826_; lean_object* v_res_827_; 
v_a_boxed_826_ = lean_unbox_uint64(v_a_825_);
lean_dec_ref(v_a_825_);
v_res_827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(v_00_u03b2_823_, v_m_824_, v_a_boxed_826_);
lean_dec_ref(v_m_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(lean_object* v_00_u03b2_828_, uint64_t v_a_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
uint64_t v_a_boxed_835_; lean_object* v_res_836_; 
v_a_boxed_835_ = lean_unbox_uint64(v_a_833_);
lean_dec_ref(v_a_833_);
v_res_836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(v_00_u03b2_832_, v_a_boxed_835_, v_x_834_);
lean_dec(v_x_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(uint64_t v_a_837_, lean_object* v_b_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_dec(v_b_838_);
return v_x_839_;
}
else
{
lean_object* v_key_840_; lean_object* v_value_841_; lean_object* v_tail_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_856_; 
v_key_840_ = lean_ctor_get(v_x_839_, 0);
v_value_841_ = lean_ctor_get(v_x_839_, 1);
v_tail_842_ = lean_ctor_get(v_x_839_, 2);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_839_);
if (v_isSharedCheck_856_ == 0)
{
v___x_844_ = v_x_839_;
v_isShared_845_ = v_isSharedCheck_856_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_tail_842_);
lean_inc(v_value_841_);
lean_inc(v_key_840_);
lean_dec(v_x_839_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_856_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
uint64_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_unbox_uint64(v_key_840_);
v___x_847_ = lean_uint64_dec_eq(v___x_846_, v_a_837_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_837_, v_b_838_, v_tail_842_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 2, v___x_848_);
v___x_850_ = v___x_844_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_key_840_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_value_841_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_dec(v_value_841_);
lean_dec(v_key_840_);
v___x_852_ = lean_box_uint64(v_a_837_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_b_838_);
lean_ctor_set(v___x_844_, 0, v___x_852_);
v___x_854_ = v___x_844_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_b_838_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_tail_842_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg___boxed(lean_object* v_a_857_, lean_object* v_b_858_, lean_object* v_x_859_){
_start:
{
uint64_t v_a_boxed_860_; lean_object* v_res_861_; 
v_a_boxed_860_ = lean_unbox_uint64(v_a_857_);
lean_dec_ref(v_a_857_);
v_res_861_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_boxed_860_, v_b_858_, v_x_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
return v_x_862_;
}
else
{
lean_object* v_key_864_; lean_object* v_value_865_; lean_object* v_tail_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_890_; 
v_key_864_ = lean_ctor_get(v_x_863_, 0);
v_value_865_ = lean_ctor_get(v_x_863_, 1);
v_tail_866_ = lean_ctor_get(v_x_863_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_890_ == 0)
{
v___x_868_ = v_x_863_;
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_tail_866_);
lean_inc(v_value_865_);
lean_inc(v_key_864_);
lean_dec(v_x_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; uint64_t v_fold_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_870_ = lean_array_get_size(v_x_862_);
v___x_871_ = 32ULL;
v___x_872_ = lean_unbox_uint64(v_key_864_);
v___x_873_ = lean_uint64_shift_right(v___x_872_, v___x_871_);
v___x_874_ = lean_unbox_uint64(v_key_864_);
v_fold_875_ = lean_uint64_xor(v___x_874_, v___x_873_);
v___x_876_ = 16ULL;
v___x_877_ = lean_uint64_shift_right(v_fold_875_, v___x_876_);
v___x_878_ = lean_uint64_xor(v_fold_875_, v___x_877_);
v___x_879_ = lean_uint64_to_usize(v___x_878_);
v___x_880_ = lean_usize_of_nat(v___x_870_);
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_sub(v___x_880_, v___x_881_);
v___x_883_ = lean_usize_land(v___x_879_, v___x_882_);
v___x_884_ = lean_array_uget_borrowed(v_x_862_, v___x_883_);
lean_inc(v___x_884_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 2, v___x_884_);
v___x_886_ = v___x_868_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_key_864_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_value_865_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v___x_884_);
v___x_886_ = v_reuseFailAlloc_889_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = lean_array_uset(v_x_862_, v___x_883_, v___x_886_);
v_x_862_ = v___x_887_;
v_x_863_ = v_tail_866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(lean_object* v_i_891_, lean_object* v_source_892_, lean_object* v_target_893_){
_start:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_array_get_size(v_source_892_);
v___x_895_ = lean_nat_dec_lt(v_i_891_, v___x_894_);
if (v___x_895_ == 0)
{
lean_dec_ref(v_source_892_);
lean_dec(v_i_891_);
return v_target_893_;
}
else
{
lean_object* v_es_896_; lean_object* v___x_897_; lean_object* v_source_898_; lean_object* v_target_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_es_896_ = lean_array_fget(v_source_892_, v_i_891_);
v___x_897_ = lean_box(0);
v_source_898_ = lean_array_fset(v_source_892_, v_i_891_, v___x_897_);
v_target_899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_target_893_, v_es_896_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_i_891_, v___x_900_);
lean_dec(v_i_891_);
v_i_891_ = v___x_901_;
v_source_892_ = v_source_898_;
v_target_893_ = v_target_899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(lean_object* v_data_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_nbuckets_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_904_ = lean_array_get_size(v_data_903_);
v___x_905_ = lean_unsigned_to_nat(2u);
v_nbuckets_906_ = lean_nat_mul(v___x_904_, v___x_905_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_box(0);
v___x_909_ = lean_mk_array(v_nbuckets_906_, v___x_908_);
v___x_910_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v___x_907_, v_data_903_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(uint64_t v_a_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_912_) == 0)
{
uint8_t v___x_913_; 
v___x_913_ = 0;
return v___x_913_;
}
else
{
lean_object* v_key_914_; lean_object* v_tail_915_; uint64_t v___x_916_; uint8_t v___x_917_; 
v_key_914_ = lean_ctor_get(v_x_912_, 0);
v_tail_915_ = lean_ctor_get(v_x_912_, 2);
v___x_916_ = lean_unbox_uint64(v_key_914_);
v___x_917_ = lean_uint64_dec_eq(v___x_916_, v_a_911_);
if (v___x_917_ == 0)
{
v_x_912_ = v_tail_915_;
goto _start;
}
else
{
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg___boxed(lean_object* v_a_919_, lean_object* v_x_920_){
_start:
{
uint64_t v_a_boxed_921_; uint8_t v_res_922_; lean_object* v_r_923_; 
v_a_boxed_921_ = lean_unbox_uint64(v_a_919_);
lean_dec_ref(v_a_919_);
v_res_922_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_boxed_921_, v_x_920_);
lean_dec(v_x_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* v_m_924_, uint64_t v_a_925_, lean_object* v_b_926_){
_start:
{
lean_object* v_size_927_; lean_object* v_buckets_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_971_; 
v_size_927_ = lean_ctor_get(v_m_924_, 0);
v_buckets_928_ = lean_ctor_get(v_m_924_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_m_924_);
if (v_isSharedCheck_971_ == 0)
{
v___x_930_ = v_m_924_;
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_buckets_928_);
lean_inc(v_size_927_);
lean_dec(v_m_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v_fold_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; size_t v___x_939_; size_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; lean_object* v_bkt_944_; uint8_t v___x_945_; 
v___x_932_ = lean_array_get_size(v_buckets_928_);
v___x_933_ = 32ULL;
v___x_934_ = lean_uint64_shift_right(v_a_925_, v___x_933_);
v_fold_935_ = lean_uint64_xor(v_a_925_, v___x_934_);
v___x_936_ = 16ULL;
v___x_937_ = lean_uint64_shift_right(v_fold_935_, v___x_936_);
v___x_938_ = lean_uint64_xor(v_fold_935_, v___x_937_);
v___x_939_ = lean_uint64_to_usize(v___x_938_);
v___x_940_ = lean_usize_of_nat(v___x_932_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_sub(v___x_940_, v___x_941_);
v___x_943_ = lean_usize_land(v___x_939_, v___x_942_);
v_bkt_944_ = lean_array_uget_borrowed(v_buckets_928_, v___x_943_);
v___x_945_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_925_, v_bkt_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v_size_x27_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_buckets_x27_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_946_ = lean_unsigned_to_nat(1u);
v_size_x27_947_ = lean_nat_add(v_size_927_, v___x_946_);
lean_dec(v_size_927_);
v___x_948_ = lean_box_uint64(v_a_925_);
lean_inc(v_bkt_944_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_b_926_);
lean_ctor_set(v___x_949_, 2, v_bkt_944_);
v_buckets_x27_950_ = lean_array_uset(v_buckets_928_, v___x_943_, v___x_949_);
v___x_951_ = lean_unsigned_to_nat(4u);
v___x_952_ = lean_nat_mul(v_size_x27_947_, v___x_951_);
v___x_953_ = lean_unsigned_to_nat(3u);
v___x_954_ = lean_nat_div(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_array_get_size(v_buckets_x27_950_);
v___x_956_ = lean_nat_dec_le(v___x_954_, v___x_955_);
lean_dec(v___x_954_);
if (v___x_956_ == 0)
{
lean_object* v_val_957_; lean_object* v___x_959_; 
v_val_957_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_buckets_x27_950_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v_val_957_);
lean_ctor_set(v___x_930_, 0, v_size_x27_947_);
v___x_959_ = v___x_930_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_size_x27_947_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_val_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v___x_962_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v_buckets_x27_950_);
lean_ctor_set(v___x_930_, 0, v_size_x27_947_);
v___x_962_ = v___x_930_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_size_x27_947_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_buckets_x27_950_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v___x_964_; lean_object* v_buckets_x27_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
lean_inc(v_bkt_944_);
v___x_964_ = lean_box(0);
v_buckets_x27_965_ = lean_array_uset(v_buckets_928_, v___x_943_, v___x_964_);
v___x_966_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_925_, v_b_926_, v_bkt_944_);
v___x_967_ = lean_array_uset(v_buckets_x27_965_, v___x_943_, v___x_966_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_967_);
v___x_969_ = v___x_930_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_size_927_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object* v_m_972_, lean_object* v_a_973_, lean_object* v_b_974_){
_start:
{
uint64_t v_a_boxed_975_; lean_object* v_res_976_; 
v_a_boxed_975_ = lean_unbox_uint64(v_a_973_);
lean_dec_ref(v_a_973_);
v_res_976_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_972_, v_a_boxed_975_, v_b_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object* v_e_980_, lean_object* v_as_x27_981_, lean_object* v_b_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
if (lean_obj_tag(v_as_x27_981_) == 0)
{
lean_object* v___x_988_; 
lean_dec_ref(v_e_980_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_b_982_);
return v___x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_tail_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_b_982_);
v_head_989_ = lean_ctor_get(v_as_x27_981_, 0);
v_tail_990_ = lean_ctor_get(v_as_x27_981_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_as_x27_981_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_992_ = v_as_x27_981_;
v_isShared_993_ = v_isSharedCheck_1019_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_tail_990_);
lean_inc(v_head_989_);
lean_dec(v_as_x27_981_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1019_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; 
lean_inc(v_head_989_);
lean_inc_ref(v_e_980_);
v___x_994_ = l_Lean_Meta_isExprDefEq(v_e_980_, v_head_989_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1010_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1010_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1010_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_box(0);
v___x_1000_ = lean_unbox(v_a_995_);
lean_dec(v_a_995_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_del_object(v___x_997_);
lean_del_object(v___x_992_);
lean_dec(v_head_989_);
v___x_1001_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0));
v_as_x27_981_ = v_tail_990_;
v_b_982_ = v___x_1001_;
goto _start;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_tail_990_);
lean_dec_ref(v_e_980_);
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_head_989_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 1, v___x_999_);
lean_ctor_set(v___x_992_, 0, v___x_1003_);
v___x_1005_ = v___x_992_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_999_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1005_);
v___x_1007_ = v___x_997_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_del_object(v___x_992_);
lean_dec(v_tail_990_);
lean_dec(v_head_989_);
lean_dec_ref(v_e_980_);
v_a_1011_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_994_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_994_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* v_e_1020_, lean_object* v_as_x27_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_e_1020_, v_as_x27_1021_, v_b_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* v_e_1029_, uint8_t v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; 
lean_inc_ref(v_e_1029_);
v___x_1037_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1152_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1152_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1152_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; uint64_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_st_ref_get(v_a_1031_);
v___x_1043_ = lean_unbox_uint64(v_a_1038_);
v___x_1044_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v___x_1043_, v___x_1042_);
lean_dec(v___x_1042_);
if (lean_obj_tag(v___x_1044_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1046_; uint8_t v_foApprox_1047_; uint8_t v_ctxApprox_1048_; uint8_t v_quasiPatternApprox_1049_; uint8_t v_constApprox_1050_; uint8_t v_isDefEqStuckEx_1051_; uint8_t v_unificationHints_1052_; uint8_t v_proofIrrelevance_1053_; uint8_t v_assignSyntheticOpaque_1054_; uint8_t v_offsetCnstrs_1055_; uint8_t v_etaStruct_1056_; uint8_t v_univApprox_1057_; uint8_t v_iota_1058_; uint8_t v_beta_1059_; uint8_t v_proj_1060_; uint8_t v_zeta_1061_; uint8_t v_zetaDelta_1062_; uint8_t v_zetaUnused_1063_; uint8_t v_zetaHave_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1133_; 
lean_del_object(v___x_1040_);
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lean_Meta_Context_config(v_a_1032_);
v_foApprox_1047_ = lean_ctor_get_uint8(v___x_1046_, 0);
v_ctxApprox_1048_ = lean_ctor_get_uint8(v___x_1046_, 1);
v_quasiPatternApprox_1049_ = lean_ctor_get_uint8(v___x_1046_, 2);
v_constApprox_1050_ = lean_ctor_get_uint8(v___x_1046_, 3);
v_isDefEqStuckEx_1051_ = lean_ctor_get_uint8(v___x_1046_, 4);
v_unificationHints_1052_ = lean_ctor_get_uint8(v___x_1046_, 5);
v_proofIrrelevance_1053_ = lean_ctor_get_uint8(v___x_1046_, 6);
v_assignSyntheticOpaque_1054_ = lean_ctor_get_uint8(v___x_1046_, 7);
v_offsetCnstrs_1055_ = lean_ctor_get_uint8(v___x_1046_, 8);
v_etaStruct_1056_ = lean_ctor_get_uint8(v___x_1046_, 10);
v_univApprox_1057_ = lean_ctor_get_uint8(v___x_1046_, 11);
v_iota_1058_ = lean_ctor_get_uint8(v___x_1046_, 12);
v_beta_1059_ = lean_ctor_get_uint8(v___x_1046_, 13);
v_proj_1060_ = lean_ctor_get_uint8(v___x_1046_, 14);
v_zeta_1061_ = lean_ctor_get_uint8(v___x_1046_, 15);
v_zetaDelta_1062_ = lean_ctor_get_uint8(v___x_1046_, 16);
v_zetaUnused_1063_ = lean_ctor_get_uint8(v___x_1046_, 17);
v_zetaHave_1064_ = lean_ctor_get_uint8(v___x_1046_, 18);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1066_ = v___x_1046_;
v_isShared_1067_ = v_isSharedCheck_1133_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v___x_1046_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1133_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint8_t v_trackZetaDelta_1068_; lean_object* v_zetaDeltaSet_1069_; lean_object* v_lctx_1070_; lean_object* v_localInstances_1071_; lean_object* v_defEqCtx_x3f_1072_; lean_object* v_synthPendingDepth_1073_; lean_object* v_canUnfold_x3f_1074_; uint8_t v_univApprox_1075_; uint8_t v_inTypeClassResolution_1076_; uint8_t v_cacheInferType_1077_; lean_object* v_config_1079_; 
v_trackZetaDelta_1068_ = lean_ctor_get_uint8(v_a_1032_, sizeof(void*)*7);
v_zetaDeltaSet_1069_ = lean_ctor_get(v_a_1032_, 1);
v_lctx_1070_ = lean_ctor_get(v_a_1032_, 2);
v_localInstances_1071_ = lean_ctor_get(v_a_1032_, 3);
v_defEqCtx_x3f_1072_ = lean_ctor_get(v_a_1032_, 4);
v_synthPendingDepth_1073_ = lean_ctor_get(v_a_1032_, 5);
v_canUnfold_x3f_1074_ = lean_ctor_get(v_a_1032_, 6);
v_univApprox_1075_ = lean_ctor_get_uint8(v_a_1032_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1076_ = lean_ctor_get_uint8(v_a_1032_, sizeof(void*)*7 + 2);
v_cacheInferType_1077_ = lean_ctor_get_uint8(v_a_1032_, sizeof(void*)*7 + 3);
if (v_isShared_1067_ == 0)
{
v_config_1079_ = v___x_1066_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 0, v_foApprox_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 1, v_ctxApprox_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 2, v_quasiPatternApprox_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 3, v_constApprox_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 4, v_isDefEqStuckEx_1051_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 5, v_unificationHints_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 6, v_proofIrrelevance_1053_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 7, v_assignSyntheticOpaque_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 8, v_offsetCnstrs_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 10, v_etaStruct_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 11, v_univApprox_1057_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 12, v_iota_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 13, v_beta_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 14, v_proj_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 15, v_zeta_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 16, v_zetaDelta_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 17, v_zetaUnused_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, 18, v_zetaHave_1064_);
v_config_1079_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; lean_object* v___x_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v_key_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_ctor_set_uint8(v_config_1079_, 9, v_a_1030_);
v___x_1080_ = l_Lean_Meta_Context_configKey(v_a_1032_);
v___x_1081_ = 2ULL;
v___x_1082_ = lean_uint64_shift_right(v___x_1080_, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0));
v___x_1084_ = lean_uint64_shift_left(v___x_1082_, v___x_1081_);
v___x_1085_ = l_Lean_Meta_TransparencyMode_toUInt64(v_a_1030_);
v_key_1086_ = lean_uint64_lor(v___x_1084_, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1087_, 0, v_config_1079_);
lean_ctor_set_uint64(v___x_1087_, sizeof(void*)*1, v_key_1086_);
lean_inc(v_canUnfold_x3f_1074_);
lean_inc(v_synthPendingDepth_1073_);
lean_inc(v_defEqCtx_x3f_1072_);
lean_inc_ref(v_localInstances_1071_);
lean_inc_ref(v_lctx_1070_);
lean_inc(v_zetaDeltaSet_1069_);
v___x_1088_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_zetaDeltaSet_1069_);
lean_ctor_set(v___x_1088_, 2, v_lctx_1070_);
lean_ctor_set(v___x_1088_, 3, v_localInstances_1071_);
lean_ctor_set(v___x_1088_, 4, v_defEqCtx_x3f_1072_);
lean_ctor_set(v___x_1088_, 5, v_synthPendingDepth_1073_);
lean_ctor_set(v___x_1088_, 6, v_canUnfold_x3f_1074_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*7, v_trackZetaDelta_1068_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*7 + 1, v_univApprox_1075_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1076_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*7 + 3, v_cacheInferType_1077_);
lean_inc(v_val_1045_);
lean_inc_ref(v_e_1029_);
v___x_1089_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_e_1029_, v_val_1045_, v___x_1083_, v___x_1088_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec_ref(v___x_1088_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1123_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1123_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1123_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_fst_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1121_; 
v_fst_1094_ = lean_ctor_get(v_a_1090_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_1090_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_a_1090_, 1);
lean_dec(v_unused_1122_);
v___x_1096_ = v_a_1090_;
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_fst_1094_);
lean_dec(v_a_1090_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
if (lean_obj_tag(v_fst_1094_) == 0)
{
lean_object* v___x_1098_; lean_object* v_cache_1099_; lean_object* v_keyToExprs_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1116_; 
v___x_1098_ = lean_st_ref_take(v_a_1031_);
v_cache_1099_ = lean_ctor_get(v___x_1098_, 0);
v_keyToExprs_1100_ = lean_ctor_get(v___x_1098_, 1);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1102_ = v___x_1098_;
v_isShared_1103_ = v_isSharedCheck_1116_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_keyToExprs_1100_);
lean_inc(v_cache_1099_);
lean_dec(v___x_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1116_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
lean_inc_ref(v_e_1029_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 1);
lean_ctor_set(v___x_1096_, 1, v_val_1045_);
lean_ctor_set(v___x_1096_, 0, v_e_1029_);
v___x_1105_ = v___x_1096_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_e_1029_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_val_1045_);
v___x_1105_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
uint64_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1106_ = lean_unbox_uint64(v_a_1038_);
lean_dec(v_a_1038_);
v___x_1107_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_1100_, v___x_1106_, v___x_1105_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___x_1107_);
v___x_1109_ = v___x_1102_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_cache_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = lean_st_ref_set(v_a_1031_, v___x_1109_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_e_1029_);
v___x_1112_ = v___x_1092_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_e_1029_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1119_; 
lean_del_object(v___x_1096_);
lean_dec(v_val_1045_);
lean_dec(v_a_1038_);
lean_dec_ref(v_e_1029_);
v_val_1117_ = lean_ctor_get(v_fst_1094_, 0);
lean_inc(v_val_1117_);
lean_dec_ref(v_fst_1094_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_val_1117_);
v___x_1119_ = v___x_1092_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_val_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v_val_1045_);
lean_dec(v_a_1038_);
lean_dec_ref(v_e_1029_);
v_a_1124_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1089_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1089_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
else
{
lean_object* v___x_1134_; lean_object* v_cache_1135_; lean_object* v_keyToExprs_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___x_1044_);
v___x_1134_ = lean_st_ref_take(v_a_1031_);
v_cache_1135_ = lean_ctor_get(v___x_1134_, 0);
v_keyToExprs_1136_ = lean_ctor_get(v___x_1134_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1138_ = v___x_1134_;
v_isShared_1139_ = v_isSharedCheck_1151_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_keyToExprs_1136_);
lean_inc(v_cache_1135_);
lean_dec(v___x_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1151_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint64_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1140_ = lean_box(0);
lean_inc_ref(v_e_1029_);
v___x_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_e_1029_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_unbox_uint64(v_a_1038_);
lean_dec(v_a_1038_);
v___x_1143_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_1136_, v___x_1142_, v___x_1141_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1143_);
v___x_1145_ = v___x_1138_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_cache_1135_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_st_ref_set(v_a_1031_, v___x_1145_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_e_1029_);
v___x_1148_ = v___x_1040_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_e_1029_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_e_1029_);
v_a_1153_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1037_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1037_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
uint8_t v_a_boxed_1169_; lean_object* v_res_1170_; 
v_a_boxed_1169_ = lean_unbox(v_a_1162_);
v_res_1170_ = l_Lean_Meta_Canonicalizer_canon(v_e_1161_, v_a_boxed_1169_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object* v_e_1171_, lean_object* v_as_1172_, lean_object* v_as_x27_1173_, lean_object* v_b_1174_, lean_object* v_a_1175_, uint8_t v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_e_1171_, v_as_x27_1173_, v_b_1174_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* v_e_1184_, lean_object* v_as_1185_, lean_object* v_as_x27_1186_, lean_object* v_b_1187_, lean_object* v_a_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v___y_10931__boxed_1196_; lean_object* v_res_1197_; 
v___y_10931__boxed_1196_ = lean_unbox(v___y_1189_);
v_res_1197_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(v_e_1184_, v_as_1185_, v_as_x27_1186_, v_b_1187_, v_a_1188_, v___y_10931__boxed_1196_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v_as_1185_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object* v_00_u03b2_1198_, lean_object* v_m_1199_, uint64_t v_a_1200_, lean_object* v_b_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_1199_, v_a_1200_, v_b_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object* v_00_u03b2_1203_, lean_object* v_m_1204_, lean_object* v_a_1205_, lean_object* v_b_1206_){
_start:
{
uint64_t v_a_boxed_1207_; lean_object* v_res_1208_; 
v_a_boxed_1207_ = lean_unbox_uint64(v_a_1205_);
lean_dec_ref(v_a_1205_);
v_res_1208_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(v_00_u03b2_1203_, v_m_1204_, v_a_boxed_1207_, v_b_1206_);
return v_res_1208_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(lean_object* v_00_u03b2_1209_, uint64_t v_a_1210_, lean_object* v_x_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_1210_, v_x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1213_, lean_object* v_a_1214_, lean_object* v_x_1215_){
_start:
{
uint64_t v_a_boxed_1216_; uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_a_boxed_1216_ = lean_unbox_uint64(v_a_1214_);
lean_dec_ref(v_a_1214_);
v_res_1217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(v_00_u03b2_1213_, v_a_boxed_1216_, v_x_1215_);
lean_dec(v_x_1215_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2(lean_object* v_00_u03b2_1219_, lean_object* v_data_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_data_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(lean_object* v_00_u03b2_1222_, uint64_t v_a_1223_, lean_object* v_b_1224_, lean_object* v_x_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_1223_, v_b_1224_, v_x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1227_, lean_object* v_a_1228_, lean_object* v_b_1229_, lean_object* v_x_1230_){
_start:
{
uint64_t v_a_boxed_1231_; lean_object* v_res_1232_; 
v_a_boxed_1231_ = lean_unbox_uint64(v_a_1228_);
lean_dec_ref(v_a_1228_);
v_res_1232_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(v_00_u03b2_1227_, v_a_boxed_1231_, v_b_1229_, v_x_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1233_, lean_object* v_i_1234_, lean_object* v_source_1235_, lean_object* v_target_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v_i_1234_, v_source_1235_, v_target_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1239_, v_x_1240_);
return v___x_1241_;
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
