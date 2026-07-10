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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = l_Lean_Expr_hasMVar(v_e_430_);
v___x_434_ = lean_bool_not(v___x_433_);
if (v___x_434_ == 0)
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
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v_e_430_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object* v_e_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_456_, v___y_457_);
lean_dec(v___y_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* v_e_460_, uint8_t v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_460_, v___y_464_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object* v_e_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___y_13167__boxed_477_; lean_object* v_res_478_; 
v___y_13167__boxed_477_ = lean_unbox(v___y_470_);
v_res_478_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(v_e_469_, v___y_13167__boxed_477_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
return v_res_478_;
}
}
static uint64_t _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0(void){
_start:
{
lean_object* v___x_479_; uint64_t v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1723u);
v___x_480_ = lean_uint64_of_nat(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1(void){
_start:
{
uint64_t v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_uint64_once(&l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0, &l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0_once, _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0);
v___x_482_ = lean_box_uint64(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* v_e_487_, uint8_t v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_t_496_; lean_object* v_b_497_; uint8_t v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; uint64_t v_key_520_; lean_object* v___y_521_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_st_ref_get(v_a_489_);
v___x_541_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(v_e_487_, v___x_540_);
lean_dec(v___x_540_);
if (lean_obj_tag(v___x_541_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v_e_487_);
v_val_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_val_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 0);
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_val_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_dec(v___x_541_);
switch(lean_obj_tag(v_e_487_))
{
case 2:
{
lean_object* v___x_550_; 
lean_inc_ref(v_e_487_);
v___x_550_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_487_, v_a_491_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_564_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_564_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint8_t v___x_555_; 
v___x_555_ = lean_expr_eqv(v_a_551_, v_e_487_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_del_object(v___x_553_);
v___x_556_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_a_551_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; uint64_t v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = lean_unbox_uint64(v_a_557_);
lean_dec(v_a_557_);
v_key_520_ = v___x_558_;
v___y_521_ = v_a_489_;
goto v___jp_519_;
}
else
{
lean_dec_ref_known(v_e_487_, 1);
return v___x_556_;
}
}
else
{
uint64_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec(v_a_551_);
v___x_559_ = l_Lean_Expr_hash(v_e_487_);
lean_dec_ref_known(v_e_487_, 1);
v___x_560_ = lean_box_uint64(v___x_559_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_560_);
v___x_562_ = v___x_553_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref_known(v_e_487_, 1);
v_a_565_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_550_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_550_);
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
case 4:
{
lean_object* v_declName_573_; 
v_declName_573_ = lean_ctor_get(v_e_487_, 0);
lean_inc(v_declName_573_);
lean_dec_ref_known(v_e_487_, 2);
if (lean_obj_tag(v_declName_573_) == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed__const__1;
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
else
{
uint64_t v_hash_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_hash_576_ = lean_ctor_get_uint64(v_declName_573_, sizeof(void*)*2);
lean_dec(v_declName_573_);
v___x_577_ = lean_box_uint64(v_hash_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
case 5:
{
lean_object* v___x_579_; lean_object* v_info_581_; uint8_t v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; uint8_t v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; uint8_t v___x_614_; 
v___x_579_ = l_Lean_Expr_getAppFn(v_e_487_);
v___x_614_ = l_Lean_Expr_isMVar(v___x_579_);
if (v___x_614_ == 0)
{
v___y_595_ = v_a_488_;
v___y_596_ = v_a_489_;
v___y_597_ = v_a_490_;
v___y_598_ = v_a_491_;
v___y_599_ = v_a_492_;
v___y_600_ = v_a_493_;
goto v___jp_594_;
}
else
{
lean_object* v___x_615_; 
lean_inc_ref(v_e_487_);
v___x_615_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(v_e_487_, v_a_491_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint8_t v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = lean_expr_eqv(v_a_616_, v_e_487_);
if (v___x_617_ == 0)
{
lean_dec_ref(v___x_579_);
lean_dec_ref_known(v_e_487_, 2);
v_e_487_ = v_a_616_;
goto _start;
}
else
{
lean_dec(v_a_616_);
v___y_595_ = v_a_488_;
v___y_596_ = v_a_489_;
v___y_597_ = v_a_490_;
v___y_598_ = v_a_491_;
v___y_599_ = v_a_492_;
v___y_600_ = v_a_493_;
goto v___jp_594_;
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v___x_579_);
lean_dec_ref_known(v_e_487_, 2);
v_a_619_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_615_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
v___jp_580_:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_579_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint64_t v___x_592_; lean_object* v___x_593_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = l_Lean_Expr_getAppNumArgs(v_e_487_);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_unbox_uint64(v_a_589_);
lean_dec(v_a_589_);
v___x_593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_590_, v_e_487_, v___x_590_, v_info_581_, v___x_591_, v___x_592_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec_ref(v_info_581_);
lean_dec_ref_known(v_e_487_, 2);
lean_dec(v___x_590_);
return v___x_593_;
}
else
{
lean_dec_ref(v_info_581_);
lean_dec_ref_known(v_e_487_, 2);
return v___x_588_;
}
}
v___jp_594_:
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_Expr_hasLooseBVars(v___x_579_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_box(0);
lean_inc_ref(v___x_579_);
v___x_603_ = l_Lean_Meta_getFunInfo(v___x_579_, v___x_602_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v_info_581_ = v_a_604_;
v___y_582_ = v___y_595_;
v___y_583_ = v___y_596_;
v___y_584_ = v___y_597_;
v___y_585_ = v___y_598_;
v___y_586_ = v___y_599_;
v___y_587_ = v___y_600_;
goto v___jp_580_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v___x_579_);
lean_dec_ref_known(v_e_487_, 2);
v_a_605_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_603_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v___x_613_; 
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__2));
v_info_581_ = v___x_613_;
v___y_582_ = v___y_595_;
v___y_583_ = v___y_596_;
v___y_584_ = v___y_597_;
v___y_585_ = v___y_598_;
v___y_586_ = v___y_599_;
v___y_587_ = v___y_600_;
goto v___jp_580_;
}
}
}
case 6:
{
lean_object* v_binderType_627_; lean_object* v_body_628_; 
v_binderType_627_ = lean_ctor_get(v_e_487_, 1);
lean_inc_ref(v_binderType_627_);
v_body_628_ = lean_ctor_get(v_e_487_, 2);
lean_inc_ref(v_body_628_);
lean_dec_ref_known(v_e_487_, 3);
v_t_496_ = v_binderType_627_;
v_b_497_ = v_body_628_;
v___y_498_ = v_a_488_;
v___y_499_ = v_a_489_;
v___y_500_ = v_a_490_;
v___y_501_ = v_a_491_;
v___y_502_ = v_a_492_;
v___y_503_ = v_a_493_;
goto v___jp_495_;
}
case 7:
{
lean_object* v_binderType_629_; lean_object* v_body_630_; 
v_binderType_629_ = lean_ctor_get(v_e_487_, 1);
lean_inc_ref(v_binderType_629_);
v_body_630_ = lean_ctor_get(v_e_487_, 2);
lean_inc_ref(v_body_630_);
lean_dec_ref_known(v_e_487_, 3);
v_t_496_ = v_binderType_629_;
v_b_497_ = v_body_630_;
v___y_498_ = v_a_488_;
v___y_499_ = v_a_489_;
v___y_500_ = v_a_490_;
v___y_501_ = v_a_491_;
v___y_502_ = v_a_492_;
v___y_503_ = v_a_493_;
goto v___jp_495_;
}
case 8:
{
lean_object* v_value_631_; lean_object* v_body_632_; lean_object* v___x_633_; 
v_value_631_ = lean_ctor_get(v_e_487_, 2);
lean_inc_ref(v_value_631_);
v_body_632_ = lean_ctor_get(v_e_487_, 3);
lean_inc_ref(v_body_632_);
lean_dec_ref_known(v_e_487_, 4);
v___x_633_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_value_631_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_body_632_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
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
v___x_640_ = lean_unbox_uint64(v_a_634_);
lean_dec(v_a_634_);
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
lean_dec(v_a_634_);
return v___x_635_;
}
}
else
{
lean_dec_ref(v_body_632_);
return v___x_633_;
}
}
case 10:
{
lean_object* v_expr_648_; lean_object* v___x_649_; 
v_expr_648_ = lean_ctor_get(v_e_487_, 1);
lean_inc_ref(v_expr_648_);
v___x_649_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_expr_648_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; uint64_t v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = lean_unbox_uint64(v_a_650_);
lean_dec(v_a_650_);
v_key_520_ = v___x_651_;
v___y_521_ = v_a_489_;
goto v___jp_519_;
}
else
{
lean_dec_ref_known(v_e_487_, 2);
return v___x_649_;
}
}
case 11:
{
lean_object* v_idx_652_; lean_object* v_struct_653_; lean_object* v___x_654_; 
v_idx_652_ = lean_ctor_get(v_e_487_, 1);
lean_inc(v_idx_652_);
v_struct_653_ = lean_ctor_get(v_e_487_, 2);
lean_inc_ref(v_struct_653_);
lean_dec_ref_known(v_e_487_, 3);
v___x_654_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_struct_653_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_666_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_666_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_659_ = lean_uint64_of_nat(v_idx_652_);
lean_dec(v_idx_652_);
v___x_660_ = lean_unbox_uint64(v_a_655_);
lean_dec(v_a_655_);
v___x_661_ = lean_uint64_mix_hash(v___x_659_, v___x_660_);
v___x_662_ = lean_box_uint64(v___x_661_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_662_);
v___x_664_ = v___x_657_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_dec(v_idx_652_);
return v___x_654_;
}
}
default: 
{
uint64_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_Expr_hash(v_e_487_);
lean_dec_ref(v_e_487_);
v___x_668_ = lean_box_uint64(v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
}
v___jp_495_:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_t_496_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_b_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_518_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_518_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_511_ = lean_unbox_uint64(v_a_505_);
lean_dec(v_a_505_);
v___x_512_ = lean_unbox_uint64(v_a_507_);
lean_dec(v_a_507_);
v___x_513_ = lean_uint64_mix_hash(v___x_511_, v___x_512_);
v___x_514_ = lean_box_uint64(v___x_513_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_514_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_dec(v_a_505_);
return v___x_506_;
}
}
else
{
lean_dec_ref(v_b_497_);
return v___x_504_;
}
}
v___jp_519_:
{
lean_object* v___x_522_; 
v___x_522_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(v_e_487_, v_key_520_, v___y_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_531_);
v___x_524_ = v___x_522_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_dec(v___x_522_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_box_uint64(v_key_520_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_522_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_522_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object* v___x_670_, lean_object* v_e_671_, lean_object* v_upperBound_672_, lean_object* v_info_673_, lean_object* v_a_674_, uint64_t v_b_675_, uint8_t v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
uint64_t v_a_684_; uint8_t v___y_689_; uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_lt(v_a_674_, v_upperBound_672_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v_a_674_);
v___x_699_ = lean_box_uint64(v_b_675_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
else
{
lean_object* v_paramInfo_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_paramInfo_701_ = lean_ctor_get(v_info_673_, 0);
v___x_702_ = lean_array_get_size(v_paramInfo_701_);
v___x_703_ = lean_nat_dec_lt(v_a_674_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = lean_nat_sub(v___x_670_, v_a_674_);
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_sub(v___x_704_, v___x_705_);
lean_dec(v___x_704_);
v___x_707_ = l_Lean_Expr_getRevArg_x21(v_e_671_, v___x_706_);
v___x_708_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_707_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; uint64_t v___x_710_; uint64_t v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_unbox_uint64(v_a_709_);
lean_dec(v_a_709_);
v___x_711_ = lean_uint64_mix_hash(v_b_675_, v___x_710_);
v_a_684_ = v___x_711_;
goto v___jp_683_;
}
else
{
lean_dec(v_a_674_);
return v___x_708_;
}
}
else
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_fget_borrowed(v_paramInfo_701_, v_a_674_);
v___x_713_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_712_);
if (v___x_713_ == 0)
{
v___y_689_ = v___x_713_;
goto v___jp_688_;
}
else
{
uint8_t v_isProp_714_; uint8_t v___x_715_; 
v_isProp_714_ = lean_ctor_get_uint8(v___x_712_, sizeof(void*)*1 + 2);
v___x_715_ = lean_bool_not(v_isProp_714_);
v___y_689_ = v___x_715_;
goto v___jp_688_;
}
}
}
v___jp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_a_674_, v___x_685_);
lean_dec(v_a_674_);
v_a_674_ = v___x_686_;
v_b_675_ = v_a_684_;
goto _start;
}
v___jp_688_:
{
if (v___y_689_ == 0)
{
v_a_684_ = v_b_675_;
goto v___jp_683_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_690_ = lean_nat_sub(v___x_670_, v_a_674_);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_sub(v___x_690_, v___x_691_);
lean_dec(v___x_690_);
v___x_693_ = l_Lean_Expr_getRevArg_x21(v_e_671_, v___x_692_);
v___x_694_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v___x_693_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; uint64_t v___x_696_; uint64_t v___x_697_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = lean_unbox_uint64(v_a_695_);
lean_dec(v_a_695_);
v___x_697_ = lean_uint64_mix_hash(v_b_675_, v___x_696_);
v_a_684_ = v___x_697_;
goto v___jp_683_;
}
else
{
lean_dec(v_a_674_);
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object* v___x_716_, lean_object* v_e_717_, lean_object* v_upperBound_718_, lean_object* v_info_719_, lean_object* v_a_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
uint64_t v_b_boxed_729_; uint8_t v___y_13199__boxed_730_; lean_object* v_res_731_; 
v_b_boxed_729_ = lean_unbox_uint64(v_b_721_);
lean_dec_ref(v_b_721_);
v___y_13199__boxed_730_ = lean_unbox(v___y_722_);
v_res_731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_716_, v_e_717_, v_upperBound_718_, v_info_719_, v_a_720_, v_b_boxed_729_, v___y_13199__boxed_730_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v_info_719_);
lean_dec(v_upperBound_718_);
lean_dec_ref(v_e_717_);
lean_dec(v___x_716_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
uint8_t v_a_boxed_740_; lean_object* v_res_741_; 
v_a_boxed_740_ = lean_unbox(v_a_733_);
v_res_741_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_732_, v_a_boxed_740_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object* v___x_742_, lean_object* v_e_743_, lean_object* v_upperBound_744_, lean_object* v_info_745_, lean_object* v_inst_746_, lean_object* v_R_747_, lean_object* v_a_748_, uint64_t v_b_749_, lean_object* v_c_750_, uint8_t v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(v___x_742_, v_e_743_, v_upperBound_744_, v_info_745_, v_a_748_, v_b_749_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object* v___x_759_, lean_object* v_e_760_, lean_object* v_upperBound_761_, lean_object* v_info_762_, lean_object* v_inst_763_, lean_object* v_R_764_, lean_object* v_a_765_, lean_object* v_b_766_, lean_object* v_c_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint64_t v_b_boxed_775_; uint8_t v___y_13674__boxed_776_; lean_object* v_res_777_; 
v_b_boxed_775_ = lean_unbox_uint64(v_b_766_);
lean_dec_ref(v_b_766_);
v___y_13674__boxed_776_ = lean_unbox(v___y_768_);
v_res_777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(v___x_759_, v_e_760_, v_upperBound_761_, v_info_762_, v_inst_763_, v_R_764_, v_a_765_, v_b_boxed_775_, v_c_767_, v___y_13674__boxed_776_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(uint64_t v_a_778_, lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_object* v___x_780_; 
v___x_780_ = lean_box(0);
return v___x_780_;
}
else
{
lean_object* v_key_781_; lean_object* v_value_782_; lean_object* v_tail_783_; uint64_t v___x_784_; uint8_t v___x_785_; 
v_key_781_ = lean_ctor_get(v_x_779_, 0);
v_value_782_ = lean_ctor_get(v_x_779_, 1);
v_tail_783_ = lean_ctor_get(v_x_779_, 2);
v___x_784_ = lean_unbox_uint64(v_key_781_);
v___x_785_ = lean_uint64_dec_eq(v___x_784_, v_a_778_);
if (v___x_785_ == 0)
{
v_x_779_ = v_tail_783_;
goto _start;
}
else
{
lean_object* v___x_787_; 
lean_inc(v_value_782_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v_value_782_);
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* v_a_788_, lean_object* v_x_789_){
_start:
{
uint64_t v_a_boxed_790_; lean_object* v_res_791_; 
v_a_boxed_790_ = lean_unbox_uint64(v_a_788_);
lean_dec_ref(v_a_788_);
v_res_791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_boxed_790_, v_x_789_);
lean_dec(v_x_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(lean_object* v_m_792_, uint64_t v_a_793_){
_start:
{
lean_object* v_buckets_794_; lean_object* v___x_795_; uint64_t v___x_796_; uint64_t v___x_797_; uint64_t v_fold_798_; uint64_t v___x_799_; uint64_t v___x_800_; uint64_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_buckets_794_ = lean_ctor_get(v_m_792_, 1);
v___x_795_ = lean_array_get_size(v_buckets_794_);
v___x_796_ = 32ULL;
v___x_797_ = lean_uint64_shift_right(v_a_793_, v___x_796_);
v_fold_798_ = lean_uint64_xor(v_a_793_, v___x_797_);
v___x_799_ = 16ULL;
v___x_800_ = lean_uint64_shift_right(v_fold_798_, v___x_799_);
v___x_801_ = lean_uint64_xor(v_fold_798_, v___x_800_);
v___x_802_ = lean_uint64_to_usize(v___x_801_);
v___x_803_ = lean_usize_of_nat(v___x_795_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_sub(v___x_803_, v___x_804_);
v___x_806_ = lean_usize_land(v___x_802_, v___x_805_);
v___x_807_ = lean_array_uget_borrowed(v_buckets_794_, v___x_806_);
v___x_808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_793_, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
uint64_t v_a_boxed_811_; lean_object* v_res_812_; 
v_a_boxed_811_ = lean_unbox_uint64(v_a_810_);
lean_dec_ref(v_a_810_);
v_res_812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_809_, v_a_boxed_811_);
lean_dec_ref(v_m_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t v_k_813_, lean_object* v_____do__lift_814_){
_start:
{
lean_object* v_keyToExprs_815_; lean_object* v___x_816_; 
v_keyToExprs_815_ = lean_ctor_get(v_____do__lift_814_, 1);
v___x_816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_keyToExprs_815_, v_k_813_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* v_k_817_, lean_object* v_____do__lift_818_){
_start:
{
uint64_t v_k_boxed_819_; lean_object* v_res_820_; 
v_k_boxed_819_ = lean_unbox_uint64(v_k_817_);
lean_dec_ref(v_k_817_);
v_res_820_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v_k_boxed_819_, v_____do__lift_818_);
lean_dec_ref(v_____do__lift_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(lean_object* v_00_u03b2_821_, lean_object* v_m_822_, uint64_t v_a_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(v_m_822_, v_a_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(lean_object* v_00_u03b2_825_, lean_object* v_m_826_, lean_object* v_a_827_){
_start:
{
uint64_t v_a_boxed_828_; lean_object* v_res_829_; 
v_a_boxed_828_ = lean_unbox_uint64(v_a_827_);
lean_dec_ref(v_a_827_);
v_res_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(v_00_u03b2_825_, v_m_826_, v_a_boxed_828_);
lean_dec_ref(v_m_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(lean_object* v_00_u03b2_830_, uint64_t v_a_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___redArg(v_a_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_834_, lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
uint64_t v_a_boxed_837_; lean_object* v_res_838_; 
v_a_boxed_837_ = lean_unbox_uint64(v_a_835_);
lean_dec_ref(v_a_835_);
v_res_838_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0_spec__0(v_00_u03b2_834_, v_a_boxed_837_, v_x_836_);
lean_dec(v_x_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(uint64_t v_a_839_, lean_object* v_b_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
lean_dec(v_b_840_);
return v_x_841_;
}
else
{
lean_object* v_key_842_; lean_object* v_value_843_; lean_object* v_tail_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_858_; 
v_key_842_ = lean_ctor_get(v_x_841_, 0);
v_value_843_ = lean_ctor_get(v_x_841_, 1);
v_tail_844_ = lean_ctor_get(v_x_841_, 2);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_841_);
if (v_isSharedCheck_858_ == 0)
{
v___x_846_ = v_x_841_;
v_isShared_847_ = v_isSharedCheck_858_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_tail_844_);
lean_inc(v_value_843_);
lean_inc(v_key_842_);
lean_dec(v_x_841_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_858_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint64_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_unbox_uint64(v_key_842_);
v___x_849_ = lean_uint64_dec_eq(v___x_848_, v_a_839_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_839_, v_b_840_, v_tail_844_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 2, v___x_850_);
v___x_852_ = v___x_846_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_key_842_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_value_843_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_value_843_);
lean_dec(v_key_842_);
v___x_854_ = lean_box_uint64(v_a_839_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_b_840_);
lean_ctor_set(v___x_846_, 0, v___x_854_);
v___x_856_ = v___x_846_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_b_840_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_tail_844_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg___boxed(lean_object* v_a_859_, lean_object* v_b_860_, lean_object* v_x_861_){
_start:
{
uint64_t v_a_boxed_862_; lean_object* v_res_863_; 
v_a_boxed_862_ = lean_unbox_uint64(v_a_859_);
lean_dec_ref(v_a_859_);
v_res_863_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_boxed_862_, v_b_860_, v_x_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
return v_x_864_;
}
else
{
lean_object* v_key_866_; lean_object* v_value_867_; lean_object* v_tail_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_892_; 
v_key_866_ = lean_ctor_get(v_x_865_, 0);
v_value_867_ = lean_ctor_get(v_x_865_, 1);
v_tail_868_ = lean_ctor_get(v_x_865_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_892_ == 0)
{
v___x_870_ = v_x_865_;
v_isShared_871_ = v_isSharedCheck_892_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_tail_868_);
lean_inc(v_value_867_);
lean_inc(v_key_866_);
lean_dec(v_x_865_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_892_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v_fold_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_872_ = lean_array_get_size(v_x_864_);
v___x_873_ = 32ULL;
v___x_874_ = lean_unbox_uint64(v_key_866_);
v___x_875_ = lean_uint64_shift_right(v___x_874_, v___x_873_);
v___x_876_ = lean_unbox_uint64(v_key_866_);
v_fold_877_ = lean_uint64_xor(v___x_876_, v___x_875_);
v___x_878_ = 16ULL;
v___x_879_ = lean_uint64_shift_right(v_fold_877_, v___x_878_);
v___x_880_ = lean_uint64_xor(v_fold_877_, v___x_879_);
v___x_881_ = lean_uint64_to_usize(v___x_880_);
v___x_882_ = lean_usize_of_nat(v___x_872_);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_sub(v___x_882_, v___x_883_);
v___x_885_ = lean_usize_land(v___x_881_, v___x_884_);
v___x_886_ = lean_array_uget_borrowed(v_x_864_, v___x_885_);
lean_inc(v___x_886_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 2, v___x_886_);
v___x_888_ = v___x_870_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_key_866_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_value_867_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___x_886_);
v___x_888_ = v_reuseFailAlloc_891_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = lean_array_uset(v_x_864_, v___x_885_, v___x_888_);
v_x_864_ = v___x_889_;
v_x_865_ = v_tail_868_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(lean_object* v_i_893_, lean_object* v_source_894_, lean_object* v_target_895_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_array_get_size(v_source_894_);
v___x_897_ = lean_nat_dec_lt(v_i_893_, v___x_896_);
if (v___x_897_ == 0)
{
lean_dec_ref(v_source_894_);
lean_dec(v_i_893_);
return v_target_895_;
}
else
{
lean_object* v_es_898_; lean_object* v___x_899_; lean_object* v_source_900_; lean_object* v_target_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_es_898_ = lean_array_fget(v_source_894_, v_i_893_);
v___x_899_ = lean_box(0);
v_source_900_ = lean_array_fset(v_source_894_, v_i_893_, v___x_899_);
v_target_901_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_target_895_, v_es_898_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_add(v_i_893_, v___x_902_);
lean_dec(v_i_893_);
v_i_893_ = v___x_903_;
v_source_894_ = v_source_900_;
v_target_895_ = v_target_901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(lean_object* v_data_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_nbuckets_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_906_ = lean_array_get_size(v_data_905_);
v___x_907_ = lean_unsigned_to_nat(2u);
v_nbuckets_908_ = lean_nat_mul(v___x_906_, v___x_907_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_box(0);
v___x_911_ = lean_mk_array(v_nbuckets_908_, v___x_910_);
v___x_912_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v___x_909_, v_data_905_, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(uint64_t v_a_913_, lean_object* v_x_914_){
_start:
{
if (lean_obj_tag(v_x_914_) == 0)
{
uint8_t v___x_915_; 
v___x_915_ = 0;
return v___x_915_;
}
else
{
lean_object* v_key_916_; lean_object* v_tail_917_; uint64_t v___x_918_; uint8_t v___x_919_; 
v_key_916_ = lean_ctor_get(v_x_914_, 0);
v_tail_917_ = lean_ctor_get(v_x_914_, 2);
v___x_918_ = lean_unbox_uint64(v_key_916_);
v___x_919_ = lean_uint64_dec_eq(v___x_918_, v_a_913_);
if (v___x_919_ == 0)
{
v_x_914_ = v_tail_917_;
goto _start;
}
else
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg___boxed(lean_object* v_a_921_, lean_object* v_x_922_){
_start:
{
uint64_t v_a_boxed_923_; uint8_t v_res_924_; lean_object* v_r_925_; 
v_a_boxed_923_ = lean_unbox_uint64(v_a_921_);
lean_dec_ref(v_a_921_);
v_res_924_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_boxed_923_, v_x_922_);
lean_dec(v_x_922_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* v_m_926_, uint64_t v_a_927_, lean_object* v_b_928_){
_start:
{
lean_object* v_size_929_; lean_object* v_buckets_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_973_; 
v_size_929_ = lean_ctor_get(v_m_926_, 0);
v_buckets_930_ = lean_ctor_get(v_m_926_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_m_926_);
if (v_isSharedCheck_973_ == 0)
{
v___x_932_ = v_m_926_;
v_isShared_933_ = v_isSharedCheck_973_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_buckets_930_);
lean_inc(v_size_929_);
lean_dec(v_m_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_973_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v_fold_937_; uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v_bkt_946_; uint8_t v___x_947_; 
v___x_934_ = lean_array_get_size(v_buckets_930_);
v___x_935_ = 32ULL;
v___x_936_ = lean_uint64_shift_right(v_a_927_, v___x_935_);
v_fold_937_ = lean_uint64_xor(v_a_927_, v___x_936_);
v___x_938_ = 16ULL;
v___x_939_ = lean_uint64_shift_right(v_fold_937_, v___x_938_);
v___x_940_ = lean_uint64_xor(v_fold_937_, v___x_939_);
v___x_941_ = lean_uint64_to_usize(v___x_940_);
v___x_942_ = lean_usize_of_nat(v___x_934_);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_sub(v___x_942_, v___x_943_);
v___x_945_ = lean_usize_land(v___x_941_, v___x_944_);
v_bkt_946_ = lean_array_uget_borrowed(v_buckets_930_, v___x_945_);
v___x_947_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_927_, v_bkt_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v_size_x27_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_buckets_x27_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v_size_x27_949_ = lean_nat_add(v_size_929_, v___x_948_);
lean_dec(v_size_929_);
v___x_950_ = lean_box_uint64(v_a_927_);
lean_inc(v_bkt_946_);
v___x_951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v_b_928_);
lean_ctor_set(v___x_951_, 2, v_bkt_946_);
v_buckets_x27_952_ = lean_array_uset(v_buckets_930_, v___x_945_, v___x_951_);
v___x_953_ = lean_unsigned_to_nat(4u);
v___x_954_ = lean_nat_mul(v_size_x27_949_, v___x_953_);
v___x_955_ = lean_unsigned_to_nat(3u);
v___x_956_ = lean_nat_div(v___x_954_, v___x_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_array_get_size(v_buckets_x27_952_);
v___x_958_ = lean_nat_dec_le(v___x_956_, v___x_957_);
lean_dec(v___x_956_);
if (v___x_958_ == 0)
{
lean_object* v_val_959_; lean_object* v___x_961_; 
v_val_959_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_buckets_x27_952_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_val_959_);
lean_ctor_set(v___x_932_, 0, v_size_x27_949_);
v___x_961_ = v___x_932_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_size_x27_949_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_val_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v___x_964_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_buckets_x27_952_);
lean_ctor_set(v___x_932_, 0, v_size_x27_949_);
v___x_964_ = v___x_932_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_size_x27_949_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_buckets_x27_952_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v___x_966_; lean_object* v_buckets_x27_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
lean_inc(v_bkt_946_);
v___x_966_ = lean_box(0);
v_buckets_x27_967_ = lean_array_uset(v_buckets_930_, v___x_945_, v___x_966_);
v___x_968_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_927_, v_b_928_, v_bkt_946_);
v___x_969_ = lean_array_uset(v_buckets_x27_967_, v___x_945_, v___x_968_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_969_);
v___x_971_ = v___x_932_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_size_929_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg___boxed(lean_object* v_m_974_, lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
uint64_t v_a_boxed_977_; lean_object* v_res_978_; 
v_a_boxed_977_ = lean_unbox_uint64(v_a_975_);
lean_dec_ref(v_a_975_);
v_res_978_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_974_, v_a_boxed_977_, v_b_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(lean_object* v_e_982_, lean_object* v_as_x27_983_, lean_object* v_b_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
if (lean_obj_tag(v_as_x27_983_) == 0)
{
lean_object* v___x_990_; 
lean_dec_ref(v_e_982_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v_b_984_);
return v___x_990_;
}
else
{
lean_object* v_head_991_; lean_object* v_tail_992_; lean_object* v___x_993_; 
lean_dec_ref(v_b_984_);
v_head_991_ = lean_ctor_get(v_as_x27_983_, 0);
v_tail_992_ = lean_ctor_get(v_as_x27_983_, 1);
lean_inc(v_head_991_);
lean_inc_ref(v_e_982_);
v___x_993_ = l_Lean_Meta_isExprDefEq(v_e_982_, v_head_991_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1007_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_box(0);
v___x_999_ = lean_unbox(v_a_994_);
lean_dec(v_a_994_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_del_object(v___x_996_);
v___x_1000_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0));
v_as_x27_983_ = v_tail_992_;
v_b_984_ = v___x_1000_;
goto _start;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec_ref(v_e_982_);
lean_inc(v_head_991_);
v___x_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1002_, 0, v_head_991_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_998_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1003_);
v___x_1005_ = v___x_996_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_e_982_);
v_a_1008_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_993_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_993_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* v_e_1016_, lean_object* v_as_x27_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_e_1016_, v_as_x27_1017_, v_b_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v_as_x27_1017_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* v_e_1025_, uint8_t v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1033_; 
lean_inc_ref(v_e_1025_);
v___x_1033_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(v_e_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1148_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1148_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1148_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; uint64_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_st_ref_get(v_a_1027_);
v___x_1039_ = lean_unbox_uint64(v_a_1034_);
v___x_1040_ = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_canon_unsafe__1(v___x_1039_, v___x_1038_);
lean_dec(v___x_1038_);
if (lean_obj_tag(v___x_1040_) == 1)
{
lean_object* v_val_1041_; lean_object* v___x_1042_; uint8_t v_foApprox_1043_; uint8_t v_ctxApprox_1044_; uint8_t v_quasiPatternApprox_1045_; uint8_t v_constApprox_1046_; uint8_t v_isDefEqStuckEx_1047_; uint8_t v_unificationHints_1048_; uint8_t v_proofIrrelevance_1049_; uint8_t v_assignSyntheticOpaque_1050_; uint8_t v_offsetCnstrs_1051_; uint8_t v_etaStruct_1052_; uint8_t v_univApprox_1053_; uint8_t v_iota_1054_; uint8_t v_beta_1055_; uint8_t v_proj_1056_; uint8_t v_zeta_1057_; uint8_t v_zetaDelta_1058_; uint8_t v_zetaUnused_1059_; uint8_t v_zetaHave_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_1036_);
v_val_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_val_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = l_Lean_Meta_Context_config(v_a_1028_);
v_foApprox_1043_ = lean_ctor_get_uint8(v___x_1042_, 0);
v_ctxApprox_1044_ = lean_ctor_get_uint8(v___x_1042_, 1);
v_quasiPatternApprox_1045_ = lean_ctor_get_uint8(v___x_1042_, 2);
v_constApprox_1046_ = lean_ctor_get_uint8(v___x_1042_, 3);
v_isDefEqStuckEx_1047_ = lean_ctor_get_uint8(v___x_1042_, 4);
v_unificationHints_1048_ = lean_ctor_get_uint8(v___x_1042_, 5);
v_proofIrrelevance_1049_ = lean_ctor_get_uint8(v___x_1042_, 6);
v_assignSyntheticOpaque_1050_ = lean_ctor_get_uint8(v___x_1042_, 7);
v_offsetCnstrs_1051_ = lean_ctor_get_uint8(v___x_1042_, 8);
v_etaStruct_1052_ = lean_ctor_get_uint8(v___x_1042_, 10);
v_univApprox_1053_ = lean_ctor_get_uint8(v___x_1042_, 11);
v_iota_1054_ = lean_ctor_get_uint8(v___x_1042_, 12);
v_beta_1055_ = lean_ctor_get_uint8(v___x_1042_, 13);
v_proj_1056_ = lean_ctor_get_uint8(v___x_1042_, 14);
v_zeta_1057_ = lean_ctor_get_uint8(v___x_1042_, 15);
v_zetaDelta_1058_ = lean_ctor_get_uint8(v___x_1042_, 16);
v_zetaUnused_1059_ = lean_ctor_get_uint8(v___x_1042_, 17);
v_zetaHave_1060_ = lean_ctor_get_uint8(v___x_1042_, 18);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1062_ = v___x_1042_;
v_isShared_1063_ = v_isSharedCheck_1129_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v___x_1042_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1129_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
uint8_t v_trackZetaDelta_1064_; lean_object* v_zetaDeltaSet_1065_; lean_object* v_lctx_1066_; lean_object* v_localInstances_1067_; lean_object* v_defEqCtx_x3f_1068_; lean_object* v_synthPendingDepth_1069_; lean_object* v_canUnfold_x3f_1070_; uint8_t v_univApprox_1071_; uint8_t v_inTypeClassResolution_1072_; uint8_t v_cacheInferType_1073_; lean_object* v_config_1075_; 
v_trackZetaDelta_1064_ = lean_ctor_get_uint8(v_a_1028_, sizeof(void*)*7);
v_zetaDeltaSet_1065_ = lean_ctor_get(v_a_1028_, 1);
v_lctx_1066_ = lean_ctor_get(v_a_1028_, 2);
v_localInstances_1067_ = lean_ctor_get(v_a_1028_, 3);
v_defEqCtx_x3f_1068_ = lean_ctor_get(v_a_1028_, 4);
v_synthPendingDepth_1069_ = lean_ctor_get(v_a_1028_, 5);
v_canUnfold_x3f_1070_ = lean_ctor_get(v_a_1028_, 6);
v_univApprox_1071_ = lean_ctor_get_uint8(v_a_1028_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1072_ = lean_ctor_get_uint8(v_a_1028_, sizeof(void*)*7 + 2);
v_cacheInferType_1073_ = lean_ctor_get_uint8(v_a_1028_, sizeof(void*)*7 + 3);
if (v_isShared_1063_ == 0)
{
v_config_1075_ = v___x_1062_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 0, v_foApprox_1043_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 1, v_ctxApprox_1044_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 2, v_quasiPatternApprox_1045_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 3, v_constApprox_1046_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 4, v_isDefEqStuckEx_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 5, v_unificationHints_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 6, v_proofIrrelevance_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 7, v_assignSyntheticOpaque_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 8, v_offsetCnstrs_1051_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 10, v_etaStruct_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 11, v_univApprox_1053_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 12, v_iota_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 13, v_beta_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 14, v_proj_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 15, v_zeta_1057_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 16, v_zetaDelta_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 17, v_zetaUnused_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, 18, v_zetaHave_1060_);
v_config_1075_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
uint64_t v___x_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; lean_object* v___x_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v_key_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_ctor_set_uint8(v_config_1075_, 9, v_a_1026_);
v___x_1076_ = l_Lean_Meta_Context_configKey(v_a_1028_);
v___x_1077_ = 3ULL;
v___x_1078_ = lean_uint64_shift_right(v___x_1076_, v___x_1077_);
v___x_1079_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg___closed__0));
v___x_1080_ = lean_uint64_shift_left(v___x_1078_, v___x_1077_);
v___x_1081_ = l_Lean_Meta_TransparencyMode_toUInt64(v_a_1026_);
v_key_1082_ = lean_uint64_lor(v___x_1080_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1083_, 0, v_config_1075_);
lean_ctor_set_uint64(v___x_1083_, sizeof(void*)*1, v_key_1082_);
lean_inc(v_canUnfold_x3f_1070_);
lean_inc(v_synthPendingDepth_1069_);
lean_inc(v_defEqCtx_x3f_1068_);
lean_inc_ref(v_localInstances_1067_);
lean_inc_ref(v_lctx_1066_);
lean_inc(v_zetaDeltaSet_1065_);
v___x_1084_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_zetaDeltaSet_1065_);
lean_ctor_set(v___x_1084_, 2, v_lctx_1066_);
lean_ctor_set(v___x_1084_, 3, v_localInstances_1067_);
lean_ctor_set(v___x_1084_, 4, v_defEqCtx_x3f_1068_);
lean_ctor_set(v___x_1084_, 5, v_synthPendingDepth_1069_);
lean_ctor_set(v___x_1084_, 6, v_canUnfold_x3f_1070_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*7, v_trackZetaDelta_1064_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*7 + 1, v_univApprox_1071_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1072_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*7 + 3, v_cacheInferType_1073_);
lean_inc_ref(v_e_1025_);
v___x_1085_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_e_1025_, v_val_1041_, v___x_1079_, v___x_1084_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec_ref_known(v___x_1084_, 7);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1119_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1119_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1119_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_fst_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1117_; 
v_fst_1090_ = lean_ctor_get(v_a_1086_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_a_1086_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_a_1086_, 1);
lean_dec(v_unused_1118_);
v___x_1092_ = v_a_1086_;
v_isShared_1093_ = v_isSharedCheck_1117_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_fst_1090_);
lean_dec(v_a_1086_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1117_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
if (lean_obj_tag(v_fst_1090_) == 0)
{
lean_object* v___x_1094_; lean_object* v_cache_1095_; lean_object* v_keyToExprs_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1112_; 
v___x_1094_ = lean_st_ref_take(v_a_1027_);
v_cache_1095_ = lean_ctor_get(v___x_1094_, 0);
v_keyToExprs_1096_ = lean_ctor_get(v___x_1094_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1098_ = v___x_1094_;
v_isShared_1099_ = v_isSharedCheck_1112_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_keyToExprs_1096_);
lean_inc(v_cache_1095_);
lean_dec(v___x_1094_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1112_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
lean_inc_ref(v_e_1025_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
lean_ctor_set(v___x_1092_, 1, v_val_1041_);
lean_ctor_set(v___x_1092_, 0, v_e_1025_);
v___x_1101_ = v___x_1092_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_e_1025_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_val_1041_);
v___x_1101_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
uint64_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = lean_unbox_uint64(v_a_1034_);
lean_dec(v_a_1034_);
v___x_1103_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_1096_, v___x_1102_, v___x_1101_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1103_);
v___x_1105_ = v___x_1098_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_cache_1095_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = lean_st_ref_set(v_a_1027_, v___x_1105_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_e_1025_);
v___x_1108_ = v___x_1088_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_e_1025_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
else
{
lean_object* v_val_1113_; lean_object* v___x_1115_; 
lean_del_object(v___x_1092_);
lean_dec(v_val_1041_);
lean_dec(v_a_1034_);
lean_dec_ref(v_e_1025_);
v_val_1113_ = lean_ctor_get(v_fst_1090_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v_fst_1090_, 1);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_val_1113_);
v___x_1115_ = v___x_1088_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_val_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_val_1041_);
lean_dec(v_a_1034_);
lean_dec_ref(v_e_1025_);
v_a_1120_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1085_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1085_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
else
{
lean_object* v___x_1130_; lean_object* v_cache_1131_; lean_object* v_keyToExprs_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v___x_1040_);
v___x_1130_ = lean_st_ref_take(v_a_1027_);
v_cache_1131_ = lean_ctor_get(v___x_1130_, 0);
v_keyToExprs_1132_ = lean_ctor_get(v___x_1130_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1134_ = v___x_1130_;
v_isShared_1135_ = v_isSharedCheck_1147_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_keyToExprs_1132_);
lean_inc(v_cache_1131_);
lean_dec(v___x_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1147_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; uint64_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1136_ = lean_box(0);
lean_inc_ref(v_e_1025_);
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_e_1025_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_unbox_uint64(v_a_1034_);
lean_dec(v_a_1034_);
v___x_1139_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_keyToExprs_1132_, v___x_1138_, v___x_1137_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1139_);
v___x_1141_ = v___x_1134_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_cache_1131_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_st_ref_set(v_a_1027_, v___x_1141_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v_e_1025_);
v___x_1144_ = v___x_1036_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_e_1025_);
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
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_e_1025_);
v_a_1149_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1033_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1033_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* v_e_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
uint8_t v_a_boxed_1165_; lean_object* v_res_1166_; 
v_a_boxed_1165_ = lean_unbox(v_a_1158_);
v_res_1166_ = l_Lean_Meta_Canonicalizer_canon(v_e_1157_, v_a_boxed_1165_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(lean_object* v_e_1167_, lean_object* v_as_1168_, lean_object* v_as_x27_1169_, lean_object* v_b_1170_, lean_object* v_a_1171_, uint8_t v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___redArg(v_e_1167_, v_as_x27_1169_, v_b_1170_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* v_e_1180_, lean_object* v_as_1181_, lean_object* v_as_x27_1182_, lean_object* v_b_1183_, lean_object* v_a_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v___y_10919__boxed_1192_; lean_object* v_res_1193_; 
v___y_10919__boxed_1192_ = lean_unbox(v___y_1185_);
v_res_1193_ = l_List_forIn_x27_loop___at___00Lean_Meta_Canonicalizer_canon_spec__0(v_e_1180_, v_as_1181_, v_as_x27_1182_, v_b_1183_, v_a_1184_, v___y_10919__boxed_1192_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v_as_x27_1182_);
lean_dec(v_as_1181_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(lean_object* v_00_u03b2_1194_, lean_object* v_m_1195_, uint64_t v_a_1196_, lean_object* v_b_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___redArg(v_m_1195_, v_a_1196_, v_b_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1___boxed(lean_object* v_00_u03b2_1199_, lean_object* v_m_1200_, lean_object* v_a_1201_, lean_object* v_b_1202_){
_start:
{
uint64_t v_a_boxed_1203_; lean_object* v_res_1204_; 
v_a_boxed_1203_ = lean_unbox_uint64(v_a_1201_);
lean_dec_ref(v_a_1201_);
v_res_1204_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1(v_00_u03b2_1199_, v_m_1200_, v_a_boxed_1203_, v_b_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(lean_object* v_00_u03b2_1205_, uint64_t v_a_1206_, lean_object* v_x_1207_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(v_a_1206_, v_x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1209_, lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
uint64_t v_a_boxed_1212_; uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_a_boxed_1212_ = lean_unbox_uint64(v_a_1210_);
lean_dec_ref(v_a_1210_);
v_res_1213_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__1(v_00_u03b2_1209_, v_a_boxed_1212_, v_x_1211_);
lean_dec(v_x_1211_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2(lean_object* v_00_u03b2_1215_, lean_object* v_data_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2___redArg(v_data_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(lean_object* v_00_u03b2_1218_, uint64_t v_a_1219_, lean_object* v_b_1220_, lean_object* v_x_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___redArg(v_a_1219_, v_b_1220_, v_x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1223_, lean_object* v_a_1224_, lean_object* v_b_1225_, lean_object* v_x_1226_){
_start:
{
uint64_t v_a_boxed_1227_; lean_object* v_res_1228_; 
v_a_boxed_1227_ = lean_unbox_uint64(v_a_1224_);
lean_dec_ref(v_a_1224_);
v_res_1228_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__3(v_00_u03b2_1223_, v_a_boxed_1227_, v_b_1225_, v_x_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1229_, lean_object* v_i_1230_, lean_object* v_source_1231_, lean_object* v_target_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3___redArg(v_i_1230_, v_source_1231_, v_target_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Canonicalizer_canon_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1235_, v_x_1236_);
return v___x_1237_;
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
