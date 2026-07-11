// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Rewrite
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeSimprocExt;
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rewriteRules"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(39, 217, 1, 104, 84, 94, 139, 227)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_9_ = lean_apply_7(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0___boxed(lean_object* v_x_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(v_x_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(lean_object* v_mvarId_19_, lean_object* v_x_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___f_28_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_28_, 0, v_x_20_);
lean_closure_set(v___f_28_, 1, v___y_21_);
lean_closure_set(v___f_28_, 2, v___y_22_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_19_, v___f_28_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
return v___x_29_;
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___boxed(lean_object* v_mvarId_38_, lean_object* v_x_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_mvarId_38_, v_x_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2(lean_object* v_00_u03b1_48_, lean_object* v_mvarId_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_mvarId_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___boxed(lean_object* v_00_u03b1_59_, lean_object* v_mvarId_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2(v_00_u03b1_59_, v_mvarId_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_69_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(lean_object* v_a_70_, lean_object* v_x_71_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
else
{
lean_object* v_key_73_; lean_object* v_tail_74_; uint8_t v___x_75_; 
v_key_73_ = lean_ctor_get(v_x_71_, 0);
v_tail_74_ = lean_ctor_get(v_x_71_, 2);
v___x_75_ = l_Lean_instBEqFVarId_beq(v_key_73_, v_a_70_);
if (v___x_75_ == 0)
{
v_x_71_ = v_tail_74_;
goto _start;
}
else
{
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_77_, lean_object* v_x_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_77_, v_x_78_);
lean_dec(v_x_78_);
lean_dec(v_a_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(lean_object* v_m_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_buckets_83_; lean_object* v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v_fold_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_buckets_83_ = lean_ctor_get(v_m_81_, 1);
v___x_84_ = lean_array_get_size(v_buckets_83_);
v___x_85_ = l_Lean_instHashableFVarId_hash(v_a_82_);
v___x_86_ = 32ULL;
v___x_87_ = lean_uint64_shift_right(v___x_85_, v___x_86_);
v_fold_88_ = lean_uint64_xor(v___x_85_, v___x_87_);
v___x_89_ = 16ULL;
v___x_90_ = lean_uint64_shift_right(v_fold_88_, v___x_89_);
v___x_91_ = lean_uint64_xor(v_fold_88_, v___x_90_);
v___x_92_ = lean_uint64_to_usize(v___x_91_);
v___x_93_ = lean_usize_of_nat(v___x_84_);
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_sub(v___x_93_, v___x_94_);
v___x_96_ = lean_usize_land(v___x_92_, v___x_95_);
v___x_97_ = lean_array_uget_borrowed(v_buckets_83_, v___x_96_);
v___x_98_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_82_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg___boxed(lean_object* v_m_99_, lean_object* v_a_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(v_m_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_m_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(lean_object* v_as_103_, size_t v_i_104_, size_t v_stop_105_, lean_object* v_b_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_a_110_; uint8_t v___x_114_; 
v___x_114_ = lean_usize_dec_eq(v_i_104_, v_stop_105_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v_rewriteCache_116_; lean_object* v___x_117_; uint8_t v___x_118_; uint8_t v___x_119_; 
v___x_115_ = lean_st_ref_get(v___y_107_);
v_rewriteCache_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref(v_rewriteCache_116_);
lean_dec(v___x_115_);
v___x_117_ = lean_array_uget_borrowed(v_as_103_, v_i_104_);
v___x_118_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(v_rewriteCache_116_, v___x_117_);
lean_dec_ref(v_rewriteCache_116_);
v___x_119_ = lean_bool_not(v___x_118_);
if (v___x_119_ == 0)
{
v_a_110_ = v_b_106_;
goto v___jp_109_;
}
else
{
lean_object* v___x_120_; 
lean_inc(v___x_117_);
v___x_120_ = lean_array_push(v_b_106_, v___x_117_);
v_a_110_ = v___x_120_;
goto v___jp_109_;
}
}
else
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v_b_106_);
return v___x_121_;
}
v___jp_109_:
{
size_t v___x_111_; size_t v___x_112_; 
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_104_, v___x_111_);
v_i_104_ = v___x_112_;
v_b_106_ = v_a_110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg___boxed(lean_object* v_as_122_, lean_object* v_i_123_, lean_object* v_stop_124_, lean_object* v_b_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
size_t v_i_boxed_128_; size_t v_stop_boxed_129_; lean_object* v_res_130_; 
v_i_boxed_128_ = lean_unbox_usize(v_i_123_);
lean_dec(v_i_123_);
v_stop_boxed_129_ = lean_unbox_usize(v_stop_124_);
lean_dec(v_stop_124_);
v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_as_122_, v_i_boxed_128_, v_stop_boxed_129_, v_b_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v_as_122_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0(lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_getPropHyps(v___y_135_, v___y_136_, v___y_137_, v___y_138_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_162_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_162_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_162_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_162_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_array_get_size(v_a_141_);
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0));
v___x_148_ = lean_nat_dec_lt(v___x_145_, v___x_146_);
if (v___x_148_ == 0)
{
lean_object* v___x_150_; 
lean_dec(v_a_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_147_);
v___x_150_ = v___x_143_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_147_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
else
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_le(v___x_146_, v___x_146_);
if (v___x_152_ == 0)
{
if (v___x_148_ == 0)
{
lean_object* v___x_154_; 
lean_dec(v_a_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_147_);
v___x_154_ = v___x_143_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_147_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; 
lean_del_object(v___x_143_);
v___x_156_ = ((size_t)0ULL);
v___x_157_ = lean_usize_of_nat(v___x_146_);
v___x_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_a_141_, v___x_156_, v___x_157_, v___x_147_, v___y_134_);
lean_dec(v_a_141_);
return v___x_158_;
}
}
else
{
size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
lean_del_object(v___x_143_);
v___x_159_ = ((size_t)0ULL);
v___x_160_ = lean_usize_of_nat(v___x_146_);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_a_141_, v___x_159_, v___x_160_, v___x_147_, v___y_134_);
lean_dec(v_a_141_);
return v___x_161_;
}
}
}
}
else
{
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___boxed(lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0(v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps(lean_object* v_goal_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___f_180_; lean_object* v___x_181_; 
v___f_180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0));
v___x_181_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_goal_172_, v___f_180_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___boxed(lean_object* v_goal_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps(v_goal_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_190_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0(lean_object* v_00_u03b2_191_, lean_object* v_m_192_, lean_object* v_a_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(v_m_192_, v_a_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___boxed(lean_object* v_00_u03b2_195_, lean_object* v_m_196_, lean_object* v_a_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0(v_00_u03b2_195_, v_m_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_m_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1(lean_object* v_as_200_, size_t v_i_201_, size_t v_stop_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_as_200_, v_i_201_, v_stop_202_, v_b_203_, v___y_205_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___boxed(lean_object* v_as_212_, lean_object* v_i_213_, lean_object* v_stop_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
size_t v_i_boxed_223_; size_t v_stop_boxed_224_; lean_object* v_res_225_; 
v_i_boxed_223_ = lean_unbox_usize(v_i_213_);
lean_dec(v_i_213_);
v_stop_boxed_224_ = lean_unbox_usize(v_stop_214_);
lean_dec(v_stop_214_);
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1(v_as_212_, v_i_boxed_223_, v_stop_boxed_224_, v_b_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec_ref(v_as_212_);
return v_res_225_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(lean_object* v_00_u03b2_226_, lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_227_, v_x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_230_, lean_object* v_a_231_, lean_object* v_x_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(v_00_u03b2_230_, v_a_231_, v_x_232_);
lean_dec(v_x_232_);
lean_dec(v_a_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
return v_x_235_;
}
else
{
lean_object* v_key_237_; lean_object* v_value_238_; lean_object* v_tail_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_262_; 
v_key_237_ = lean_ctor_get(v_x_236_, 0);
v_value_238_ = lean_ctor_get(v_x_236_, 1);
v_tail_239_ = lean_ctor_get(v_x_236_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_262_ == 0)
{
v___x_241_ = v_x_236_;
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_tail_239_);
lean_inc(v_value_238_);
lean_inc(v_key_237_);
lean_dec(v_x_236_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v_fold_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_243_ = lean_array_get_size(v_x_235_);
v___x_244_ = l_Lean_instHashableFVarId_hash(v_key_237_);
v___x_245_ = 32ULL;
v___x_246_ = lean_uint64_shift_right(v___x_244_, v___x_245_);
v_fold_247_ = lean_uint64_xor(v___x_244_, v___x_246_);
v___x_248_ = 16ULL;
v___x_249_ = lean_uint64_shift_right(v_fold_247_, v___x_248_);
v___x_250_ = lean_uint64_xor(v_fold_247_, v___x_249_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = lean_usize_of_nat(v___x_243_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v___x_252_, v___x_253_);
v___x_255_ = lean_usize_land(v___x_251_, v___x_254_);
v___x_256_ = lean_array_uget_borrowed(v_x_235_, v___x_255_);
lean_inc(v___x_256_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v___x_256_);
v___x_258_ = v___x_241_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_key_237_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_value_238_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v___x_256_);
v___x_258_ = v_reuseFailAlloc_261_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = lean_array_uset(v_x_235_, v___x_255_, v___x_258_);
v_x_235_ = v___x_259_;
v_x_236_ = v_tail_239_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_263_, lean_object* v_source_264_, lean_object* v_target_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_source_264_);
v___x_267_ = lean_nat_dec_lt(v_i_263_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_source_264_);
lean_dec(v_i_263_);
return v_target_265_;
}
else
{
lean_object* v_es_268_; lean_object* v___x_269_; lean_object* v_source_270_; lean_object* v_target_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_es_268_ = lean_array_fget(v_source_264_, v_i_263_);
v___x_269_ = lean_box(0);
v_source_270_ = lean_array_fset(v_source_264_, v_i_263_, v___x_269_);
v_target_271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3___redArg(v_target_265_, v_es_268_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_i_263_, v___x_272_);
lean_dec(v_i_263_);
v_i_263_ = v___x_273_;
v_source_264_ = v_source_270_;
v_target_265_ = v_target_271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___redArg(lean_object* v_data_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_nbuckets_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_276_ = lean_array_get_size(v_data_275_);
v___x_277_ = lean_unsigned_to_nat(2u);
v_nbuckets_278_ = lean_nat_mul(v___x_276_, v___x_277_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_box(0);
v___x_281_ = lean_mk_array(v_nbuckets_278_, v___x_280_);
v___x_282_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1___redArg(v___x_279_, v_data_275_, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* v_m_283_, lean_object* v_a_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_size_286_; lean_object* v_buckets_287_; lean_object* v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v_fold_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v_bkt_301_; uint8_t v___x_302_; 
v_size_286_ = lean_ctor_get(v_m_283_, 0);
v_buckets_287_ = lean_ctor_get(v_m_283_, 1);
v___x_288_ = lean_array_get_size(v_buckets_287_);
v___x_289_ = l_Lean_instHashableFVarId_hash(v_a_284_);
v___x_290_ = 32ULL;
v___x_291_ = lean_uint64_shift_right(v___x_289_, v___x_290_);
v_fold_292_ = lean_uint64_xor(v___x_289_, v___x_291_);
v___x_293_ = 16ULL;
v___x_294_ = lean_uint64_shift_right(v_fold_292_, v___x_293_);
v___x_295_ = lean_uint64_xor(v_fold_292_, v___x_294_);
v___x_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = lean_usize_of_nat(v___x_288_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_sub(v___x_297_, v___x_298_);
v___x_300_ = lean_usize_land(v___x_296_, v___x_299_);
v_bkt_301_ = lean_array_uget_borrowed(v_buckets_287_, v___x_300_);
v___x_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_284_, v_bkt_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_323_; 
lean_inc_ref(v_buckets_287_);
lean_inc(v_size_286_);
v_isSharedCheck_323_ = !lean_is_exclusive(v_m_283_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; 
v_unused_324_ = lean_ctor_get(v_m_283_, 1);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_m_283_, 0);
lean_dec(v_unused_325_);
v___x_304_ = v_m_283_;
v_isShared_305_ = v_isSharedCheck_323_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_m_283_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_323_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v_size_x27_307_; lean_object* v___x_308_; lean_object* v_buckets_x27_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_306_ = lean_unsigned_to_nat(1u);
v_size_x27_307_ = lean_nat_add(v_size_286_, v___x_306_);
lean_dec(v_size_286_);
lean_inc(v_bkt_301_);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v_a_284_);
lean_ctor_set(v___x_308_, 1, v_b_285_);
lean_ctor_set(v___x_308_, 2, v_bkt_301_);
v_buckets_x27_309_ = lean_array_uset(v_buckets_287_, v___x_300_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(4u);
v___x_311_ = lean_nat_mul(v_size_x27_307_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(3u);
v___x_313_ = lean_nat_div(v___x_311_, v___x_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_array_get_size(v_buckets_x27_309_);
v___x_315_ = lean_nat_dec_le(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
if (v___x_315_ == 0)
{
lean_object* v_val_316_; lean_object* v___x_318_; 
v_val_316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___redArg(v_buckets_x27_309_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v_val_316_);
lean_ctor_set(v___x_304_, 0, v_size_x27_307_);
v___x_318_ = v___x_304_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_x27_307_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_val_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_321_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v_buckets_x27_309_);
lean_ctor_set(v___x_304_, 0, v_size_x27_307_);
v___x_321_ = v___x_304_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_size_x27_307_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_buckets_x27_309_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_dec(v_b_285_);
lean_dec(v_a_284_);
return v_m_283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object* v_as_326_, size_t v_i_327_, size_t v_stop_328_, lean_object* v_b_329_, lean_object* v___y_330_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_eq(v_i_327_, v_stop_328_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v_rewriteCache_334_; lean_object* v_acNfCache_335_; lean_object* v_typeAnalysis_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_350_; 
v___x_333_ = lean_st_ref_take(v___y_330_);
v_rewriteCache_334_ = lean_ctor_get(v___x_333_, 0);
v_acNfCache_335_ = lean_ctor_get(v___x_333_, 1);
v_typeAnalysis_336_ = lean_ctor_get(v___x_333_, 2);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_350_ == 0)
{
v___x_338_ = v___x_333_;
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_typeAnalysis_336_);
lean_inc(v_acNfCache_335_);
lean_inc(v_rewriteCache_334_);
lean_dec(v___x_333_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_340_ = lean_array_uget_borrowed(v_as_326_, v_i_327_);
v___x_341_ = lean_box(0);
lean_inc(v___x_340_);
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_rewriteCache_334_, v___x_340_, v___x_341_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_342_);
v___x_344_ = v___x_338_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_acNfCache_335_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_typeAnalysis_336_);
v___x_344_ = v_reuseFailAlloc_349_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; size_t v___x_346_; size_t v___x_347_; 
v___x_345_ = lean_st_ref_set(v___y_330_, v___x_344_);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_327_, v___x_346_);
v_i_327_ = v___x_347_;
v_b_329_ = v___x_341_;
goto _start;
}
}
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v_b_329_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object* v_as_352_, lean_object* v_i_353_, lean_object* v_stop_354_, lean_object* v_b_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
size_t v_i_boxed_358_; size_t v_stop_boxed_359_; lean_object* v_res_360_; 
v_i_boxed_358_ = lean_unbox_usize(v_i_353_);
lean_dec(v_i_353_);
v_stop_boxed_359_ = lean_unbox_usize(v_stop_354_);
lean_dec(v_stop_354_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_as_352_, v_i_boxed_358_, v_stop_boxed_359_, v_b_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v_as_352_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object* v___x_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_getPropHyps(v___y_364_, v___y_365_, v___y_366_, v___y_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_390_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_390_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_390_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_390_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = lean_array_get_size(v_a_370_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_nat_dec_lt(v___x_361_, v___x_374_);
if (v___x_376_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_a_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_375_);
v___x_378_ = v___x_372_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_375_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_le(v___x_374_, v___x_374_);
if (v___x_380_ == 0)
{
if (v___x_376_ == 0)
{
lean_object* v___x_382_; 
lean_dec(v_a_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_375_);
v___x_382_ = v___x_372_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_375_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
lean_del_object(v___x_372_);
v___x_384_ = ((size_t)0ULL);
v___x_385_ = lean_usize_of_nat(v___x_374_);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_a_370_, v___x_384_, v___x_385_, v___x_375_, v___y_363_);
lean_dec(v_a_370_);
return v___x_386_;
}
}
else
{
size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
lean_del_object(v___x_372_);
v___x_387_ = ((size_t)0ULL);
v___x_388_ = lean_usize_of_nat(v___x_374_);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_a_370_, v___x_387_, v___x_388_, v___x_375_, v___y_363_);
lean_dec(v_a_370_);
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_369_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_369_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* v___x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v___x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___x_399_);
return v_res_407_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0(void){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(32u);
v___x_415_ = lean_mk_empty_array_with_capacity(v___x_414_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4(void){
_start:
{
size_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_417_ = ((size_t)5ULL);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_unsigned_to_nat(32u);
v___x_420_ = lean_mk_empty_array_with_capacity(v___x_419_);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3);
v___x_422_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_418_);
lean_ctor_set(v___x_422_, 3, v___x_418_);
lean_ctor_set_usize(v___x_422_, 4, v___x_417_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4);
v___x_424_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1);
v___x_425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
lean_ctor_set(v___x_425_, 3, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5);
v___x_427_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object* v_goal_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
v___x_440_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_439_, v___y_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeSimprocExt;
v___x_443_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(v___x_442_, v___y_437_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = l_Lean_Meta_getSEvalTheorems___redArg(v___y_437_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_447_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v___x_447_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v___y_437_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_437_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v_maxSteps_451_; lean_object* v___x_452_; uint8_t v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v_maxSteps_451_ = lean_ctor_get(v___y_432_, 1);
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = 0;
v___x_454_ = 1;
v___x_455_ = 0;
v___x_456_ = lean_box(0);
lean_inc(v_maxSteps_451_);
v___x_457_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_457_, 0, v_maxSteps_451_);
lean_ctor_set(v___x_457_, 1, v___x_452_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 1, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 2, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 3, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 4, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 5, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 6, v___x_455_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 7, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 8, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 9, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 10, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 11, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 12, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 13, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 14, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 15, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 16, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 17, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 18, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 19, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 20, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 21, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 22, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 23, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 24, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 25, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 26, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 27, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 28, v___x_454_);
v___x_458_ = lean_mk_empty_array_with_capacity(v___x_452_);
lean_inc_ref(v___x_458_);
v___x_459_ = lean_array_push(v___x_458_, v_a_441_);
v___x_460_ = lean_array_push(v___x_459_, v_a_446_);
v___x_461_ = l_Lean_Options_empty;
v___x_462_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_457_, v___x_460_, v_a_450_, v___x_461_, v___y_434_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
lean_inc(v_goal_431_);
v___x_464_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps(v_goal_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_524_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_524_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_524_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_524_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_array_get_size(v_a_465_);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_nat_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_del_object(v___x_467_);
v___x_472_ = lean_array_push(v___x_458_, v_a_444_);
v___x_473_ = lean_array_push(v___x_472_, v_a_448_);
v___x_474_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6);
v___x_475_ = l_Lean_Meta_simpGoal(v_goal_431_, v_a_463_, v___x_473_, v___x_456_, v___x_454_, v_a_465_, v___x_474_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_511_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_511_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_511_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_511_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_fst_480_; 
v_fst_480_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_fst_480_);
lean_dec(v_a_476_);
if (lean_obj_tag(v_fst_480_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_507_; 
lean_del_object(v___x_478_);
v_val_481_ = lean_ctor_get(v_fst_480_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_fst_480_);
if (v_isSharedCheck_507_ == 0)
{
v___x_483_ = v_fst_480_;
v_isShared_484_ = v_isSharedCheck_507_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v_fst_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_507_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_snd_485_; lean_object* v___f_486_; lean_object* v___x_487_; 
v_snd_485_ = lean_ctor_get(v_val_481_, 1);
lean_inc_n(v_snd_485_, 2);
lean_dec(v_val_481_);
v___f_486_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7));
v___x_487_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_snd_485_, v___f_486_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_497_; 
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_487_, 0);
lean_dec(v_unused_498_);
v___x_489_ = v___x_487_;
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
else
{
lean_dec(v___x_487_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v_snd_485_);
v___x_492_ = v___x_483_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_snd_485_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_492_);
v___x_494_ = v___x_489_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_snd_485_);
lean_del_object(v___x_483_);
v_a_499_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_487_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_487_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
else
{
lean_object* v___x_509_; 
lean_dec(v_fst_480_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_456_);
v___x_509_ = v___x_478_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_456_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_475_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_475_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_a_465_);
lean_dec(v_a_463_);
lean_dec_ref(v___x_458_);
lean_dec(v_a_448_);
lean_dec(v_a_444_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v_goal_431_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_520_);
v___x_522_ = v___x_467_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_463_);
lean_dec_ref(v___x_458_);
lean_dec(v_a_448_);
lean_dec(v_a_444_);
lean_dec(v_goal_431_);
v_a_525_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_464_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_464_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v___x_458_);
lean_dec(v_a_448_);
lean_dec(v_a_444_);
lean_dec(v_goal_431_);
v_a_533_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_462_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_462_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_448_);
lean_dec(v_a_446_);
lean_dec(v_a_444_);
lean_dec(v_a_441_);
lean_dec(v_goal_431_);
v_a_541_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_449_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_449_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_446_);
lean_dec(v_a_444_);
lean_dec(v_a_441_);
lean_dec(v_goal_431_);
v_a_549_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_447_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_447_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_a_444_);
lean_dec(v_a_441_);
lean_dec(v_goal_431_);
v_a_557_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_445_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_445_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
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
lean_dec(v_a_441_);
lean_dec(v_goal_431_);
v_a_565_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_443_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_443_);
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
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_goal_431_);
v_a_573_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_440_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_440_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object* v_goal_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(v_goal_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object* v_00_u03b2_598_, lean_object* v_m_599_, lean_object* v_a_600_, lean_object* v_b_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_m_599_, v_a_600_, v_b_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object* v_as_603_, size_t v_i_604_, size_t v_stop_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_as_603_, v_i_604_, v_stop_605_, v_b_606_, v___y_608_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object* v_as_615_, lean_object* v_i_616_, lean_object* v_stop_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
size_t v_i_boxed_626_; size_t v_stop_boxed_627_; lean_object* v_res_628_; 
v_i_boxed_626_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_stop_boxed_627_ = lean_unbox_usize(v_stop_617_);
lean_dec(v_stop_617_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(v_as_615_, v_i_boxed_626_, v_stop_boxed_627_, v_b_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v_as_615_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(lean_object* v_00_u03b2_629_, lean_object* v_data_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___redArg(v_data_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_632_, lean_object* v_i_633_, lean_object* v_source_634_, lean_object* v_target_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1___redArg(v_i_633_, v_source_634_, v_target_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3___redArg(v_x_638_, v_x_639_);
return v___x_640_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
