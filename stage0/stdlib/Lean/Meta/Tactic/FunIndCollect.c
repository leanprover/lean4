// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndCollect
// Imports: public import Lean.Meta.Tactic.Util public import Lean.Meta.Tactic.FunIndInfo
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_filter(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_FunInd_instHashableCall_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instHashableCall_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_FunInd_instHashableCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_FunInd_instHashableCall_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_FunInd_instHashableCall___closed__0 = (const lean_object*)&l_Lean_Meta_FunInd_instHashableCall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_FunInd_instHashableCall = (const lean_object*)&l_Lean_Meta_FunInd_instHashableCall___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_instBEqCall_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instBEqCall_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_FunInd_instBEqCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_FunInd_instBEqCall_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_FunInd_instBEqCall___closed__0 = (const lean_object*)&l_Lean_Meta_FunInd_instBEqCall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_FunInd_instBEqCall = (const lean_object*)&l_Lean_Meta_FunInd_instBEqCall___closed__0_value;
static const lean_array_object l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0 = (const lean_object*)&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0_value;
static lean_once_cell_t l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1;
static lean_once_cell_t l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2;
static lean_once_cell_t l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls;
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_FunInd_Collector_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_Collector_visit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_FunInd_Collector_main___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_Collector_main___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_FunInd_instHashableCall_hash(lean_object* v_x_1_){
_start:
{
lean_object* v_expr_2_; lean_object* v_relevantArgs_3_; uint64_t v___x_4_; uint64_t v___x_5_; uint64_t v___x_6_; uint64_t v___x_7_; uint64_t v___x_8_; 
v_expr_2_ = lean_ctor_get(v_x_1_, 0);
v_relevantArgs_3_ = lean_ctor_get(v_x_1_, 1);
v___x_4_ = 0ULL;
v___x_5_ = l_Lean_Expr_hash(v_expr_2_);
v___x_6_ = lean_uint64_mix_hash(v___x_4_, v___x_5_);
v___x_7_ = l_Lean_Expr_hash(v_relevantArgs_3_);
v___x_8_ = lean_uint64_mix_hash(v___x_6_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instHashableCall_hash___boxed(lean_object* v_x_9_){
_start:
{
uint64_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Lean_Meta_FunInd_instHashableCall_hash(v_x_9_);
lean_dec_ref(v_x_9_);
v_r_11_ = lean_box_uint64(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_instBEqCall_beq(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
lean_object* v_expr_16_; lean_object* v_relevantArgs_17_; lean_object* v_expr_18_; lean_object* v_relevantArgs_19_; uint8_t v___x_20_; 
v_expr_16_ = lean_ctor_get(v_x_14_, 0);
v_relevantArgs_17_ = lean_ctor_get(v_x_14_, 1);
v_expr_18_ = lean_ctor_get(v_x_15_, 0);
v_relevantArgs_19_ = lean_ctor_get(v_x_15_, 1);
v___x_20_ = lean_expr_eqv(v_expr_16_, v_expr_18_);
if (v___x_20_ == 0)
{
return v___x_20_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = lean_expr_eqv(v_relevantArgs_17_, v_relevantArgs_19_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instBEqCall_beq___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_Meta_FunInd_instBEqCall_beq(v_x_22_, v_x_23_);
lean_dec_ref(v_x_23_);
lean_dec_ref(v_x_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box(0);
v___x_31_ = lean_unsigned_to_nat(16u);
v___x_32_ = lean_mk_array(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2);
v___x_37_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_isEmpty(lean_object* v_sc_40_){
_start:
{
lean_object* v_calls_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_calls_41_ = lean_ctor_get(v_sc_40_, 0);
v___x_42_ = lean_array_get_size(v_calls_41_);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_nat_dec_eq(v___x_42_, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(lean_object* v_sc_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Meta_FunInd_SeenCalls_isEmpty(v_sc_45_);
lean_dec_ref(v_sc_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(lean_object* v_xs_48_, lean_object* v_ys_49_, lean_object* v_x_50_){
_start:
{
lean_object* v_zero_51_; uint8_t v_isZero_52_; 
v_zero_51_ = lean_unsigned_to_nat(0u);
v_isZero_52_ = lean_nat_dec_eq(v_x_50_, v_zero_51_);
if (v_isZero_52_ == 1)
{
lean_dec(v_x_50_);
return v_isZero_52_;
}
else
{
lean_object* v_one_53_; lean_object* v_n_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_one_53_ = lean_unsigned_to_nat(1u);
v_n_54_ = lean_nat_sub(v_x_50_, v_one_53_);
lean_dec(v_x_50_);
v___x_55_ = lean_array_fget_borrowed(v_xs_48_, v_n_54_);
v___x_56_ = lean_array_fget_borrowed(v_ys_49_, v_n_54_);
v___x_57_ = lean_expr_eqv(v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_dec(v_n_54_);
return v___x_57_;
}
else
{
v_x_50_ = v_n_54_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_xs_59_, lean_object* v_ys_60_, lean_object* v_x_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_59_, v_ys_60_, v_x_61_);
lean_dec_ref(v_ys_60_);
lean_dec_ref(v_xs_59_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
else
{
lean_object* v_key_67_; lean_object* v_tail_68_; uint8_t v___y_70_; lean_object* v_fst_72_; lean_object* v_snd_73_; lean_object* v_fst_74_; lean_object* v_snd_75_; uint8_t v___x_76_; 
v_key_67_ = lean_ctor_get(v_x_65_, 0);
v_tail_68_ = lean_ctor_get(v_x_65_, 2);
v_fst_72_ = lean_ctor_get(v_key_67_, 0);
v_snd_73_ = lean_ctor_get(v_key_67_, 1);
v_fst_74_ = lean_ctor_get(v_a_64_, 0);
v_snd_75_ = lean_ctor_get(v_a_64_, 1);
v___x_76_ = lean_name_eq(v_fst_72_, v_fst_74_);
if (v___x_76_ == 0)
{
v___y_70_ = v___x_76_;
goto v___jp_69_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_array_get_size(v_snd_73_);
v___x_78_ = lean_array_get_size(v_snd_75_);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
v_x_65_ = v_tail_68_;
goto _start;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_snd_73_, v_snd_75_, v___x_77_);
v___y_70_ = v___x_81_;
goto v___jp_69_;
}
}
v___jp_69_:
{
if (v___y_70_ == 0)
{
v_x_65_ = v_tail_68_;
goto _start;
}
else
{
return v___y_70_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg___boxed(lean_object* v_a_82_, lean_object* v_x_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_82_, v_x_83_);
lean_dec(v_x_83_);
lean_dec_ref(v_a_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(lean_object* v_as_86_, size_t v_i_87_, size_t v_stop_88_, uint64_t v_b_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_usize_dec_eq(v_i_87_, v_stop_88_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; size_t v___x_94_; size_t v___x_95_; 
v___x_91_ = lean_array_uget_borrowed(v_as_86_, v_i_87_);
v___x_92_ = l_Lean_Expr_hash(v___x_91_);
v___x_93_ = lean_uint64_mix_hash(v_b_89_, v___x_92_);
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_add(v_i_87_, v___x_94_);
v_i_87_ = v___x_95_;
v_b_89_ = v___x_93_;
goto _start;
}
else
{
return v_b_89_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2___boxed(lean_object* v_as_97_, lean_object* v_i_98_, lean_object* v_stop_99_, lean_object* v_b_100_){
_start:
{
size_t v_i_boxed_101_; size_t v_stop_boxed_102_; uint64_t v_b_boxed_103_; uint64_t v_res_104_; lean_object* v_r_105_; 
v_i_boxed_101_ = lean_unbox_usize(v_i_98_);
lean_dec(v_i_98_);
v_stop_boxed_102_ = lean_unbox_usize(v_stop_99_);
lean_dec(v_stop_99_);
v_b_boxed_103_ = lean_unbox_uint64(v_b_100_);
lean_dec_ref(v_b_100_);
v_res_104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_as_97_, v_i_boxed_101_, v_stop_boxed_102_, v_b_boxed_103_);
lean_dec_ref(v_as_97_);
v_r_105_ = lean_box_uint64(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
return v_x_106_;
}
else
{
lean_object* v_key_108_; lean_object* v_value_109_; lean_object* v_tail_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_149_; 
v_key_108_ = lean_ctor_get(v_x_107_, 0);
v_value_109_ = lean_ctor_get(v_x_107_, 1);
v_tail_110_ = lean_ctor_get(v_x_107_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_107_);
if (v_isSharedCheck_149_ == 0)
{
v___x_112_ = v_x_107_;
v_isShared_113_ = v_isSharedCheck_149_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_tail_110_);
lean_inc(v_value_109_);
lean_inc(v_key_108_);
lean_dec(v_x_107_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_149_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v___x_116_; uint64_t v___y_118_; uint64_t v___y_119_; uint64_t v___y_139_; 
v_fst_114_ = lean_ctor_get(v_key_108_, 0);
v_snd_115_ = lean_ctor_get(v_key_108_, 1);
v___x_116_ = lean_array_get_size(v_x_106_);
if (lean_obj_tag(v_fst_114_) == 0)
{
uint64_t v___x_147_; 
v___x_147_ = 1723ULL;
v___y_139_ = v___x_147_;
goto v___jp_138_;
}
else
{
uint64_t v_hash_148_; 
v_hash_148_ = lean_ctor_get_uint64(v_fst_114_, sizeof(void*)*2);
v___y_139_ = v_hash_148_;
goto v___jp_138_;
}
v___jp_117_:
{
uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_120_ = lean_uint64_mix_hash(v___y_118_, v___y_119_);
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___x_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___x_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_116_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v___x_132_ = lean_array_uget_borrowed(v_x_106_, v___x_131_);
lean_inc(v___x_132_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 2, v___x_132_);
v___x_134_ = v___x_112_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_key_108_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_value_109_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v___x_132_);
v___x_134_ = v_reuseFailAlloc_137_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = lean_array_uset(v_x_106_, v___x_131_, v___x_134_);
v_x_106_ = v___x_135_;
v_x_107_ = v_tail_110_;
goto _start;
}
}
v___jp_138_:
{
uint64_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = 7ULL;
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_array_get_size(v_snd_115_);
v___x_143_ = lean_nat_dec_lt(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
v___y_118_ = v___y_139_;
v___y_119_ = v___x_140_;
goto v___jp_117_;
}
else
{
size_t v___x_144_; size_t v___x_145_; uint64_t v___x_146_; 
v___x_144_ = ((size_t)0ULL);
v___x_145_ = lean_usize_of_nat(v___x_142_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_115_, v___x_144_, v___x_145_, v___x_140_);
v___y_118_ = v___y_139_;
v___y_119_ = v___x_146_;
goto v___jp_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(lean_object* v_i_150_, lean_object* v_source_151_, lean_object* v_target_152_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_array_get_size(v_source_151_);
v___x_154_ = lean_nat_dec_lt(v_i_150_, v___x_153_);
if (v___x_154_ == 0)
{
lean_dec_ref(v_source_151_);
lean_dec(v_i_150_);
return v_target_152_;
}
else
{
lean_object* v_es_155_; lean_object* v___x_156_; lean_object* v_source_157_; lean_object* v_target_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_es_155_ = lean_array_fget(v_source_151_, v_i_150_);
v___x_156_ = lean_box(0);
v_source_157_ = lean_array_fset(v_source_151_, v_i_150_, v___x_156_);
v_target_158_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_target_152_, v_es_155_);
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_add(v_i_150_, v___x_159_);
lean_dec(v_i_150_);
v_i_150_ = v___x_160_;
v_source_151_ = v_source_157_;
v_target_152_ = v_target_158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(lean_object* v_data_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_nbuckets_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_163_ = lean_array_get_size(v_data_162_);
v___x_164_ = lean_unsigned_to_nat(2u);
v_nbuckets_165_ = lean_nat_mul(v___x_163_, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_box(0);
v___x_168_ = lean_mk_array(v_nbuckets_165_, v___x_167_);
v___x_169_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_166_, v_data_162_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object* v_m_170_, lean_object* v_a_171_, lean_object* v_b_172_){
_start:
{
lean_object* v_size_173_; lean_object* v_buckets_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_177_; uint64_t v___y_179_; uint64_t v___y_180_; uint64_t v___y_219_; 
v_size_173_ = lean_ctor_get(v_m_170_, 0);
v_buckets_174_ = lean_ctor_get(v_m_170_, 1);
v_fst_175_ = lean_ctor_get(v_a_171_, 0);
v_snd_176_ = lean_ctor_get(v_a_171_, 1);
v___x_177_ = lean_array_get_size(v_buckets_174_);
if (lean_obj_tag(v_fst_175_) == 0)
{
uint64_t v___x_227_; 
v___x_227_ = 1723ULL;
v___y_219_ = v___x_227_;
goto v___jp_218_;
}
else
{
uint64_t v_hash_228_; 
v_hash_228_ = lean_ctor_get_uint64(v_fst_175_, sizeof(void*)*2);
v___y_219_ = v_hash_228_;
goto v___jp_218_;
}
v___jp_178_:
{
uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v_fold_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v_bkt_193_; uint8_t v___x_194_; 
v___x_181_ = lean_uint64_mix_hash(v___y_179_, v___y_180_);
v___x_182_ = 32ULL;
v___x_183_ = lean_uint64_shift_right(v___x_181_, v___x_182_);
v_fold_184_ = lean_uint64_xor(v___x_181_, v___x_183_);
v___x_185_ = 16ULL;
v___x_186_ = lean_uint64_shift_right(v_fold_184_, v___x_185_);
v___x_187_ = lean_uint64_xor(v_fold_184_, v___x_186_);
v___x_188_ = lean_uint64_to_usize(v___x_187_);
v___x_189_ = lean_usize_of_nat(v___x_177_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_sub(v___x_189_, v___x_190_);
v___x_192_ = lean_usize_land(v___x_188_, v___x_191_);
v_bkt_193_ = lean_array_uget_borrowed(v_buckets_174_, v___x_192_);
v___x_194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_171_, v_bkt_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_215_; 
lean_inc_ref(v_buckets_174_);
lean_inc(v_size_173_);
v_isSharedCheck_215_ = !lean_is_exclusive(v_m_170_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; lean_object* v_unused_217_; 
v_unused_216_ = lean_ctor_get(v_m_170_, 1);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_m_170_, 0);
lean_dec(v_unused_217_);
v___x_196_ = v_m_170_;
v_isShared_197_ = v_isSharedCheck_215_;
goto v_resetjp_195_;
}
else
{
lean_dec(v_m_170_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_215_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v_size_x27_199_; lean_object* v___x_200_; lean_object* v_buckets_x27_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v_size_x27_199_ = lean_nat_add(v_size_173_, v___x_198_);
lean_dec(v_size_173_);
lean_inc(v_bkt_193_);
v___x_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_200_, 0, v_a_171_);
lean_ctor_set(v___x_200_, 1, v_b_172_);
lean_ctor_set(v___x_200_, 2, v_bkt_193_);
v_buckets_x27_201_ = lean_array_uset(v_buckets_174_, v___x_192_, v___x_200_);
v___x_202_ = lean_unsigned_to_nat(4u);
v___x_203_ = lean_nat_mul(v_size_x27_199_, v___x_202_);
v___x_204_ = lean_unsigned_to_nat(3u);
v___x_205_ = lean_nat_div(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_array_get_size(v_buckets_x27_201_);
v___x_207_ = lean_nat_dec_le(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
if (v___x_207_ == 0)
{
lean_object* v_val_208_; lean_object* v___x_210_; 
v_val_208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_201_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v_val_208_);
lean_ctor_set(v___x_196_, 0, v_size_x27_199_);
v___x_210_ = v___x_196_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_size_x27_199_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_val_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
else
{
lean_object* v___x_213_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v_buckets_x27_201_);
lean_ctor_set(v___x_196_, 0, v_size_x27_199_);
v___x_213_ = v___x_196_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_size_x27_199_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_buckets_x27_201_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_dec(v_b_172_);
lean_dec_ref(v_a_171_);
return v_m_170_;
}
}
v___jp_218_:
{
uint64_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_220_ = 7ULL;
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_array_get_size(v_snd_176_);
v___x_223_ = lean_nat_dec_lt(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
v___y_179_ = v___y_219_;
v___y_180_ = v___x_220_;
goto v___jp_178_;
}
else
{
size_t v___x_224_; size_t v___x_225_; uint64_t v___x_226_; 
v___x_224_ = ((size_t)0ULL);
v___x_225_ = lean_usize_of_nat(v___x_222_);
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_176_, v___x_224_, v___x_225_, v___x_220_);
v___y_179_ = v___y_219_;
v___y_180_ = v___x_226_;
goto v___jp_178_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object* v_m_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_buckets_231_; lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v___x_234_; uint64_t v___y_236_; uint64_t v___y_237_; uint64_t v___y_253_; 
v_buckets_231_ = lean_ctor_get(v_m_229_, 1);
v_fst_232_ = lean_ctor_get(v_a_230_, 0);
v_snd_233_ = lean_ctor_get(v_a_230_, 1);
v___x_234_ = lean_array_get_size(v_buckets_231_);
if (lean_obj_tag(v_fst_232_) == 0)
{
uint64_t v___x_261_; 
v___x_261_ = 1723ULL;
v___y_253_ = v___x_261_;
goto v___jp_252_;
}
else
{
uint64_t v_hash_262_; 
v_hash_262_ = lean_ctor_get_uint64(v_fst_232_, sizeof(void*)*2);
v___y_253_ = v_hash_262_;
goto v___jp_252_;
}
v___jp_235_:
{
uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v_fold_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_238_ = lean_uint64_mix_hash(v___y_236_, v___y_237_);
v___x_239_ = 32ULL;
v___x_240_ = lean_uint64_shift_right(v___x_238_, v___x_239_);
v_fold_241_ = lean_uint64_xor(v___x_238_, v___x_240_);
v___x_242_ = 16ULL;
v___x_243_ = lean_uint64_shift_right(v_fold_241_, v___x_242_);
v___x_244_ = lean_uint64_xor(v_fold_241_, v___x_243_);
v___x_245_ = lean_uint64_to_usize(v___x_244_);
v___x_246_ = lean_usize_of_nat(v___x_234_);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_sub(v___x_246_, v___x_247_);
v___x_249_ = lean_usize_land(v___x_245_, v___x_248_);
v___x_250_ = lean_array_uget_borrowed(v_buckets_231_, v___x_249_);
v___x_251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_230_, v___x_250_);
return v___x_251_;
}
v___jp_252_:
{
uint64_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = 7ULL;
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_array_get_size(v_snd_233_);
v___x_257_ = lean_nat_dec_lt(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
v___y_236_ = v___y_253_;
v___y_237_ = v___x_254_;
goto v___jp_235_;
}
else
{
size_t v___x_258_; size_t v___x_259_; uint64_t v___x_260_; 
v___x_258_ = ((size_t)0ULL);
v___x_259_ = lean_usize_of_nat(v___x_256_);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_233_, v___x_258_, v___x_259_, v___x_254_);
v___y_236_ = v___y_253_;
v___y_237_ = v___x_260_;
goto v___jp_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_263_, v_a_264_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_m_263_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object* v_calls_267_, lean_object* v_as_268_, size_t v_sz_269_, size_t v_i_270_, lean_object* v_b_271_){
_start:
{
lean_object* v_a_274_; uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_lt(v_i_270_, v_sz_269_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec_ref(v_calls_267_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_b_271_);
return v___x_279_;
}
else
{
lean_object* v_snd_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_337_; 
v_snd_280_ = lean_ctor_get(v_b_271_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_b_271_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_b_271_, 0);
lean_dec(v_unused_338_);
v___x_282_ = v_b_271_;
v_isShared_283_ = v_isSharedCheck_337_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_snd_280_);
lean_dec(v_b_271_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_337_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_snd_284_; lean_object* v_fst_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_336_; 
v_snd_284_ = lean_ctor_get(v_snd_280_, 1);
v_fst_285_ = lean_ctor_get(v_snd_280_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_snd_280_);
if (v_isSharedCheck_336_ == 0)
{
v___x_287_ = v_snd_280_;
v_isShared_288_ = v_isSharedCheck_336_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_snd_284_);
lean_inc(v_fst_285_);
lean_dec(v_snd_280_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_336_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_array_289_; lean_object* v_start_290_; lean_object* v_stop_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_array_289_ = lean_ctor_get(v_snd_284_, 0);
v_start_290_ = lean_ctor_get(v_snd_284_, 1);
v_stop_291_ = lean_ctor_get(v_snd_284_, 2);
v___x_292_ = lean_box(0);
v___x_293_ = lean_nat_dec_lt(v_start_290_, v_stop_291_);
if (v___x_293_ == 0)
{
lean_object* v___x_295_; 
lean_dec_ref(v_calls_267_);
if (v_isShared_288_ == 0)
{
v___x_295_ = v___x_287_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_fst_285_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_snd_284_);
v___x_295_ = v_reuseFailAlloc_300_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_295_);
lean_ctor_set(v___x_282_, 0, v___x_292_);
v___x_297_ = v___x_282_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
}
else
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_332_; 
lean_inc(v_stop_291_);
lean_inc(v_start_290_);
lean_inc_ref(v_array_289_);
v_isSharedCheck_332_ = !lean_is_exclusive(v_snd_284_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_333_ = lean_ctor_get(v_snd_284_, 2);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_snd_284_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_snd_284_, 0);
lean_dec(v_unused_335_);
v___x_302_ = v_snd_284_;
v_isShared_303_ = v_isSharedCheck_332_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_snd_284_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_332_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_a_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v_a_304_ = lean_array_uget_borrowed(v_as_268_, v_i_270_);
v___x_305_ = lean_array_fget(v_array_289_, v_start_290_);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_start_290_, v___x_306_);
lean_dec(v_start_290_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_307_);
v___x_309_ = v___x_302_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_array_289_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_stop_291_);
v___x_309_ = v_reuseFailAlloc_331_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
uint8_t v___x_325_; 
v___x_325_ = lean_unbox(v___x_305_);
if (v___x_325_ == 2)
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_Expr_isFVar(v_a_304_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v___x_305_);
lean_del_object(v___x_287_);
lean_del_object(v___x_282_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v_calls_267_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_fst_285_);
lean_ctor_set(v___x_328_, 1, v___x_309_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
else
{
goto v___jp_310_;
}
}
else
{
goto v___jp_310_;
}
v___jp_310_:
{
uint8_t v___x_311_; 
v___x_311_ = lean_unbox(v___x_305_);
lean_dec(v___x_305_);
if (v___x_311_ == 0)
{
lean_object* v___x_313_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_309_);
v___x_313_ = v___x_287_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_fst_285_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_309_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_313_);
lean_ctor_set(v___x_282_, 0, v___x_292_);
v___x_315_ = v___x_282_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
v_a_274_ = v___x_315_;
goto v___jp_273_;
}
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_320_; 
lean_inc(v_a_304_);
v___x_318_ = lean_array_push(v_fst_285_, v_a_304_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_309_);
lean_ctor_set(v___x_287_, 0, v___x_318_);
v___x_320_ = v___x_287_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_309_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_320_);
lean_ctor_set(v___x_282_, 0, v___x_292_);
v___x_322_ = v___x_282_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
v_a_274_ = v___x_322_;
goto v___jp_273_;
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
v___jp_273_:
{
size_t v___x_275_; size_t v___x_276_; 
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_270_, v___x_275_);
v_i_270_ = v___x_276_;
v_b_271_ = v_a_274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object* v_calls_339_, lean_object* v_as_340_, lean_object* v_sz_341_, lean_object* v_i_342_, lean_object* v_b_343_, lean_object* v___y_344_){
_start:
{
size_t v_sz_boxed_345_; size_t v_i_boxed_346_; lean_object* v_res_347_; 
v_sz_boxed_345_ = lean_unbox_usize(v_sz_341_);
lean_dec(v_sz_341_);
v_i_boxed_346_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_339_, v_as_340_, v_sz_boxed_345_, v_i_boxed_346_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object* v_e_348_, lean_object* v_funIndInfo_349_, lean_object* v_args_350_, lean_object* v_calls_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_funName_357_; lean_object* v_params_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_funName_357_ = lean_ctor_get(v_funIndInfo_349_, 0);
lean_inc(v_funName_357_);
v_params_358_ = lean_ctor_get(v_funIndInfo_349_, 3);
lean_inc_ref(v_params_358_);
lean_dec_ref(v_funIndInfo_349_);
v___x_359_ = lean_array_get_size(v_params_358_);
v___x_360_ = lean_array_get_size(v_args_350_);
v___x_361_ = lean_nat_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v_params_358_);
lean_dec(v_funName_357_);
lean_dec_ref(v_e_348_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v_calls_351_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; lean_object* v_keys_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v_keys_364_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_365_ = l_Array_toSubarray___redArg(v_params_358_, v___x_363_, v___x_359_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_keys_364_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v_sz_369_ = lean_array_size(v_args_350_);
v___x_370_ = ((size_t)0ULL);
lean_inc_ref(v_calls_351_);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_351_, v_args_350_, v_sz_369_, v___x_370_, v___x_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_412_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_412_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_412_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_412_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_fst_376_; 
v_fst_376_ = lean_ctor_get(v_a_372_, 0);
if (lean_obj_tag(v_fst_376_) == 0)
{
lean_object* v_snd_377_; lean_object* v_fst_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_406_; 
v_snd_377_ = lean_ctor_get(v_a_372_, 1);
lean_inc(v_snd_377_);
lean_dec(v_a_372_);
v_fst_378_ = lean_ctor_get(v_snd_377_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_snd_377_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_snd_377_, 1);
lean_dec(v_unused_407_);
v___x_380_ = v_snd_377_;
v_isShared_381_ = v_isSharedCheck_406_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_fst_378_);
lean_dec(v_snd_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_406_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_calls_382_; lean_object* v_seen_383_; lean_object* v___x_385_; 
v_calls_382_ = lean_ctor_get(v_calls_351_, 0);
v_seen_383_ = lean_ctor_get(v_calls_351_, 1);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_fst_378_);
lean_ctor_set(v___x_380_, 0, v_funName_357_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_funName_357_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_fst_378_);
v___x_385_ = v_reuseFailAlloc_405_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
uint8_t v___x_386_; 
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_383_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_399_; 
lean_inc_ref(v_seen_383_);
lean_inc_ref(v_calls_382_);
v_isSharedCheck_399_ = !lean_is_exclusive(v_calls_351_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; 
v_unused_400_ = lean_ctor_get(v_calls_351_, 1);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_calls_351_, 0);
lean_dec(v_unused_401_);
v___x_388_ = v_calls_351_;
v_isShared_389_ = v_isSharedCheck_399_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_calls_351_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_399_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_390_ = lean_array_push(v_calls_382_, v_e_348_);
v___x_391_ = lean_box(0);
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_383_, v___x_385_, v___x_391_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_392_);
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_394_);
v___x_396_ = v___x_374_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
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
else
{
lean_object* v___x_403_; 
lean_dec_ref(v___x_385_);
lean_dec_ref(v_e_348_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v_calls_351_);
v___x_403_ = v___x_374_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_calls_351_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
else
{
lean_object* v_val_408_; lean_object* v___x_410_; 
lean_inc_ref(v_fst_376_);
lean_dec(v_a_372_);
lean_dec(v_funName_357_);
lean_dec_ref(v_calls_351_);
lean_dec_ref(v_e_348_);
v_val_408_ = lean_ctor_get(v_fst_376_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v_fst_376_, 1);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v_val_408_);
v___x_410_ = v___x_374_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_val_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_funName_357_);
lean_dec_ref(v_calls_351_);
lean_dec_ref(v_e_348_);
v_a_413_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_371_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_371_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object* v_e_421_, lean_object* v_funIndInfo_422_, lean_object* v_args_423_, lean_object* v_calls_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_421_, v_funIndInfo_422_, v_args_423_, v_calls_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec_ref(v_args_423_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object* v_calls_431_, lean_object* v_as_432_, size_t v_sz_433_, size_t v_i_434_, lean_object* v_b_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_431_, v_as_432_, v_sz_433_, v_i_434_, v_b_435_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object* v_calls_442_, lean_object* v_as_443_, lean_object* v_sz_444_, lean_object* v_i_445_, lean_object* v_b_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_444_);
lean_dec(v_sz_444_);
v_i_boxed_453_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_442_, v_as_443_, v_sz_boxed_452_, v_i_boxed_453_, v_b_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec_ref(v_as_443_);
return v_res_454_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object* v_00_u03b2_455_, lean_object* v_m_456_, lean_object* v_a_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_456_, v_a_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object* v_00_u03b2_459_, lean_object* v_m_460_, lean_object* v_a_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(v_00_u03b2_459_, v_m_460_, v_a_461_);
lean_dec_ref(v_a_461_);
lean_dec_ref(v_m_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object* v_00_u03b2_464_, lean_object* v_m_465_, lean_object* v_a_466_, lean_object* v_b_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_465_, v_a_466_, v_b_467_);
return v___x_468_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object* v_00_u03b2_469_, lean_object* v_a_470_, lean_object* v_x_471_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_470_, v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object* v_00_u03b2_473_, lean_object* v_a_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_473_, v_a_474_, v_x_475_);
lean_dec(v_x_475_);
lean_dec_ref(v_a_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object* v_00_u03b2_478_, lean_object* v_data_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_479_);
return v___x_480_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(lean_object* v_xs_481_, lean_object* v_ys_482_, lean_object* v_hsz_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_481_, v_ys_482_, v_x_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_487_, lean_object* v_ys_488_, lean_object* v_hsz_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_487_, v_ys_488_, v_hsz_489_, v_x_490_, v_x_491_);
lean_dec_ref(v_ys_488_);
lean_dec_ref(v_xs_487_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_494_, lean_object* v_i_495_, lean_object* v_source_496_, lean_object* v_target_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_495_, v_source_496_, v_target_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_500_, v_x_501_);
return v___x_502_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object* v_snd_503_, lean_object* v_x_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = l_Lean_NameSet_contains(v_snd_503_, v_x_504_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; 
v___x_506_ = 1;
return v___x_506_;
}
else
{
uint8_t v___x_507_; 
v___x_507_ = 0;
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object* v_snd_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec(v_snd_508_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
if (lean_obj_tag(v_a_512_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_a_513_);
return v___x_514_;
}
else
{
lean_object* v_key_515_; lean_object* v_tail_516_; lean_object* v_fst_517_; lean_object* v_fst_518_; lean_object* v_snd_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_539_; 
v_key_515_ = lean_ctor_get(v_a_512_, 0);
lean_inc(v_key_515_);
v_tail_516_ = lean_ctor_get(v_a_512_, 2);
lean_inc(v_tail_516_);
lean_dec_ref_known(v_a_512_, 3);
v_fst_517_ = lean_ctor_get(v_key_515_, 0);
lean_inc(v_fst_517_);
lean_dec(v_key_515_);
v_fst_518_ = lean_ctor_get(v_a_513_, 0);
v_snd_519_ = lean_ctor_get(v_a_513_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_539_ == 0)
{
v___x_521_ = v_a_513_;
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_519_);
lean_inc(v_fst_518_);
lean_dec(v_a_513_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v___x_523_; 
v___x_523_ = l_Lean_NameSet_contains(v_snd_519_, v_fst_517_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_NameSet_contains(v_fst_518_, v_fst_517_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = l_Lean_NameSet_insert(v_fst_518_, v_fst_517_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_snd_519_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v_a_512_ = v_tail_516_;
v_a_513_ = v___x_527_;
goto _start;
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = l_Lean_NameSet_insert(v_snd_519_, v_fst_517_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_530_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_518_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_534_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v_a_512_ = v_tail_516_;
v_a_513_ = v___x_532_;
goto _start;
}
}
}
else
{
lean_object* v___x_536_; 
lean_dec(v_fst_517_);
if (v_isShared_522_ == 0)
{
v___x_536_ = v___x_521_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_fst_518_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_snd_519_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
v_a_512_ = v_tail_516_;
v_a_513_ = v___x_536_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(lean_object* v_as_540_, size_t v_sz_541_, size_t v_i_542_, lean_object* v_b_543_){
_start:
{
uint8_t v___x_544_; 
v___x_544_ = lean_usize_dec_lt(v_i_542_, v_sz_541_);
if (v___x_544_ == 0)
{
return v_b_543_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_546_; 
v_a_545_ = lean_array_uget_borrowed(v_as_540_, v_i_542_);
lean_inc(v_a_545_);
v___x_546_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_545_, v_b_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
return v_a_547_;
}
else
{
lean_object* v_a_548_; size_t v___x_549_; size_t v___x_550_; 
v_a_548_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_546_, 1);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_542_, v___x_549_);
v_i_542_ = v___x_550_;
v_b_543_ = v_a_548_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(lean_object* v_as_552_, lean_object* v_sz_553_, lean_object* v_i_554_, lean_object* v_b_555_){
_start:
{
size_t v_sz_boxed_556_; size_t v_i_boxed_557_; lean_object* v_res_558_; 
v_sz_boxed_556_ = lean_unbox_usize(v_sz_553_);
lean_dec(v_sz_553_);
v_i_boxed_557_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_res_558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_552_, v_sz_boxed_556_, v_i_boxed_557_, v_b_555_);
lean_dec_ref(v_as_552_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0(void){
_start:
{
lean_object* v_seen_559_; lean_object* v___x_560_; 
v_seen_559_ = l_Lean_NameSet_empty;
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_seen_559_);
lean_ctor_set(v___x_560_, 1, v_seen_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object* v_calls_561_){
_start:
{
lean_object* v_seen_562_; lean_object* v___x_563_; lean_object* v_buckets_564_; size_t v_sz_565_; size_t v___x_566_; lean_object* v___x_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v_seen_562_ = lean_ctor_get(v_calls_561_, 1);
v___x_563_ = lean_obj_once(&l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0, &l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once, _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0);
v_buckets_564_ = lean_ctor_get(v_seen_562_, 1);
v_sz_565_ = lean_array_size(v_buckets_564_);
v___x_566_ = ((size_t)0ULL);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_564_, v_sz_565_, v___x_566_, v___x_563_);
v_fst_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_fst_568_);
v_snd_569_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_snd_569_);
lean_dec_ref(v___x_567_);
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed), 2, 1);
lean_closure_set(v___f_570_, 0, v_snd_569_);
v___x_571_ = l_Lean_NameSet_filter(v___f_570_, v_fst_568_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object* v_calls_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_572_);
lean_dec_ref(v_calls_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object* v_e_574_, lean_object* v_funIndInfo_575_, lean_object* v_args_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_st_ref_get(v_a_577_);
v___x_584_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_574_, v_funIndInfo_575_, v_args_576_, v___x_583_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_594_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_594_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_589_ = lean_st_ref_swap(v_a_577_, v_a_585_);
lean_dec(v___x_589_);
v___x_590_ = lean_box(0);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_584_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_584_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object* v_e_603_, lean_object* v_funIndInfo_604_, lean_object* v_args_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_603_, v_funIndInfo_604_, v_args_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_args_605_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object* v_e_613_, lean_object* v_funIndInfo_614_, lean_object* v_args_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_613_, v_funIndInfo_614_, v_args_615_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object* v_e_624_, lean_object* v_funIndInfo_625_, lean_object* v_args_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_624_, v_funIndInfo_625_, v_args_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec_ref(v_args_626_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object* v_e_635_, lean_object* v_funIndInfo_636_, lean_object* v_args_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_635_, v_funIndInfo_636_, v_args_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object* v_e_645_, lean_object* v_funIndInfo_646_, lean_object* v_args_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_645_, v_funIndInfo_646_, v_args_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_args_647_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object* v_e_655_, lean_object* v_funIndInfo_656_, lean_object* v_args_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_655_, v_funIndInfo_656_, v_args_657_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object* v_e_666_, lean_object* v_funIndInfo_667_, lean_object* v_args_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_666_, v_funIndInfo_667_, v_args_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec_ref(v_args_668_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
return v_x_677_;
}
else
{
lean_object* v_key_679_; lean_object* v_value_680_; lean_object* v_tail_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_707_; 
v_key_679_ = lean_ctor_get(v_x_678_, 0);
v_value_680_ = lean_ctor_get(v_x_678_, 1);
v_tail_681_ = lean_ctor_get(v_x_678_, 2);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_678_);
if (v_isSharedCheck_707_ == 0)
{
v___x_683_ = v_x_678_;
v_isShared_684_ = v_isSharedCheck_707_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_tail_681_);
lean_inc(v_value_680_);
lean_inc(v_key_679_);
lean_dec(v_x_678_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_707_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; size_t v___x_686_; uint64_t v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; uint64_t v___x_691_; uint64_t v_fold_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_685_ = lean_array_get_size(v_x_677_);
v___x_686_ = lean_ptr_addr(v_key_679_);
v___x_687_ = lean_usize_to_uint64(v___x_686_);
v___x_688_ = 11ULL;
v___x_689_ = lean_uint64_mix_hash(v___x_687_, v___x_688_);
v___x_690_ = 32ULL;
v___x_691_ = lean_uint64_shift_right(v___x_689_, v___x_690_);
v_fold_692_ = lean_uint64_xor(v___x_689_, v___x_691_);
v___x_693_ = 16ULL;
v___x_694_ = lean_uint64_shift_right(v_fold_692_, v___x_693_);
v___x_695_ = lean_uint64_xor(v_fold_692_, v___x_694_);
v___x_696_ = lean_uint64_to_usize(v___x_695_);
v___x_697_ = lean_usize_of_nat(v___x_685_);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_sub(v___x_697_, v___x_698_);
v___x_700_ = lean_usize_land(v___x_696_, v___x_699_);
v___x_701_ = lean_array_uget_borrowed(v_x_677_, v___x_700_);
lean_inc(v___x_701_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 2, v___x_701_);
v___x_703_ = v___x_683_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_key_679_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_value_680_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v___x_701_);
v___x_703_ = v_reuseFailAlloc_706_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = lean_array_uset(v_x_677_, v___x_700_, v___x_703_);
v_x_677_ = v___x_704_;
v_x_678_ = v_tail_681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(lean_object* v_i_708_, lean_object* v_source_709_, lean_object* v_target_710_){
_start:
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_array_get_size(v_source_709_);
v___x_712_ = lean_nat_dec_lt(v_i_708_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v_source_709_);
lean_dec(v_i_708_);
return v_target_710_;
}
else
{
lean_object* v_es_713_; lean_object* v___x_714_; lean_object* v_source_715_; lean_object* v_target_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_es_713_ = lean_array_fget(v_source_709_, v_i_708_);
v___x_714_ = lean_box(0);
v_source_715_ = lean_array_fset(v_source_709_, v_i_708_, v___x_714_);
v_target_716_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_710_, v_es_713_);
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_nat_add(v_i_708_, v___x_717_);
lean_dec(v_i_708_);
v_i_708_ = v___x_718_;
v_source_709_ = v_source_715_;
v_target_710_ = v_target_716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(lean_object* v_data_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_nbuckets_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_721_ = lean_array_get_size(v_data_720_);
v___x_722_ = lean_unsigned_to_nat(2u);
v_nbuckets_723_ = lean_nat_mul(v___x_721_, v___x_722_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_box(0);
v___x_726_ = lean_mk_array(v_nbuckets_723_, v___x_725_);
v___x_727_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_724_, v_data_720_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_a_728_, lean_object* v_x_729_){
_start:
{
if (lean_obj_tag(v_x_729_) == 0)
{
uint8_t v___x_730_; 
v___x_730_ = 0;
return v___x_730_;
}
else
{
lean_object* v_key_731_; lean_object* v_tail_732_; size_t v___x_733_; size_t v___x_734_; uint8_t v___x_735_; 
v_key_731_ = lean_ctor_get(v_x_729_, 0);
v_tail_732_ = lean_ctor_get(v_x_729_, 2);
v___x_733_ = lean_ptr_addr(v_key_731_);
v___x_734_ = lean_ptr_addr(v_a_728_);
v___x_735_ = lean_usize_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
v_x_729_ = v_tail_732_;
goto _start;
}
else
{
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_737_, v_x_738_);
lean_dec(v_x_738_);
lean_dec_ref(v_a_737_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(lean_object* v_m_741_, lean_object* v_a_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_size_744_; lean_object* v_buckets_745_; lean_object* v___x_746_; size_t v___x_747_; uint64_t v___x_748_; uint64_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v___x_752_; uint64_t v_fold_753_; uint64_t v___x_754_; uint64_t v___x_755_; uint64_t v___x_756_; size_t v___x_757_; size_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; lean_object* v_bkt_762_; uint8_t v___x_763_; 
v_size_744_ = lean_ctor_get(v_m_741_, 0);
v_buckets_745_ = lean_ctor_get(v_m_741_, 1);
v___x_746_ = lean_array_get_size(v_buckets_745_);
v___x_747_ = lean_ptr_addr(v_a_742_);
v___x_748_ = lean_usize_to_uint64(v___x_747_);
v___x_749_ = 11ULL;
v___x_750_ = lean_uint64_mix_hash(v___x_748_, v___x_749_);
v___x_751_ = 32ULL;
v___x_752_ = lean_uint64_shift_right(v___x_750_, v___x_751_);
v_fold_753_ = lean_uint64_xor(v___x_750_, v___x_752_);
v___x_754_ = 16ULL;
v___x_755_ = lean_uint64_shift_right(v_fold_753_, v___x_754_);
v___x_756_ = lean_uint64_xor(v_fold_753_, v___x_755_);
v___x_757_ = lean_uint64_to_usize(v___x_756_);
v___x_758_ = lean_usize_of_nat(v___x_746_);
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_sub(v___x_758_, v___x_759_);
v___x_761_ = lean_usize_land(v___x_757_, v___x_760_);
v_bkt_762_ = lean_array_uget_borrowed(v_buckets_745_, v___x_761_);
v___x_763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_742_, v_bkt_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_784_; 
lean_inc_ref(v_buckets_745_);
lean_inc(v_size_744_);
v_isSharedCheck_784_ = !lean_is_exclusive(v_m_741_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; 
v_unused_785_ = lean_ctor_get(v_m_741_, 1);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_m_741_, 0);
lean_dec(v_unused_786_);
v___x_765_ = v_m_741_;
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
else
{
lean_dec(v_m_741_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v_size_x27_768_; lean_object* v___x_769_; lean_object* v_buckets_x27_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v_size_x27_768_ = lean_nat_add(v_size_744_, v___x_767_);
lean_dec(v_size_744_);
lean_inc(v_bkt_762_);
v___x_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_769_, 0, v_a_742_);
lean_ctor_set(v___x_769_, 1, v_b_743_);
lean_ctor_set(v___x_769_, 2, v_bkt_762_);
v_buckets_x27_770_ = lean_array_uset(v_buckets_745_, v___x_761_, v___x_769_);
v___x_771_ = lean_unsigned_to_nat(4u);
v___x_772_ = lean_nat_mul(v_size_x27_768_, v___x_771_);
v___x_773_ = lean_unsigned_to_nat(3u);
v___x_774_ = lean_nat_div(v___x_772_, v___x_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_array_get_size(v_buckets_x27_770_);
v___x_776_ = lean_nat_dec_le(v___x_774_, v___x_775_);
lean_dec(v___x_774_);
if (v___x_776_ == 0)
{
lean_object* v_val_777_; lean_object* v___x_779_; 
v_val_777_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_770_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_val_777_);
lean_ctor_set(v___x_765_, 0, v_size_x27_768_);
v___x_779_ = v___x_765_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_size_x27_768_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_val_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v___x_782_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_buckets_x27_770_);
lean_ctor_set(v___x_765_, 0, v_size_x27_768_);
v___x_782_ = v___x_765_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_size_x27_768_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_buckets_x27_770_);
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
lean_dec(v_b_743_);
lean_dec_ref(v_a_742_);
return v_m_741_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_buckets_789_; lean_object* v___x_790_; size_t v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v_fold_797_; uint64_t v___x_798_; uint64_t v___x_799_; uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_buckets_789_ = lean_ctor_get(v_m_787_, 1);
v___x_790_ = lean_array_get_size(v_buckets_789_);
v___x_791_ = lean_ptr_addr(v_a_788_);
v___x_792_ = lean_usize_to_uint64(v___x_791_);
v___x_793_ = 11ULL;
v___x_794_ = lean_uint64_mix_hash(v___x_792_, v___x_793_);
v___x_795_ = 32ULL;
v___x_796_ = lean_uint64_shift_right(v___x_794_, v___x_795_);
v_fold_797_ = lean_uint64_xor(v___x_794_, v___x_796_);
v___x_798_ = 16ULL;
v___x_799_ = lean_uint64_shift_right(v_fold_797_, v___x_798_);
v___x_800_ = lean_uint64_xor(v_fold_797_, v___x_799_);
v___x_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = lean_usize_of_nat(v___x_790_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_sub(v___x_802_, v___x_803_);
v___x_805_ = lean_usize_land(v___x_801_, v___x_804_);
v___x_806_ = lean_array_uget_borrowed(v_buckets_789_, v___x_805_);
v___x_807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_788_, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_808_, lean_object* v_a_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_808_, v_a_809_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_m_808_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_812_; lean_object* v_dummy_813_; 
v___x_812_ = lean_box(0);
v_dummy_813_ = l_Lean_Expr_sort___override(v___x_812_);
return v_dummy_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_e_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; 
if (lean_obj_tag(v_x_815_) == 5)
{
lean_object* v_fn_847_; lean_object* v_arg_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_fn_847_ = lean_ctor_get(v_x_815_, 0);
lean_inc_ref(v_fn_847_);
v_arg_848_ = lean_ctor_get(v_x_815_, 1);
lean_inc_ref(v_arg_848_);
lean_dec_ref_known(v_x_815_, 2);
v___x_849_ = lean_array_set(v_x_816_, v_x_817_, v_arg_848_);
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_sub(v_x_817_, v___x_850_);
lean_dec(v_x_817_);
v_x_815_ = v_fn_847_;
v_x_816_ = v___x_849_;
v_x_817_ = v___x_851_;
goto _start;
}
else
{
lean_dec(v_x_817_);
if (lean_obj_tag(v_x_815_) == 4)
{
lean_object* v_declName_853_; lean_object* v_funName_854_; uint8_t v___x_855_; 
v_declName_853_ = lean_ctor_get(v_x_815_, 0);
lean_inc(v_declName_853_);
lean_dec_ref_known(v_x_815_, 2);
v_funName_854_ = lean_ctor_get(v___y_819_, 0);
v___x_855_ = lean_name_eq(v_declName_853_, v_funName_854_);
lean_dec(v_declName_853_);
if (v___x_855_ == 0)
{
lean_dec_ref(v_e_814_);
v___y_827_ = v___y_818_;
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
goto v___jp_826_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = l_Lean_Expr_hasLooseBVars(v_e_814_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_inc_ref(v___y_819_);
v___x_857_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_814_, v___y_819_, v_x_816_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_dec_ref_known(v___x_857_, 1);
v___y_827_ = v___y_818_;
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
goto v___jp_826_;
}
else
{
lean_dec_ref(v_x_816_);
return v___x_857_;
}
}
else
{
lean_dec_ref(v_e_814_);
v___y_827_ = v___y_818_;
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
goto v___jp_826_;
}
}
}
else
{
lean_object* v___x_858_; 
lean_dec_ref(v_e_814_);
v___x_858_ = l_Lean_Meta_FunInd_Collector_visit(v_x_815_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_dec_ref_known(v___x_858_, 1);
v___y_827_ = v___y_818_;
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
goto v___jp_826_;
}
else
{
lean_dec_ref(v_x_816_);
return v___x_858_;
}
}
}
v___jp_826_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_array_get_size(v_x_816_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v_x_816_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
return v___x_838_;
}
else
{
uint8_t v___x_839_; 
v___x_839_ = lean_nat_dec_le(v___x_835_, v___x_835_);
if (v___x_839_ == 0)
{
if (v___x_837_ == 0)
{
lean_object* v___x_840_; 
lean_dec_ref(v_x_816_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_836_);
return v___x_840_;
}
else
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
v___x_841_ = ((size_t)0ULL);
v___x_842_ = lean_usize_of_nat(v___x_835_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_816_, v___x_841_, v___x_842_, v___x_836_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec_ref(v_x_816_);
return v___x_843_;
}
}
else
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((size_t)0ULL);
v___x_845_ = lean_usize_of_nat(v___x_835_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_816_, v___x_844_, v___x_845_, v___x_836_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec_ref(v_x_816_);
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = lean_st_ref_get(v_a_860_);
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_868_, v_e_859_);
lean_dec(v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_d_875_; lean_object* v_b_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; 
v___x_870_ = lean_st_ref_take(v_a_860_);
v___x_871_ = lean_box(0);
lean_inc_ref(v_e_859_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_870_, v_e_859_, v___x_871_);
v___x_873_ = lean_st_ref_put(v_a_860_, v___x_872_);
switch(lean_obj_tag(v_e_859_))
{
case 4:
{
lean_object* v___x_886_; 
lean_dec_ref_known(v_e_859_, 2);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_871_);
return v___x_886_;
}
case 7:
{
lean_object* v_binderType_887_; lean_object* v_body_888_; 
v_binderType_887_ = lean_ctor_get(v_e_859_, 1);
lean_inc_ref(v_binderType_887_);
v_body_888_ = lean_ctor_get(v_e_859_, 2);
lean_inc_ref(v_body_888_);
lean_dec_ref_known(v_e_859_, 3);
v_d_875_ = v_binderType_887_;
v_b_876_ = v_body_888_;
v___y_877_ = v_a_860_;
v___y_878_ = v_a_861_;
v___y_879_ = v_a_862_;
v___y_880_ = v_a_863_;
v___y_881_ = v_a_864_;
v___y_882_ = v_a_865_;
v___y_883_ = v_a_866_;
goto v___jp_874_;
}
case 6:
{
lean_object* v_binderType_889_; lean_object* v_body_890_; 
v_binderType_889_ = lean_ctor_get(v_e_859_, 1);
lean_inc_ref(v_binderType_889_);
v_body_890_ = lean_ctor_get(v_e_859_, 2);
lean_inc_ref(v_body_890_);
lean_dec_ref_known(v_e_859_, 3);
v_d_875_ = v_binderType_889_;
v_b_876_ = v_body_890_;
v___y_877_ = v_a_860_;
v___y_878_ = v_a_861_;
v___y_879_ = v_a_862_;
v___y_880_ = v_a_863_;
v___y_881_ = v_a_864_;
v___y_882_ = v_a_865_;
v___y_883_ = v_a_866_;
goto v___jp_874_;
}
case 10:
{
lean_object* v_expr_891_; 
v_expr_891_ = lean_ctor_get(v_e_859_, 1);
lean_inc_ref(v_expr_891_);
lean_dec_ref_known(v_e_859_, 2);
v_e_859_ = v_expr_891_;
goto _start;
}
case 8:
{
lean_object* v_type_893_; lean_object* v_value_894_; lean_object* v_body_895_; lean_object* v___x_896_; 
v_type_893_ = lean_ctor_get(v_e_859_, 1);
lean_inc_ref(v_type_893_);
v_value_894_ = lean_ctor_get(v_e_859_, 2);
lean_inc_ref(v_value_894_);
v_body_895_ = lean_ctor_get(v_e_859_, 3);
lean_inc_ref(v_body_895_);
lean_dec_ref_known(v_e_859_, 4);
v___x_896_ = l_Lean_Meta_FunInd_Collector_visit(v_type_893_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v___x_897_; 
lean_dec_ref_known(v___x_896_, 1);
v___x_897_ = l_Lean_Meta_FunInd_Collector_visit(v_value_894_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref_known(v___x_897_, 1);
v_e_859_ = v_body_895_;
goto _start;
}
else
{
lean_dec_ref(v_body_895_);
return v___x_897_;
}
}
else
{
lean_dec_ref(v_body_895_);
lean_dec_ref(v_value_894_);
return v___x_896_;
}
}
case 5:
{
lean_object* v_dummy_899_; lean_object* v_nargs_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_dummy_899_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_900_ = l_Lean_Expr_getAppNumArgs(v_e_859_);
lean_inc(v_nargs_900_);
v___x_901_ = lean_mk_array(v_nargs_900_, v_dummy_899_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_sub(v_nargs_900_, v___x_902_);
lean_dec(v_nargs_900_);
lean_inc_ref(v_e_859_);
v___x_904_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_859_, v_e_859_, v___x_901_, v___x_903_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_904_;
}
case 11:
{
lean_object* v_struct_905_; 
v_struct_905_ = lean_ctor_get(v_e_859_, 2);
lean_inc_ref(v_struct_905_);
lean_dec_ref_known(v_e_859_, 3);
v_e_859_ = v_struct_905_;
goto _start;
}
default: 
{
lean_object* v___x_907_; 
lean_dec_ref(v_e_859_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_871_);
return v___x_907_;
}
}
v___jp_874_:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_FunInd_Collector_visit(v_d_875_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_dec_ref_known(v___x_884_, 1);
v_e_859_ = v_b_876_;
v_a_860_ = v___y_877_;
v_a_861_ = v___y_878_;
v_a_862_ = v___y_879_;
v_a_863_ = v___y_880_;
v_a_864_ = v___y_881_;
v_a_865_ = v___y_882_;
v_a_866_ = v___y_883_;
goto _start;
}
else
{
lean_dec_ref(v_b_876_);
return v___x_884_;
}
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref(v_e_859_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_910_, size_t v_i_911_, size_t v_stop_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_eq(v_i_911_, v_stop_912_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_array_uget_borrowed(v_as_910_, v_i_911_);
lean_inc(v___x_923_);
v___x_924_ = l_Lean_Meta_FunInd_Collector_visit(v___x_923_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; size_t v___x_926_; size_t v___x_927_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_911_, v___x_926_);
v_i_911_ = v___x_927_;
v_b_913_ = v_a_925_;
goto _start;
}
else
{
return v___x_924_;
}
}
else
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v_b_913_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_930_, lean_object* v_i_931_, lean_object* v_stop_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
size_t v_i_boxed_942_; size_t v_stop_boxed_943_; lean_object* v_res_944_; 
v_i_boxed_942_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_stop_boxed_943_ = lean_unbox_usize(v_stop_932_);
lean_dec(v_stop_932_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_930_, v_i_boxed_942_, v_stop_boxed_943_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v_as_930_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Meta_FunInd_Collector_visit(v_e_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_e_955_, lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_955_, v_x_956_, v_x_957_, v_x_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
return v_res_967_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_968_, lean_object* v_m_969_, lean_object* v_a_970_){
_start:
{
uint8_t v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_969_, v_a_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
uint8_t v_res_975_; lean_object* v_r_976_; 
v_res_975_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_972_, v_m_973_, v_a_974_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_m_973_);
v_r_976_ = lean_box(v_res_975_);
return v_r_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_00_u03b2_977_, lean_object* v_m_978_, lean_object* v_a_979_, lean_object* v_b_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_978_, v_a_979_, v_b_980_);
return v___x_981_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_982_, lean_object* v_a_983_, lean_object* v_x_984_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_983_, v_x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_986_, lean_object* v_a_987_, lean_object* v_x_988_){
_start:
{
uint8_t v_res_989_; lean_object* v_r_990_; 
v_res_989_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_986_, v_a_987_, v_x_988_);
lean_dec(v_x_988_);
lean_dec_ref(v_a_987_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object* v_00_u03b2_991_, lean_object* v_data_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_994_, lean_object* v_i_995_, lean_object* v_source_996_, lean_object* v_target_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_995_, v_source_996_, v_target_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = l_Lean_Expr_hasMVar(v_e_1003_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_e_1003_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v_mctx_1009_; lean_object* v___x_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1013_; lean_object* v_cache_1014_; lean_object* v_zetaDeltaFVarIds_1015_; lean_object* v_postponed_1016_; lean_object* v_diag_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1026_; 
v___x_1008_ = lean_st_ref_get(v___y_1004_);
v_mctx_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_mctx_1009_);
lean_dec(v___x_1008_);
v___x_1010_ = l_Lean_instantiateMVarsCore(v_mctx_1009_, v_e_1003_);
v_fst_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_fst_1011_);
v_snd_1012_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_snd_1012_);
lean_dec_ref(v___x_1010_);
v___x_1013_ = lean_st_ref_take(v___y_1004_);
v_cache_1014_ = lean_ctor_get(v___x_1013_, 1);
v_zetaDeltaFVarIds_1015_ = lean_ctor_get(v___x_1013_, 2);
v_postponed_1016_ = lean_ctor_get(v___x_1013_, 3);
v_diag_1017_ = lean_ctor_get(v___x_1013_, 4);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v___x_1013_, 0);
lean_dec(v_unused_1027_);
v___x_1019_ = v___x_1013_;
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_diag_1017_);
lean_inc(v_postponed_1016_);
lean_inc(v_zetaDeltaFVarIds_1015_);
lean_inc(v_cache_1014_);
lean_dec(v___x_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v_snd_1012_);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_snd_1012_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_cache_1014_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_zetaDeltaFVarIds_1015_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_postponed_1016_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_diag_1017_);
v___x_1022_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_st_ref_put(v___y_1004_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_fst_1011_);
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1028_, v___y_1029_);
lean_dec(v___y_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1032_, v___y_1037_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1052_, size_t v_sz_1053_, size_t v_i_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1054_, v_sz_1053_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1055_);
return v___x_1065_;
}
else
{
lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1124_; 
v_snd_1066_ = lean_ctor_get(v_b_1055_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_b_1055_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_b_1055_, 0);
lean_dec(v_unused_1125_);
v___x_1068_ = v_b_1055_;
v_isShared_1069_ = v_isSharedCheck_1124_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_dec(v_b_1055_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1124_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v_a_1072_; lean_object* v_a_1079_; 
v___x_1070_ = lean_box(0);
v_a_1079_ = lean_array_uget_borrowed(v_as_1052_, v_i_1054_);
if (lean_obj_tag(v_a_1079_) == 0)
{
v_a_1072_ = v_snd_1066_;
goto v___jp_1071_;
}
else
{
lean_object* v_val_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
lean_dec(v_snd_1066_);
v_val_1080_ = lean_ctor_get(v_a_1079_, 0);
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Lean_LocalDecl_isAuxDecl(v_val_1080_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_LocalDecl_value_x3f(v_val_1080_, v___x_1082_);
if (lean_obj_tag(v___x_1083_) == 1)
{
lean_object* v_val_1084_; lean_object* v___x_1085_; 
v_val_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1084_, v___y_1060_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1086_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_dec_ref_known(v___x_1087_, 1);
v_a_1072_ = v___x_1081_;
goto v___jp_1071_;
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_del_object(v___x_1068_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_del_object(v___x_1068_);
v_a_1096_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1085_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1085_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v___x_1083_);
v___x_1104_ = l_Lean_LocalDecl_type(v_val_1080_);
v___x_1105_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1104_, v___y_1060_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1106_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref_known(v___x_1107_, 1);
v_a_1072_ = v___x_1081_;
goto v___jp_1071_;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_del_object(v___x_1068_);
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_del_object(v___x_1068_);
v_a_1116_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1105_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1105_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
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
v_a_1072_ = v___x_1081_;
goto v___jp_1071_;
}
}
v___jp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v_a_1072_);
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_a_1072_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
size_t v___x_1075_; size_t v___x_1076_; 
v___x_1075_ = ((size_t)1ULL);
v___x_1076_ = lean_usize_add(v_i_1054_, v___x_1075_);
v_i_1054_ = v___x_1076_;
v_b_1055_ = v___x_1074_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1126_, lean_object* v_sz_1127_, lean_object* v_i_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
size_t v_sz_boxed_1138_; size_t v_i_boxed_1139_; lean_object* v_res_1140_; 
v_sz_boxed_1138_ = lean_unbox_usize(v_sz_1127_);
lean_dec(v_sz_1127_);
v_i_boxed_1139_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1126_, v_sz_boxed_1138_, v_i_boxed_1139_, v_b_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v_as_1126_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1141_, size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_b_1144_);
return v___x_1154_;
}
else
{
lean_object* v_snd_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1213_; 
v_snd_1155_ = lean_ctor_get(v_b_1144_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_b_1144_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_b_1144_, 0);
lean_dec(v_unused_1214_);
v___x_1157_ = v_b_1144_;
v_isShared_1158_ = v_isSharedCheck_1213_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snd_1155_);
lean_dec(v_b_1144_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1213_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v_a_1161_; lean_object* v_a_1168_; 
v___x_1159_ = lean_box(0);
v_a_1168_ = lean_array_uget_borrowed(v_as_1141_, v_i_1143_);
if (lean_obj_tag(v_a_1168_) == 0)
{
v_a_1161_ = v_snd_1155_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
lean_dec(v_snd_1155_);
v_val_1169_ = lean_ctor_get(v_a_1168_, 0);
v___x_1170_ = lean_box(0);
v___x_1171_ = l_Lean_LocalDecl_isAuxDecl(v_val_1169_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_LocalDecl_value_x3f(v_val_1169_, v___x_1171_);
if (lean_obj_tag(v___x_1172_) == 1)
{
lean_object* v_val_1173_; lean_object* v___x_1174_; 
v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1173_, v___y_1149_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1175_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_dec_ref_known(v___x_1176_, 1);
v_a_1161_ = v___x_1170_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_del_object(v___x_1157_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_del_object(v___x_1157_);
v_a_1185_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1174_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1174_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v___x_1172_);
v___x_1193_ = l_Lean_LocalDecl_type(v_val_1169_);
v___x_1194_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1193_, v___y_1149_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1195_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_dec_ref_known(v___x_1196_, 1);
v_a_1161_ = v___x_1170_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_del_object(v___x_1157_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_del_object(v___x_1157_);
v_a_1205_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1194_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1194_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
else
{
v_a_1161_ = v___x_1170_;
goto v___jp_1160_;
}
}
v___jp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_a_1161_);
lean_ctor_set(v___x_1157_, 0, v___x_1159_);
v___x_1163_ = v___x_1157_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_a_1161_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1143_, v___x_1164_);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1141_, v_sz_1142_, v___x_1165_, v___x_1163_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1215_, lean_object* v_sz_1216_, lean_object* v_i_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
size_t v_sz_boxed_1227_; size_t v_i_boxed_1228_; lean_object* v_res_1229_; 
v_sz_boxed_1227_ = lean_unbox_usize(v_sz_1216_);
lean_dec(v_sz_1216_);
v_i_boxed_1228_ = lean_unbox_usize(v_i_1217_);
lean_dec(v_i_1217_);
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1215_, v_sz_boxed_1227_, v_i_boxed_1228_, v_b_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v_as_1215_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1230_, size_t v_sz_1231_, size_t v_i_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_usize_dec_lt(v_i_1232_, v_sz_1231_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_b_1233_);
return v___x_1243_;
}
else
{
lean_object* v_snd_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1302_; 
v_snd_1244_ = lean_ctor_get(v_b_1233_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_b_1233_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_b_1233_, 0);
lean_dec(v_unused_1303_);
v___x_1246_ = v_b_1233_;
v_isShared_1247_ = v_isSharedCheck_1302_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_snd_1244_);
lean_dec(v_b_1233_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1302_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v_a_1250_; lean_object* v_a_1257_; 
v___x_1248_ = lean_box(0);
v_a_1257_ = lean_array_uget_borrowed(v_as_1230_, v_i_1232_);
if (lean_obj_tag(v_a_1257_) == 0)
{
v_a_1250_ = v_snd_1244_;
goto v___jp_1249_;
}
else
{
lean_object* v_val_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
lean_dec(v_snd_1244_);
v_val_1258_ = lean_ctor_get(v_a_1257_, 0);
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Lean_LocalDecl_isAuxDecl(v_val_1258_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_LocalDecl_value_x3f(v_val_1258_, v___x_1260_);
if (lean_obj_tag(v___x_1261_) == 1)
{
lean_object* v_val_1262_; lean_object* v___x_1263_; 
v_val_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1262_, v___y_1238_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1264_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_dec_ref_known(v___x_1265_, 1);
v_a_1250_ = v___x_1259_;
goto v___jp_1249_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_del_object(v___x_1246_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_del_object(v___x_1246_);
v_a_1274_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1263_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1263_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec(v___x_1261_);
v___x_1282_ = l_Lean_LocalDecl_type(v_val_1258_);
v___x_1283_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1282_, v___y_1238_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1284_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec_ref_known(v___x_1285_, 1);
v_a_1250_ = v___x_1259_;
goto v___jp_1249_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_del_object(v___x_1246_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_del_object(v___x_1246_);
v_a_1294_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1283_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1283_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
else
{
v_a_1250_ = v___x_1259_;
goto v___jp_1249_;
}
}
v___jp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_a_1250_);
lean_ctor_set(v___x_1246_, 0, v___x_1248_);
v___x_1252_ = v___x_1246_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_a_1250_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
size_t v___x_1253_; size_t v___x_1254_; 
v___x_1253_ = ((size_t)1ULL);
v___x_1254_ = lean_usize_add(v_i_1232_, v___x_1253_);
v_i_1232_ = v___x_1254_;
v_b_1233_ = v___x_1252_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1304_, lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
size_t v_sz_boxed_1316_; size_t v_i_boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1317_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1304_, v_sz_boxed_1316_, v_i_boxed_1317_, v_b_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v_as_1304_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1319_, size_t v_sz_1320_, size_t v_i_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_usize_dec_lt(v_i_1321_, v_sz_1320_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_b_1322_);
return v___x_1332_;
}
else
{
lean_object* v_snd_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1391_; 
v_snd_1333_ = lean_ctor_get(v_b_1322_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_b_1322_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v_b_1322_, 0);
lean_dec(v_unused_1392_);
v___x_1335_ = v_b_1322_;
v_isShared_1336_ = v_isSharedCheck_1391_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_snd_1333_);
lean_dec(v_b_1322_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1391_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v_a_1339_; lean_object* v_a_1346_; 
v___x_1337_ = lean_box(0);
v_a_1346_ = lean_array_uget_borrowed(v_as_1319_, v_i_1321_);
if (lean_obj_tag(v_a_1346_) == 0)
{
v_a_1339_ = v_snd_1333_;
goto v___jp_1338_;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
lean_dec(v_snd_1333_);
v_val_1347_ = lean_ctor_get(v_a_1346_, 0);
v___x_1348_ = lean_box(0);
v___x_1349_ = l_Lean_LocalDecl_isAuxDecl(v_val_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_LocalDecl_value_x3f(v_val_1347_, v___x_1349_);
if (lean_obj_tag(v___x_1350_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1352_; 
v_val_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1351_, v___y_1327_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1353_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_dec_ref_known(v___x_1354_, 1);
v_a_1339_ = v___x_1348_;
goto v___jp_1338_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_del_object(v___x_1335_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_del_object(v___x_1335_);
v_a_1363_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1352_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1352_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v___x_1350_);
v___x_1371_ = l_Lean_LocalDecl_type(v_val_1347_);
v___x_1372_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1371_, v___y_1327_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1373_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_dec_ref_known(v___x_1374_, 1);
v_a_1339_ = v___x_1348_;
goto v___jp_1338_;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_del_object(v___x_1335_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_del_object(v___x_1335_);
v_a_1383_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1372_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1372_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
else
{
v_a_1339_ = v___x_1348_;
goto v___jp_1338_;
}
}
v___jp_1338_:
{
lean_object* v___x_1341_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v_a_1339_);
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1341_ = v___x_1335_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_a_1339_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1321_, v___x_1342_);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1319_, v_sz_1320_, v___x_1343_, v___x_1341_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
size_t v_sz_boxed_1405_; size_t v_i_boxed_1406_; lean_object* v_res_1407_; 
v_sz_boxed_1405_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1406_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1393_, v_sz_boxed_1405_, v_i_boxed_1406_, v_b_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v_as_1393_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_init_1408_, lean_object* v_n_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
if (lean_obj_tag(v_n_1409_) == 0)
{
lean_object* v_cs_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; size_t v_sz_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v_cs_1419_ = lean_ctor_get(v_n_1409_, 0);
v___x_1420_ = lean_box(0);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v_b_1410_);
v_sz_1422_ = lean_array_size(v_cs_1419_);
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1408_, v_cs_1419_, v_sz_1422_, v___x_1423_, v___x_1421_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1439_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1439_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1439_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; 
v_fst_1429_ = lean_ctor_get(v_a_1425_, 0);
if (lean_obj_tag(v_fst_1429_) == 0)
{
lean_object* v_snd_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v_snd_1430_ = lean_ctor_get(v_a_1425_, 1);
lean_inc(v_snd_1430_);
lean_dec(v_a_1425_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_snd_1430_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1431_);
v___x_1433_ = v___x_1427_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1437_; 
lean_inc_ref(v_fst_1429_);
lean_dec(v_a_1425_);
v_val_1435_ = lean_ctor_get(v_fst_1429_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v_fst_1429_, 1);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v_val_1435_);
v___x_1437_ = v___x_1427_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_val_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_a_1440_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1424_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1424_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_vs_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; size_t v_sz_1451_; size_t v___x_1452_; lean_object* v___x_1453_; 
v_vs_1448_ = lean_ctor_get(v_n_1409_, 0);
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_b_1410_);
v_sz_1451_ = lean_array_size(v_vs_1448_);
v___x_1452_ = ((size_t)0ULL);
v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1448_, v_sz_1451_, v___x_1452_, v___x_1450_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1468_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1468_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1468_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v_fst_1458_; 
v_fst_1458_ = lean_ctor_get(v_a_1454_, 0);
if (lean_obj_tag(v_fst_1458_) == 0)
{
lean_object* v_snd_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v_snd_1459_ = lean_ctor_get(v_a_1454_, 1);
lean_inc(v_snd_1459_);
lean_dec(v_a_1454_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_snd_1459_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1460_);
v___x_1462_ = v___x_1456_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v_val_1464_; lean_object* v___x_1466_; 
lean_inc_ref(v_fst_1458_);
lean_dec(v_a_1454_);
v_val_1464_ = lean_ctor_get(v_fst_1458_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v_fst_1458_, 1);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v_val_1464_);
v___x_1466_ = v___x_1456_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_val_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1453_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1453_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_init_1477_, lean_object* v_as_1478_, size_t v_sz_1479_, size_t v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1480_, v_sz_1479_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1481_);
return v___x_1491_;
}
else
{
lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1526_; 
v_snd_1492_ = lean_ctor_get(v_b_1481_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_b_1481_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_b_1481_, 0);
lean_dec(v_unused_1527_);
v___x_1494_ = v_b_1481_;
v_isShared_1495_ = v_isSharedCheck_1526_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_dec(v_b_1481_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1526_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_array_uget_borrowed(v_as_1478_, v_i_1480_);
lean_inc(v_snd_1492_);
v___x_1497_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1477_, v_a_1496_, v_snd_1492_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1517_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
if (lean_obj_tag(v_a_1498_) == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_a_1498_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1502_);
v___x_1504_ = v___x_1494_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1492_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1504_);
v___x_1506_ = v___x_1500_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_del_object(v___x_1500_);
lean_dec(v_snd_1492_);
v_a_1509_ = lean_ctor_get(v_a_1498_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_a_1498_, 1);
v___x_1510_ = lean_box(0);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v_a_1509_);
lean_ctor_set(v___x_1494_, 0, v___x_1510_);
v___x_1512_ = v___x_1494_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1509_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
size_t v___x_1513_; size_t v___x_1514_; 
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1480_, v___x_1513_);
v_i_1480_ = v___x_1514_;
v_b_1481_ = v___x_1512_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
v_a_1518_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1497_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1497_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1528_, lean_object* v_as_1529_, lean_object* v_sz_1530_, lean_object* v_i_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
size_t v_sz_boxed_1541_; size_t v_i_boxed_1542_; lean_object* v_res_1543_; 
v_sz_boxed_1541_ = lean_unbox_usize(v_sz_1530_);
lean_dec(v_sz_1530_);
v_i_boxed_1542_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_res_1543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1528_, v_as_1529_, v_sz_boxed_1541_, v_i_boxed_1542_, v_b_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v_as_1529_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_init_1544_, lean_object* v_n_1545_, lean_object* v_b_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1544_, v_n_1545_, v_b_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v_n_1545_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1556_, lean_object* v_init_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_root_1566_; lean_object* v_tail_1567_; lean_object* v___x_1568_; 
v_root_1566_ = lean_ctor_get(v_t_1556_, 0);
v_tail_1567_ = lean_ctor_get(v_t_1556_, 1);
v___x_1568_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1557_, v_root_1566_, v_init_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1605_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1605_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1605_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
if (lean_obj_tag(v_a_1569_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; 
v_a_1573_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v_a_1569_, 1);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v_a_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; size_t v_sz_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
lean_del_object(v___x_1571_);
v_a_1577_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v_a_1569_, 1);
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_a_1577_);
v_sz_1580_ = lean_array_size(v_tail_1567_);
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1567_, v_sz_1580_, v___x_1581_, v___x_1579_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1596_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1596_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1596_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_fst_1587_; 
v_fst_1587_ = lean_ctor_get(v_a_1583_, 0);
if (lean_obj_tag(v_fst_1587_) == 0)
{
lean_object* v_snd_1588_; lean_object* v___x_1590_; 
v_snd_1588_ = lean_ctor_get(v_a_1583_, 1);
lean_inc(v_snd_1588_);
lean_dec(v_a_1583_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v_snd_1588_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_snd_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
else
{
lean_object* v_val_1592_; lean_object* v___x_1594_; 
lean_inc_ref(v_fst_1587_);
lean_dec(v_a_1583_);
v_val_1592_ = lean_ctor_get(v_fst_1587_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_fst_1587_, 1);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v_val_1592_);
v___x_1594_ = v___x_1585_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_val_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_a_1597_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1582_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1582_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_a_1606_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1568_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1568_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1614_, lean_object* v_init_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1614_, v_init_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v_t_1614_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_lctx_1634_; lean_object* v_decls_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_lctx_1634_ = lean_ctor_get(v_a_1629_, 2);
v_decls_1635_ = lean_ctor_get(v_lctx_1634_, 1);
v___x_1636_ = lean_box(0);
v___x_1637_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1635_, v___x_1636_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1637_, 1);
v___x_1638_ = l_Lean_MVarId_getType(v_mvarId_1625_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1639_, v_a_1630_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1641_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
return v___x_1642_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1640_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1640_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1638_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1638_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_dec(v_mvarId_1625_);
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1669_, lean_object* v_x_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1669_, v_x_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1685_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1676_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1676_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1693_, lean_object* v_x_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1693_, v_x_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1701_, lean_object* v_mvarId_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1702_, v_x_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1710_, lean_object* v_mvarId_1711_, lean_object* v_x_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1710_, v_mvarId_1711_, v_x_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1719_, lean_object* v___x_1720_, lean_object* v_mvarId_1721_, lean_object* v_needle_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_st_mk_ref(v___x_1719_);
v___x_1729_ = lean_st_mk_ref(v___x_1720_);
v___x_1730_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1721_, v___x_1729_, v_needle_1722_, v___x_1728_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1740_; 
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1740_ == 0)
{
lean_object* v_unused_1741_; 
v_unused_1741_ = lean_ctor_get(v___x_1730_, 0);
lean_dec(v_unused_1741_);
v___x_1732_ = v___x_1730_;
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
else
{
lean_dec(v___x_1730_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_calls_1736_; lean_object* v___x_1738_; 
v___x_1734_ = lean_st_ref_get(v___x_1729_);
lean_dec(v___x_1729_);
lean_dec(v___x_1734_);
v___x_1735_ = lean_st_ref_get(v___x_1728_);
lean_dec(v___x_1728_);
v_calls_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc_ref(v_calls_1736_);
lean_dec(v___x_1735_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v_calls_1736_);
v___x_1738_ = v___x_1732_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_calls_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v___x_1729_);
lean_dec(v___x_1728_);
v_a_1742_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1730_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1730_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v_mvarId_1752_, lean_object* v_needle_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1750_, v___x_1751_, v_mvarId_1752_, v_needle_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v_needle_1753_);
return v_res_1759_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(64u);
v___x_1761_ = l_Lean_mkPtrSet___redArg(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1762_, lean_object* v_mvarId_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_1770_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
lean_inc(v_mvarId_1763_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1771_, 0, v___x_1770_);
lean_closure_set(v___f_1771_, 1, v___x_1769_);
lean_closure_set(v___f_1771_, 2, v_mvarId_1763_);
lean_closure_set(v___f_1771_, 3, v_needle_1762_);
v___x_1772_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1763_, v___f_1771_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_1773_, lean_object* v_mvarId_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1773_, v_mvarId_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_1781_, lean_object* v_mvarId_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1781_, v_mvarId_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_1789_, lean_object* v_mvarId_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1789_, v_mvarId_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_1797_, lean_object* v_mvarId_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1797_, v_mvarId_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_1805_, lean_object* v_mvarId_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Meta_FunInd_collect(v_needle_1805_, v_mvarId_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1812_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_FunIndCollect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls = _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls();
lean_mark_persistent(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_FunIndCollect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FunIndCollect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
}
#ifdef __cplusplus
}
#endif
