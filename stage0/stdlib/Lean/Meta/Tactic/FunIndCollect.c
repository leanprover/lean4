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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_key_67_; lean_object* v_tail_68_; lean_object* v_fst_69_; lean_object* v_snd_70_; lean_object* v_fst_71_; lean_object* v_snd_72_; uint8_t v___x_73_; 
v_key_67_ = lean_ctor_get(v_x_65_, 0);
v_tail_68_ = lean_ctor_get(v_x_65_, 2);
v_fst_69_ = lean_ctor_get(v_key_67_, 0);
v_snd_70_ = lean_ctor_get(v_key_67_, 1);
v_fst_71_ = lean_ctor_get(v_a_64_, 0);
v_snd_72_ = lean_ctor_get(v_a_64_, 1);
v___x_73_ = lean_name_eq(v_fst_69_, v_fst_71_);
if (v___x_73_ == 0)
{
v_x_65_ = v_tail_68_;
goto _start;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_array_get_size(v_snd_70_);
v___x_76_ = lean_array_get_size(v_snd_72_);
v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
v_x_65_ = v_tail_68_;
goto _start;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_snd_70_, v_snd_72_, v___x_75_);
if (v___x_79_ == 0)
{
v_x_65_ = v_tail_68_;
goto _start;
}
else
{
return v___x_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg___boxed(lean_object* v_a_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec_ref(v_a_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(lean_object* v_as_85_, size_t v_i_86_, size_t v_stop_87_, uint64_t v_b_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_usize_dec_eq(v_i_86_, v_stop_87_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; size_t v___x_93_; size_t v___x_94_; 
v___x_90_ = lean_array_uget_borrowed(v_as_85_, v_i_86_);
v___x_91_ = l_Lean_Expr_hash(v___x_90_);
v___x_92_ = lean_uint64_mix_hash(v_b_88_, v___x_91_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_add(v_i_86_, v___x_93_);
v_i_86_ = v___x_94_;
v_b_88_ = v___x_92_;
goto _start;
}
else
{
return v_b_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2___boxed(lean_object* v_as_96_, lean_object* v_i_97_, lean_object* v_stop_98_, lean_object* v_b_99_){
_start:
{
size_t v_i_boxed_100_; size_t v_stop_boxed_101_; uint64_t v_b_boxed_102_; uint64_t v_res_103_; lean_object* v_r_104_; 
v_i_boxed_100_ = lean_unbox_usize(v_i_97_);
lean_dec(v_i_97_);
v_stop_boxed_101_ = lean_unbox_usize(v_stop_98_);
lean_dec(v_stop_98_);
v_b_boxed_102_ = lean_unbox_uint64(v_b_99_);
lean_dec_ref(v_b_99_);
v_res_103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_as_96_, v_i_boxed_100_, v_stop_boxed_101_, v_b_boxed_102_);
lean_dec_ref(v_as_96_);
v_r_104_ = lean_box_uint64(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
return v_x_105_;
}
else
{
lean_object* v_key_107_; lean_object* v_value_108_; lean_object* v_tail_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_148_; 
v_key_107_ = lean_ctor_get(v_x_106_, 0);
v_value_108_ = lean_ctor_get(v_x_106_, 1);
v_tail_109_ = lean_ctor_get(v_x_106_, 2);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_148_ == 0)
{
v___x_111_ = v_x_106_;
v_isShared_112_ = v_isSharedCheck_148_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_tail_109_);
lean_inc(v_value_108_);
lean_inc(v_key_107_);
lean_dec(v_x_106_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_148_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_115_; uint64_t v___y_117_; uint64_t v___y_118_; uint64_t v___y_138_; 
v_fst_113_ = lean_ctor_get(v_key_107_, 0);
v_snd_114_ = lean_ctor_get(v_key_107_, 1);
v___x_115_ = lean_array_get_size(v_x_105_);
if (lean_obj_tag(v_fst_113_) == 0)
{
uint64_t v___x_146_; 
v___x_146_ = 1723ULL;
v___y_138_ = v___x_146_;
goto v___jp_137_;
}
else
{
uint64_t v_hash_147_; 
v_hash_147_ = lean_ctor_get_uint64(v_fst_113_, sizeof(void*)*2);
v___y_138_ = v_hash_147_;
goto v___jp_137_;
}
v___jp_116_:
{
uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_119_ = lean_uint64_mix_hash(v___y_117_, v___y_118_);
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
v___x_131_ = lean_array_uget_borrowed(v_x_105_, v___x_130_);
lean_inc(v___x_131_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 2, v___x_131_);
v___x_133_ = v___x_111_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_key_107_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_value_108_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v___x_131_);
v___x_133_ = v_reuseFailAlloc_136_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
v___x_134_ = lean_array_uset(v_x_105_, v___x_130_, v___x_133_);
v_x_105_ = v___x_134_;
v_x_106_ = v_tail_109_;
goto _start;
}
}
v___jp_137_:
{
uint64_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_139_ = 7ULL;
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_array_get_size(v_snd_114_);
v___x_142_ = lean_nat_dec_lt(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
v___y_117_ = v___y_138_;
v___y_118_ = v___x_139_;
goto v___jp_116_;
}
else
{
size_t v___x_143_; size_t v___x_144_; uint64_t v___x_145_; 
v___x_143_ = ((size_t)0ULL);
v___x_144_ = lean_usize_of_nat(v___x_141_);
v___x_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_114_, v___x_143_, v___x_144_, v___x_139_);
v___y_117_ = v___y_138_;
v___y_118_ = v___x_145_;
goto v___jp_116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(lean_object* v_i_149_, lean_object* v_source_150_, lean_object* v_target_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_array_get_size(v_source_150_);
v___x_153_ = lean_nat_dec_lt(v_i_149_, v___x_152_);
if (v___x_153_ == 0)
{
lean_dec_ref(v_source_150_);
lean_dec(v_i_149_);
return v_target_151_;
}
else
{
lean_object* v_es_154_; lean_object* v___x_155_; lean_object* v_source_156_; lean_object* v_target_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_es_154_ = lean_array_fget(v_source_150_, v_i_149_);
v___x_155_ = lean_box(0);
v_source_156_ = lean_array_fset(v_source_150_, v_i_149_, v___x_155_);
v_target_157_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_target_151_, v_es_154_);
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = lean_nat_add(v_i_149_, v___x_158_);
lean_dec(v_i_149_);
v_i_149_ = v___x_159_;
v_source_150_ = v_source_156_;
v_target_151_ = v_target_157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(lean_object* v_data_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_nbuckets_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_162_ = lean_array_get_size(v_data_161_);
v___x_163_ = lean_unsigned_to_nat(2u);
v_nbuckets_164_ = lean_nat_mul(v___x_162_, v___x_163_);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_box(0);
v___x_167_ = lean_mk_array(v_nbuckets_164_, v___x_166_);
v___x_168_ = lean_array_propagate_mark(v_data_161_, v___x_167_);
v___x_169_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_165_, v_data_161_, v___x_168_);
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
v___x_589_ = lean_box(0);
v___x_590_ = lean_st_ref_swap(v_a_577_, v_a_585_);
lean_dec(v___x_590_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_589_);
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
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_nbuckets_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_721_ = lean_array_get_size(v_data_720_);
v___x_722_ = lean_unsigned_to_nat(2u);
v_nbuckets_723_ = lean_nat_mul(v___x_721_, v___x_722_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_box(0);
v___x_726_ = lean_mk_array(v_nbuckets_723_, v___x_725_);
v___x_727_ = lean_array_propagate_mark(v_data_720_, v___x_726_);
v___x_728_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_724_, v_data_720_, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_a_729_, lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 0)
{
uint8_t v___x_731_; 
v___x_731_ = 0;
return v___x_731_;
}
else
{
lean_object* v_key_732_; lean_object* v_tail_733_; size_t v___x_734_; size_t v___x_735_; uint8_t v___x_736_; 
v_key_732_ = lean_ctor_get(v_x_730_, 0);
v_tail_733_ = lean_ctor_get(v_x_730_, 2);
v___x_734_ = lean_ptr_addr(v_key_732_);
v___x_735_ = lean_ptr_addr(v_a_729_);
v___x_736_ = lean_usize_dec_eq(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
v_x_730_ = v_tail_733_;
goto _start;
}
else
{
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_738_, lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_738_, v_x_739_);
lean_dec(v_x_739_);
lean_dec_ref(v_a_738_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(lean_object* v_m_742_, lean_object* v_a_743_, lean_object* v_b_744_){
_start:
{
lean_object* v_size_745_; lean_object* v_buckets_746_; lean_object* v___x_747_; size_t v___x_748_; uint64_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; uint64_t v_fold_754_; uint64_t v___x_755_; uint64_t v___x_756_; uint64_t v___x_757_; size_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; lean_object* v_bkt_763_; uint8_t v___x_764_; 
v_size_745_ = lean_ctor_get(v_m_742_, 0);
v_buckets_746_ = lean_ctor_get(v_m_742_, 1);
v___x_747_ = lean_array_get_size(v_buckets_746_);
v___x_748_ = lean_ptr_addr(v_a_743_);
v___x_749_ = lean_usize_to_uint64(v___x_748_);
v___x_750_ = 11ULL;
v___x_751_ = lean_uint64_mix_hash(v___x_749_, v___x_750_);
v___x_752_ = 32ULL;
v___x_753_ = lean_uint64_shift_right(v___x_751_, v___x_752_);
v_fold_754_ = lean_uint64_xor(v___x_751_, v___x_753_);
v___x_755_ = 16ULL;
v___x_756_ = lean_uint64_shift_right(v_fold_754_, v___x_755_);
v___x_757_ = lean_uint64_xor(v_fold_754_, v___x_756_);
v___x_758_ = lean_uint64_to_usize(v___x_757_);
v___x_759_ = lean_usize_of_nat(v___x_747_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_sub(v___x_759_, v___x_760_);
v___x_762_ = lean_usize_land(v___x_758_, v___x_761_);
v_bkt_763_ = lean_array_uget_borrowed(v_buckets_746_, v___x_762_);
v___x_764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_743_, v_bkt_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_785_; 
lean_inc_ref(v_buckets_746_);
lean_inc(v_size_745_);
v_isSharedCheck_785_ = !lean_is_exclusive(v_m_742_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; lean_object* v_unused_787_; 
v_unused_786_ = lean_ctor_get(v_m_742_, 1);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_m_742_, 0);
lean_dec(v_unused_787_);
v___x_766_ = v_m_742_;
v_isShared_767_ = v_isSharedCheck_785_;
goto v_resetjp_765_;
}
else
{
lean_dec(v_m_742_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_785_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v_size_x27_769_; lean_object* v___x_770_; lean_object* v_buckets_x27_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_768_ = lean_unsigned_to_nat(1u);
v_size_x27_769_ = lean_nat_add(v_size_745_, v___x_768_);
lean_dec(v_size_745_);
lean_inc(v_bkt_763_);
v___x_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_770_, 0, v_a_743_);
lean_ctor_set(v___x_770_, 1, v_b_744_);
lean_ctor_set(v___x_770_, 2, v_bkt_763_);
v_buckets_x27_771_ = lean_array_uset(v_buckets_746_, v___x_762_, v___x_770_);
v___x_772_ = lean_unsigned_to_nat(4u);
v___x_773_ = lean_nat_mul(v_size_x27_769_, v___x_772_);
v___x_774_ = lean_unsigned_to_nat(3u);
v___x_775_ = lean_nat_div(v___x_773_, v___x_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_array_get_size(v_buckets_x27_771_);
v___x_777_ = lean_nat_dec_le(v___x_775_, v___x_776_);
lean_dec(v___x_775_);
if (v___x_777_ == 0)
{
lean_object* v_val_778_; lean_object* v___x_780_; 
v_val_778_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_771_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_val_778_);
lean_ctor_set(v___x_766_, 0, v_size_x27_769_);
v___x_780_ = v___x_766_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_size_x27_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_val_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v___x_783_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_buckets_x27_771_);
lean_ctor_set(v___x_766_, 0, v_size_x27_769_);
v___x_783_ = v___x_766_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_size_x27_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_buckets_x27_771_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_dec(v_b_744_);
lean_dec_ref(v_a_743_);
return v_m_742_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_buckets_790_; lean_object* v___x_791_; size_t v___x_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v___x_797_; uint64_t v_fold_798_; uint64_t v___x_799_; uint64_t v___x_800_; uint64_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_buckets_790_ = lean_ctor_get(v_m_788_, 1);
v___x_791_ = lean_array_get_size(v_buckets_790_);
v___x_792_ = lean_ptr_addr(v_a_789_);
v___x_793_ = lean_usize_to_uint64(v___x_792_);
v___x_794_ = 11ULL;
v___x_795_ = lean_uint64_mix_hash(v___x_793_, v___x_794_);
v___x_796_ = 32ULL;
v___x_797_ = lean_uint64_shift_right(v___x_795_, v___x_796_);
v_fold_798_ = lean_uint64_xor(v___x_795_, v___x_797_);
v___x_799_ = 16ULL;
v___x_800_ = lean_uint64_shift_right(v_fold_798_, v___x_799_);
v___x_801_ = lean_uint64_xor(v_fold_798_, v___x_800_);
v___x_802_ = lean_uint64_to_usize(v___x_801_);
v___x_803_ = lean_usize_of_nat(v___x_791_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_sub(v___x_803_, v___x_804_);
v___x_806_ = lean_usize_land(v___x_802_, v___x_805_);
v___x_807_ = lean_array_uget_borrowed(v_buckets_790_, v___x_806_);
v___x_808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_789_, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_809_, v_a_810_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_m_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_813_; lean_object* v_dummy_814_; 
v___x_813_ = lean_box(0);
v_dummy_814_ = l_Lean_Expr_sort___override(v___x_813_);
return v_dummy_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_e_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; 
if (lean_obj_tag(v_x_816_) == 5)
{
lean_object* v_fn_843_; lean_object* v_arg_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_fn_843_ = lean_ctor_get(v_x_816_, 0);
lean_inc_ref(v_fn_843_);
v_arg_844_ = lean_ctor_get(v_x_816_, 1);
lean_inc_ref(v_arg_844_);
lean_dec_ref_known(v_x_816_, 2);
v___x_845_ = lean_array_set(v_x_817_, v_x_818_, v_arg_844_);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_sub(v_x_818_, v___x_846_);
lean_dec(v_x_818_);
v_x_816_ = v_fn_843_;
v_x_817_ = v___x_845_;
v_x_818_ = v___x_847_;
goto _start;
}
else
{
lean_dec(v_x_818_);
if (lean_obj_tag(v_x_816_) == 4)
{
lean_object* v_declName_849_; lean_object* v_funName_850_; uint8_t v___x_851_; 
v_declName_849_ = lean_ctor_get(v_x_816_, 0);
lean_inc(v_declName_849_);
lean_dec_ref_known(v_x_816_, 2);
v_funName_850_ = lean_ctor_get(v___y_820_, 0);
v___x_851_ = lean_name_eq(v_declName_849_, v_funName_850_);
lean_dec(v_declName_849_);
if (v___x_851_ == 0)
{
lean_dec_ref(v_e_815_);
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
goto v___jp_827_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_Expr_hasLooseBVars(v_e_815_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_inc_ref(v___y_820_);
v___x_853_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_815_, v___y_820_, v_x_817_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_dec_ref_known(v___x_853_, 1);
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
goto v___jp_827_;
}
else
{
lean_dec_ref(v_x_817_);
return v___x_853_;
}
}
else
{
lean_dec_ref(v_e_815_);
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
goto v___jp_827_;
}
}
}
else
{
lean_object* v___x_854_; 
lean_dec_ref(v_e_815_);
v___x_854_ = l_Lean_Meta_FunInd_Collector_visit(v_x_816_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_dec_ref_known(v___x_854_, 1);
v___y_828_ = v___y_819_;
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
goto v___jp_827_;
}
else
{
lean_dec_ref(v_x_817_);
return v___x_854_;
}
}
}
v___jp_827_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_array_get_size(v_x_817_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_nat_dec_lt(v___x_835_, v___x_836_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v_x_817_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
return v___x_839_;
}
else
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)0ULL);
v___x_841_ = lean_usize_of_nat(v___x_836_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_817_, v___x_840_, v___x_841_, v___x_837_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec_ref(v_x_817_);
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_d_865_; lean_object* v_b_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_st_ref_get(v_a_856_);
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_876_, v_e_855_);
lean_dec(v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = lean_st_ref_take(v_a_856_);
v___x_879_ = lean_box(0);
lean_inc_ref(v_e_855_);
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_878_, v_e_855_, v___x_879_);
v___x_881_ = lean_st_ref_put(v_a_856_, v___x_880_);
switch(lean_obj_tag(v_e_855_))
{
case 7:
{
lean_object* v_binderType_882_; lean_object* v_body_883_; 
v_binderType_882_ = lean_ctor_get(v_e_855_, 1);
lean_inc_ref(v_binderType_882_);
v_body_883_ = lean_ctor_get(v_e_855_, 2);
lean_inc_ref(v_body_883_);
lean_dec_ref_known(v_e_855_, 3);
v_d_865_ = v_binderType_882_;
v_b_866_ = v_body_883_;
v___y_867_ = v_a_856_;
v___y_868_ = v_a_857_;
v___y_869_ = v_a_858_;
v___y_870_ = v_a_859_;
v___y_871_ = v_a_860_;
v___y_872_ = v_a_861_;
v___y_873_ = v_a_862_;
goto v___jp_864_;
}
case 6:
{
lean_object* v_binderType_884_; lean_object* v_body_885_; 
v_binderType_884_ = lean_ctor_get(v_e_855_, 1);
lean_inc_ref(v_binderType_884_);
v_body_885_ = lean_ctor_get(v_e_855_, 2);
lean_inc_ref(v_body_885_);
lean_dec_ref_known(v_e_855_, 3);
v_d_865_ = v_binderType_884_;
v_b_866_ = v_body_885_;
v___y_867_ = v_a_856_;
v___y_868_ = v_a_857_;
v___y_869_ = v_a_858_;
v___y_870_ = v_a_859_;
v___y_871_ = v_a_860_;
v___y_872_ = v_a_861_;
v___y_873_ = v_a_862_;
goto v___jp_864_;
}
case 10:
{
lean_object* v_expr_886_; 
v_expr_886_ = lean_ctor_get(v_e_855_, 1);
lean_inc_ref(v_expr_886_);
lean_dec_ref_known(v_e_855_, 2);
v_e_855_ = v_expr_886_;
goto _start;
}
case 8:
{
lean_object* v_type_888_; lean_object* v_value_889_; lean_object* v_body_890_; lean_object* v___x_891_; 
v_type_888_ = lean_ctor_get(v_e_855_, 1);
lean_inc_ref(v_type_888_);
v_value_889_ = lean_ctor_get(v_e_855_, 2);
lean_inc_ref(v_value_889_);
v_body_890_ = lean_ctor_get(v_e_855_, 3);
lean_inc_ref(v_body_890_);
lean_dec_ref_known(v_e_855_, 4);
v___x_891_ = l_Lean_Meta_FunInd_Collector_visit(v_type_888_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v___x_892_; 
lean_dec_ref_known(v___x_891_, 1);
v___x_892_ = l_Lean_Meta_FunInd_Collector_visit(v_value_889_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
v_e_855_ = v_body_890_;
goto _start;
}
else
{
lean_dec_ref(v_body_890_);
return v___x_892_;
}
}
else
{
lean_dec_ref(v_body_890_);
lean_dec_ref(v_value_889_);
return v___x_891_;
}
}
case 5:
{
lean_object* v_dummy_894_; lean_object* v_nargs_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_dummy_894_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_895_ = l_Lean_Expr_getAppNumArgs(v_e_855_);
lean_inc(v_nargs_895_);
v___x_896_ = lean_mk_array(v_nargs_895_, v_dummy_894_);
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_nat_sub(v_nargs_895_, v___x_897_);
lean_dec(v_nargs_895_);
lean_inc_ref(v_e_855_);
v___x_899_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_855_, v_e_855_, v___x_896_, v___x_898_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
return v___x_899_;
}
case 11:
{
lean_object* v_struct_900_; 
v_struct_900_ = lean_ctor_get(v_e_855_, 2);
lean_inc_ref(v_struct_900_);
lean_dec_ref_known(v_e_855_, 3);
v_e_855_ = v_struct_900_;
goto _start;
}
default: 
{
lean_object* v___x_902_; 
lean_dec_ref(v_e_855_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_879_);
return v___x_902_;
}
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref(v_e_855_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
v___jp_864_:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_FunInd_Collector_visit(v_d_865_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec_ref_known(v___x_874_, 1);
v_e_855_ = v_b_866_;
v_a_856_ = v___y_867_;
v_a_857_ = v___y_868_;
v_a_858_ = v___y_869_;
v_a_859_ = v___y_870_;
v_a_860_ = v___y_871_;
v_a_861_ = v___y_872_;
v_a_862_ = v___y_873_;
goto _start;
}
else
{
lean_dec_ref(v_b_866_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_905_, size_t v_i_906_, size_t v_stop_907_, lean_object* v_b_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v___x_917_; 
v___x_917_ = lean_usize_dec_eq(v_i_906_, v_stop_907_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_array_uget_borrowed(v_as_905_, v_i_906_);
lean_inc(v___x_918_);
v___x_919_ = l_Lean_Meta_FunInd_Collector_visit(v___x_918_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; size_t v___x_921_; size_t v___x_922_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_add(v_i_906_, v___x_921_);
v_i_906_ = v___x_922_;
v_b_908_ = v_a_920_;
goto _start;
}
else
{
return v___x_919_;
}
}
else
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_b_908_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_925_, lean_object* v_i_926_, lean_object* v_stop_927_, lean_object* v_b_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_i_boxed_937_; size_t v_stop_boxed_938_; lean_object* v_res_939_; 
v_i_boxed_937_ = lean_unbox_usize(v_i_926_);
lean_dec(v_i_926_);
v_stop_boxed_938_ = lean_unbox_usize(v_stop_927_);
lean_dec(v_stop_927_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_925_, v_i_boxed_937_, v_stop_boxed_938_, v_b_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v_as_925_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_e_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_940_, v_x_941_, v_x_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_FunInd_Collector_visit(v_e_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
return v_res_962_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_963_, lean_object* v_m_964_, lean_object* v_a_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_964_, v_a_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_967_, lean_object* v_m_968_, lean_object* v_a_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_967_, v_m_968_, v_a_969_);
lean_dec_ref(v_a_969_);
lean_dec_ref(v_m_968_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_, lean_object* v_b_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_973_, v_a_974_, v_b_975_);
return v___x_976_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_977_, lean_object* v_a_978_, lean_object* v_x_979_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_978_, v_x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_981_, lean_object* v_a_982_, lean_object* v_x_983_){
_start:
{
uint8_t v_res_984_; lean_object* v_r_985_; 
v_res_984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_981_, v_a_982_, v_x_983_);
lean_dec(v_x_983_);
lean_dec_ref(v_a_982_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object* v_00_u03b2_986_, lean_object* v_data_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_989_, lean_object* v_i_990_, lean_object* v_source_991_, lean_object* v_target_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_990_, v_source_991_, v_target_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_995_, v_x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_998_, lean_object* v___y_999_){
_start:
{
uint8_t v___x_1001_; 
v___x_1001_ = l_Lean_Expr_hasMVar(v_e_998_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v_e_998_);
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; lean_object* v_mctx_1004_; lean_object* v___x_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1008_; lean_object* v_cache_1009_; lean_object* v_zetaDeltaFVarIds_1010_; lean_object* v_postponed_1011_; lean_object* v_diag_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1021_; 
v___x_1003_ = lean_st_ref_get(v___y_999_);
v_mctx_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_mctx_1004_);
lean_dec(v___x_1003_);
v___x_1005_ = l_Lean_instantiateMVarsCore(v_mctx_1004_, v_e_998_);
v_fst_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_fst_1006_);
v_snd_1007_ = lean_ctor_get(v___x_1005_, 1);
lean_inc(v_snd_1007_);
lean_dec_ref(v___x_1005_);
v___x_1008_ = lean_st_ref_take(v___y_999_);
v_cache_1009_ = lean_ctor_get(v___x_1008_, 1);
v_zetaDeltaFVarIds_1010_ = lean_ctor_get(v___x_1008_, 2);
v_postponed_1011_ = lean_ctor_get(v___x_1008_, 3);
v_diag_1012_ = lean_ctor_get(v___x_1008_, 4);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_1008_, 0);
lean_dec(v_unused_1022_);
v___x_1014_ = v___x_1008_;
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_diag_1012_);
lean_inc(v_postponed_1011_);
lean_inc(v_zetaDeltaFVarIds_1010_);
lean_inc(v_cache_1009_);
lean_dec(v___x_1008_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_snd_1007_);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_snd_1007_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_cache_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_zetaDeltaFVarIds_1010_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_postponed_1011_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_diag_1012_);
v___x_1017_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_st_ref_put(v___y_999_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_fst_1006_);
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1023_, v___y_1024_);
lean_dec(v___y_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1027_, v___y_1032_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_b_1050_);
return v___x_1060_;
}
else
{
lean_object* v_snd_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1119_; 
v_snd_1061_ = lean_ctor_get(v_b_1050_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_b_1050_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_b_1050_, 0);
lean_dec(v_unused_1120_);
v___x_1063_ = v_b_1050_;
v_isShared_1064_ = v_isSharedCheck_1119_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snd_1061_);
lean_dec(v_b_1050_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1119_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v_a_1067_; lean_object* v_a_1074_; 
v___x_1065_ = lean_box(0);
v_a_1074_ = lean_array_uget_borrowed(v_as_1047_, v_i_1049_);
if (lean_obj_tag(v_a_1074_) == 0)
{
v_a_1067_ = v_snd_1061_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
lean_dec(v_snd_1061_);
v_val_1075_ = lean_ctor_get(v_a_1074_, 0);
v___x_1076_ = lean_box(0);
v___x_1077_ = l_Lean_LocalDecl_isAuxDecl(v_val_1075_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_LocalDecl_value_x3f(v_val_1075_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 1)
{
lean_object* v_val_1079_; lean_object* v___x_1080_; 
v_val_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_val_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1079_, v___y_1055_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1081_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_dec_ref_known(v___x_1082_, 1);
v_a_1067_ = v___x_1076_;
goto v___jp_1066_;
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_del_object(v___x_1063_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_del_object(v___x_1063_);
v_a_1091_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1080_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1080_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec(v___x_1078_);
v___x_1099_ = l_Lean_LocalDecl_type(v_val_1075_);
v___x_1100_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1099_, v___y_1055_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1101_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec_ref_known(v___x_1102_, 1);
v_a_1067_ = v___x_1076_;
goto v___jp_1066_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_del_object(v___x_1063_);
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
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
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_del_object(v___x_1063_);
v_a_1111_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1100_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1100_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
v_a_1067_ = v___x_1076_;
goto v___jp_1066_;
}
}
v___jp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v_a_1067_);
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1069_ = v___x_1063_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_a_1067_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
size_t v___x_1070_; size_t v___x_1071_; 
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1049_, v___x_1070_);
v_i_1049_ = v___x_1071_;
v_b_1050_ = v___x_1069_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1121_, lean_object* v_sz_1122_, lean_object* v_i_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
size_t v_sz_boxed_1133_; size_t v_i_boxed_1134_; lean_object* v_res_1135_; 
v_sz_boxed_1133_ = lean_unbox_usize(v_sz_1122_);
lean_dec(v_sz_1122_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1121_, v_sz_boxed_1133_, v_i_boxed_1134_, v_b_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v_as_1121_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1136_, size_t v_sz_1137_, size_t v_i_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1138_, v_sz_1137_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_b_1139_);
return v___x_1149_;
}
else
{
lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1208_; 
v_snd_1150_ = lean_ctor_get(v_b_1139_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_b_1139_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_b_1139_, 0);
lean_dec(v_unused_1209_);
v___x_1152_ = v_b_1139_;
v_isShared_1153_ = v_isSharedCheck_1208_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_dec(v_b_1139_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1208_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v_a_1156_; lean_object* v_a_1163_; 
v___x_1154_ = lean_box(0);
v_a_1163_ = lean_array_uget_borrowed(v_as_1136_, v_i_1138_);
if (lean_obj_tag(v_a_1163_) == 0)
{
v_a_1156_ = v_snd_1150_;
goto v___jp_1155_;
}
else
{
lean_object* v_val_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
lean_dec(v_snd_1150_);
v_val_1164_ = lean_ctor_get(v_a_1163_, 0);
v___x_1165_ = lean_box(0);
v___x_1166_ = l_Lean_LocalDecl_isAuxDecl(v_val_1164_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_LocalDecl_value_x3f(v_val_1164_, v___x_1166_);
if (lean_obj_tag(v___x_1167_) == 1)
{
lean_object* v_val_1168_; lean_object* v___x_1169_; 
v_val_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1168_, v___y_1144_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1170_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_dec_ref_known(v___x_1171_, 1);
v_a_1156_ = v___x_1165_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_del_object(v___x_1152_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_del_object(v___x_1152_);
v_a_1180_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1169_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1169_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v___x_1167_);
v___x_1188_ = l_Lean_LocalDecl_type(v_val_1164_);
v___x_1189_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1188_, v___y_1144_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1190_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_dec_ref_known(v___x_1191_, 1);
v_a_1156_ = v___x_1165_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_del_object(v___x_1152_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
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
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_del_object(v___x_1152_);
v_a_1200_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1189_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1189_);
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
else
{
v_a_1156_ = v___x_1165_;
goto v___jp_1155_;
}
}
v___jp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_a_1156_);
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1158_ = v___x_1152_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_a_1156_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = ((size_t)1ULL);
v___x_1160_ = lean_usize_add(v_i_1138_, v___x_1159_);
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1136_, v_sz_1137_, v___x_1160_, v___x_1158_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1210_, lean_object* v_sz_1211_, lean_object* v_i_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
size_t v_sz_boxed_1222_; size_t v_i_boxed_1223_; lean_object* v_res_1224_; 
v_sz_boxed_1222_ = lean_unbox_usize(v_sz_1211_);
lean_dec(v_sz_1211_);
v_i_boxed_1223_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1210_, v_sz_boxed_1222_, v_i_boxed_1223_, v_b_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v_as_1210_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1225_, size_t v_sz_1226_, size_t v_i_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_usize_dec_lt(v_i_1227_, v_sz_1226_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_b_1228_);
return v___x_1238_;
}
else
{
lean_object* v_snd_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1297_; 
v_snd_1239_ = lean_ctor_get(v_b_1228_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_b_1228_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_b_1228_, 0);
lean_dec(v_unused_1298_);
v___x_1241_ = v_b_1228_;
v_isShared_1242_ = v_isSharedCheck_1297_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_snd_1239_);
lean_dec(v_b_1228_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1297_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v_a_1245_; lean_object* v_a_1252_; 
v___x_1243_ = lean_box(0);
v_a_1252_ = lean_array_uget_borrowed(v_as_1225_, v_i_1227_);
if (lean_obj_tag(v_a_1252_) == 0)
{
v_a_1245_ = v_snd_1239_;
goto v___jp_1244_;
}
else
{
lean_object* v_val_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
lean_dec(v_snd_1239_);
v_val_1253_ = lean_ctor_get(v_a_1252_, 0);
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Lean_LocalDecl_isAuxDecl(v_val_1253_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_LocalDecl_value_x3f(v_val_1253_, v___x_1255_);
if (lean_obj_tag(v___x_1256_) == 1)
{
lean_object* v_val_1257_; lean_object* v___x_1258_; 
v_val_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1257_, v___y_1233_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1259_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_dec_ref_known(v___x_1260_, 1);
v_a_1245_ = v___x_1254_;
goto v___jp_1244_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_del_object(v___x_1241_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1241_);
v_a_1269_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1258_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1258_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v___x_1256_);
v___x_1277_ = l_Lean_LocalDecl_type(v_val_1253_);
v___x_1278_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1277_, v___y_1233_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1279_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_dec_ref_known(v___x_1280_, 1);
v_a_1245_ = v___x_1254_;
goto v___jp_1244_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1241_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_del_object(v___x_1241_);
v_a_1289_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1278_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1278_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
else
{
v_a_1245_ = v___x_1254_;
goto v___jp_1244_;
}
}
v___jp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_a_1245_);
lean_ctor_set(v___x_1241_, 0, v___x_1243_);
v___x_1247_ = v___x_1241_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_a_1245_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
size_t v___x_1248_; size_t v___x_1249_; 
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_i_1227_, v___x_1248_);
v_i_1227_ = v___x_1249_;
v_b_1228_ = v___x_1247_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1299_, v_sz_boxed_1311_, v_i_boxed_1312_, v_b_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v_as_1299_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1314_, size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_lt(v_i_1316_, v_sz_1315_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_b_1317_);
return v___x_1327_;
}
else
{
lean_object* v_snd_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1386_; 
v_snd_1328_ = lean_ctor_get(v_b_1317_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_b_1317_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v_b_1317_, 0);
lean_dec(v_unused_1387_);
v___x_1330_ = v_b_1317_;
v_isShared_1331_ = v_isSharedCheck_1386_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_snd_1328_);
lean_dec(v_b_1317_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1386_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v_a_1334_; lean_object* v_a_1341_; 
v___x_1332_ = lean_box(0);
v_a_1341_ = lean_array_uget_borrowed(v_as_1314_, v_i_1316_);
if (lean_obj_tag(v_a_1341_) == 0)
{
v_a_1334_ = v_snd_1328_;
goto v___jp_1333_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
lean_dec(v_snd_1328_);
v_val_1342_ = lean_ctor_get(v_a_1341_, 0);
v___x_1343_ = lean_box(0);
v___x_1344_ = l_Lean_LocalDecl_isAuxDecl(v_val_1342_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_LocalDecl_value_x3f(v_val_1342_, v___x_1344_);
if (lean_obj_tag(v___x_1345_) == 1)
{
lean_object* v_val_1346_; lean_object* v___x_1347_; 
v_val_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1346_, v___y_1322_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1348_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec_ref_known(v___x_1349_, 1);
v_a_1334_ = v___x_1343_;
goto v___jp_1333_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_del_object(v___x_1330_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_del_object(v___x_1330_);
v_a_1358_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1347_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1347_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v___x_1345_);
v___x_1366_ = l_Lean_LocalDecl_type(v_val_1342_);
v___x_1367_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1366_, v___y_1322_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v___x_1369_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1368_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec_ref_known(v___x_1369_, 1);
v_a_1334_ = v___x_1343_;
goto v___jp_1333_;
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_del_object(v___x_1330_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_del_object(v___x_1330_);
v_a_1378_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1367_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1367_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
else
{
v_a_1334_ = v___x_1343_;
goto v___jp_1333_;
}
}
v___jp_1333_:
{
lean_object* v___x_1336_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v_a_1334_);
lean_ctor_set(v___x_1330_, 0, v___x_1332_);
v___x_1336_ = v___x_1330_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_a_1334_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1316_, v___x_1337_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1314_, v_sz_1315_, v___x_1338_, v___x_1336_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1388_, lean_object* v_sz_1389_, lean_object* v_i_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
size_t v_sz_boxed_1400_; size_t v_i_boxed_1401_; lean_object* v_res_1402_; 
v_sz_boxed_1400_ = lean_unbox_usize(v_sz_1389_);
lean_dec(v_sz_1389_);
v_i_boxed_1401_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1388_, v_sz_boxed_1400_, v_i_boxed_1401_, v_b_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v_as_1388_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_init_1403_, lean_object* v_n_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
if (lean_obj_tag(v_n_1404_) == 0)
{
lean_object* v_cs_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v_sz_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v_cs_1414_ = lean_ctor_get(v_n_1404_, 0);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v_b_1405_);
v_sz_1417_ = lean_array_size(v_cs_1414_);
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1403_, v_cs_1414_, v_sz_1417_, v___x_1418_, v___x_1416_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1434_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1434_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1434_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_fst_1424_; 
v_fst_1424_ = lean_ctor_get(v_a_1420_, 0);
if (lean_obj_tag(v_fst_1424_) == 0)
{
lean_object* v_snd_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v_snd_1425_ = lean_ctor_get(v_a_1420_, 1);
lean_inc(v_snd_1425_);
lean_dec(v_a_1420_);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_snd_1425_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1426_);
v___x_1428_ = v___x_1422_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
lean_object* v_val_1430_; lean_object* v___x_1432_; 
lean_inc_ref(v_fst_1424_);
lean_dec(v_a_1420_);
v_val_1430_ = lean_ctor_get(v_fst_1424_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v_fst_1424_, 1);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v_val_1430_);
v___x_1432_ = v___x_1422_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_val_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_a_1435_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1419_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1419_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_vs_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; size_t v_sz_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v_vs_1443_ = lean_ctor_get(v_n_1404_, 0);
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v_b_1405_);
v_sz_1446_ = lean_array_size(v_vs_1443_);
v___x_1447_ = ((size_t)0ULL);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1443_, v_sz_1446_, v___x_1447_, v___x_1445_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1463_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_fst_1453_; 
v_fst_1453_ = lean_ctor_get(v_a_1449_, 0);
if (lean_obj_tag(v_fst_1453_) == 0)
{
lean_object* v_snd_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v_snd_1454_ = lean_ctor_get(v_a_1449_, 1);
lean_inc(v_snd_1454_);
lean_dec(v_a_1449_);
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_snd_1454_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1455_);
v___x_1457_ = v___x_1451_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v_val_1459_; lean_object* v___x_1461_; 
lean_inc_ref(v_fst_1453_);
lean_dec(v_a_1449_);
v_val_1459_ = lean_ctor_get(v_fst_1453_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v_fst_1453_, 1);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v_val_1459_);
v___x_1461_ = v___x_1451_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_val_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1448_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1448_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_init_1472_, lean_object* v_as_1473_, size_t v_sz_1474_, size_t v_i_1475_, lean_object* v_b_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_usize_dec_lt(v_i_1475_, v_sz_1474_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1476_);
return v___x_1486_;
}
else
{
lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1521_; 
v_snd_1487_ = lean_ctor_get(v_b_1476_, 1);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_b_1476_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v_b_1476_, 0);
lean_dec(v_unused_1522_);
v___x_1489_ = v_b_1476_;
v_isShared_1490_ = v_isSharedCheck_1521_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_dec(v_b_1476_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1521_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v_a_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_box(0);
v_a_1492_ = lean_array_uget_borrowed(v_as_1473_, v_i_1475_);
lean_inc(v_snd_1487_);
v___x_1493_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1472_, v_a_1492_, v_snd_1487_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1512_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
if (lean_obj_tag(v_a_1494_) == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_a_1494_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1498_);
v___x_1500_ = v___x_1489_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_snd_1487_);
v___x_1500_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1500_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; 
lean_del_object(v___x_1496_);
lean_dec(v_snd_1487_);
v_a_1505_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v_a_1494_, 1);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v_a_1505_);
lean_ctor_set(v___x_1489_, 0, v___x_1491_);
v___x_1507_ = v___x_1489_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_a_1505_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
size_t v___x_1508_; size_t v___x_1509_; 
v___x_1508_ = ((size_t)1ULL);
v___x_1509_ = lean_usize_add(v_i_1475_, v___x_1508_);
v_i_1475_ = v___x_1509_;
v_b_1476_ = v___x_1507_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_del_object(v___x_1489_);
lean_dec(v_snd_1487_);
v_a_1513_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1493_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1493_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1523_, lean_object* v_as_1524_, lean_object* v_sz_1525_, lean_object* v_i_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1525_);
lean_dec(v_sz_1525_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1526_);
lean_dec(v_i_1526_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1523_, v_as_1524_, v_sz_boxed_1536_, v_i_boxed_1537_, v_b_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v_as_1524_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_init_1539_, lean_object* v_n_1540_, lean_object* v_b_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1539_, v_n_1540_, v_b_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v_n_1540_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1551_, lean_object* v_init_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_root_1561_; lean_object* v_tail_1562_; lean_object* v___x_1563_; 
v_root_1561_ = lean_ctor_get(v_t_1551_, 0);
v_tail_1562_ = lean_ctor_get(v_t_1551_, 1);
v___x_1563_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1552_, v_root_1561_, v_init_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1600_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1600_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1600_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
if (lean_obj_tag(v_a_1564_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v_a_1564_, 1);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_a_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
lean_del_object(v___x_1566_);
v_a_1572_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v_a_1564_, 1);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_a_1572_);
v_sz_1575_ = lean_array_size(v_tail_1562_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1562_, v_sz_1575_, v___x_1576_, v___x_1574_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1591_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_fst_1582_; 
v_fst_1582_ = lean_ctor_get(v_a_1578_, 0);
if (lean_obj_tag(v_fst_1582_) == 0)
{
lean_object* v_snd_1583_; lean_object* v___x_1585_; 
v_snd_1583_ = lean_ctor_get(v_a_1578_, 1);
lean_inc(v_snd_1583_);
lean_dec(v_a_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_snd_1583_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_snd_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v_val_1587_; lean_object* v___x_1589_; 
lean_inc_ref(v_fst_1582_);
lean_dec(v_a_1578_);
v_val_1587_ = lean_ctor_get(v_fst_1582_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v_fst_1582_, 1);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_val_1587_);
v___x_1589_ = v___x_1580_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_val_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_a_1592_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1577_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1577_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1563_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1563_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1609_, lean_object* v_init_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1609_, v_init_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v_t_1609_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_lctx_1629_; lean_object* v_decls_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_lctx_1629_ = lean_ctor_get(v_a_1624_, 2);
v_decls_1630_ = lean_ctor_get(v_lctx_1629_, 1);
v___x_1631_ = lean_box(0);
v___x_1632_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1630_, v___x_1631_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref_known(v___x_1632_, 1);
v___x_1633_ = l_Lean_MVarId_getType(v_mvarId_1620_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1634_, v_a_1625_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1636_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
return v___x_1637_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1635_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1635_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1633_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1633_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_dec(v_mvarId_1620_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1664_, v_x_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_a_1680_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1671_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1671_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1688_, lean_object* v_x_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1688_, v_x_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1696_, lean_object* v_mvarId_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1697_, v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_mvarId_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1705_, v_mvarId_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1714_, lean_object* v___x_1715_, lean_object* v_mvarId_1716_, lean_object* v_needle_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = lean_st_mk_ref(v___x_1714_);
v___x_1724_ = lean_st_mk_ref(v___x_1715_);
v___x_1725_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1716_, v___x_1724_, v_needle_1717_, v___x_1723_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1735_; 
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v___x_1725_, 0);
lean_dec(v_unused_1736_);
v___x_1727_ = v___x_1725_;
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
else
{
lean_dec(v___x_1725_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v_calls_1731_; lean_object* v___x_1733_; 
v___x_1729_ = lean_st_ref_get(v___x_1724_);
lean_dec(v___x_1724_);
lean_dec(v___x_1729_);
v___x_1730_ = lean_st_ref_get(v___x_1723_);
lean_dec(v___x_1723_);
v_calls_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc_ref(v_calls_1731_);
lean_dec(v___x_1730_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v_calls_1731_);
v___x_1733_ = v___x_1727_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_calls_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v___x_1724_);
lean_dec(v___x_1723_);
v_a_1737_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1725_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1745_, lean_object* v___x_1746_, lean_object* v_mvarId_1747_, lean_object* v_needle_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1745_, v___x_1746_, v_mvarId_1747_, v_needle_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v_needle_1748_);
return v_res_1754_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_unsigned_to_nat(64u);
v___x_1756_ = l_Lean_mkPtrSet___redArg(v___x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1757_, lean_object* v_mvarId_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___f_1766_; lean_object* v___x_1767_; 
v___x_1764_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_1765_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
lean_inc(v_mvarId_1758_);
v___f_1766_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1766_, 0, v___x_1765_);
lean_closure_set(v___f_1766_, 1, v___x_1764_);
lean_closure_set(v___f_1766_, 2, v_mvarId_1758_);
lean_closure_set(v___f_1766_, 3, v_needle_1757_);
v___x_1767_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1758_, v___f_1766_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_1768_, lean_object* v_mvarId_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1768_, v_mvarId_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_1776_, lean_object* v_mvarId_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1776_, v_mvarId_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_1784_, lean_object* v_mvarId_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1784_, v_mvarId_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_1792_, lean_object* v_mvarId_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1792_, v_mvarId_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_1800_, lean_object* v_mvarId_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Meta_FunInd_collect(v_needle_1800_, v_mvarId_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
return v_res_1807_;
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
