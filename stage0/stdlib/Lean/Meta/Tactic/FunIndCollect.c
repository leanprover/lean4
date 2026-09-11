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
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_nbuckets_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_163_ = lean_array_get_size(v_data_162_);
v___x_164_ = lean_unsigned_to_nat(2u);
v_nbuckets_165_ = lean_nat_mul(v___x_163_, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_box(0);
v___x_168_ = lean_mk_array(v_nbuckets_165_, v___x_167_);
v___x_169_ = lean_array_propagate_mark(v_data_162_, v___x_168_);
v___x_170_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_166_, v_data_162_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object* v_m_171_, lean_object* v_a_172_, lean_object* v_b_173_){
_start:
{
lean_object* v_size_174_; lean_object* v_buckets_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; uint64_t v___y_180_; uint64_t v___y_181_; uint64_t v___y_220_; 
v_size_174_ = lean_ctor_get(v_m_171_, 0);
v_buckets_175_ = lean_ctor_get(v_m_171_, 1);
v_fst_176_ = lean_ctor_get(v_a_172_, 0);
v_snd_177_ = lean_ctor_get(v_a_172_, 1);
v___x_178_ = lean_array_get_size(v_buckets_175_);
if (lean_obj_tag(v_fst_176_) == 0)
{
uint64_t v___x_228_; 
v___x_228_ = 1723ULL;
v___y_220_ = v___x_228_;
goto v___jp_219_;
}
else
{
uint64_t v_hash_229_; 
v_hash_229_ = lean_ctor_get_uint64(v_fst_176_, sizeof(void*)*2);
v___y_220_ = v_hash_229_;
goto v___jp_219_;
}
v___jp_179_:
{
uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v_fold_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; lean_object* v_bkt_194_; uint8_t v___x_195_; 
v___x_182_ = lean_uint64_mix_hash(v___y_180_, v___y_181_);
v___x_183_ = 32ULL;
v___x_184_ = lean_uint64_shift_right(v___x_182_, v___x_183_);
v_fold_185_ = lean_uint64_xor(v___x_182_, v___x_184_);
v___x_186_ = 16ULL;
v___x_187_ = lean_uint64_shift_right(v_fold_185_, v___x_186_);
v___x_188_ = lean_uint64_xor(v_fold_185_, v___x_187_);
v___x_189_ = lean_uint64_to_usize(v___x_188_);
v___x_190_ = lean_usize_of_nat(v___x_178_);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_sub(v___x_190_, v___x_191_);
v___x_193_ = lean_usize_land(v___x_189_, v___x_192_);
v_bkt_194_ = lean_array_uget_borrowed(v_buckets_175_, v___x_193_);
v___x_195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_172_, v_bkt_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_216_; 
lean_inc_ref(v_buckets_175_);
lean_inc(v_size_174_);
v_isSharedCheck_216_ = !lean_is_exclusive(v_m_171_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_217_ = lean_ctor_get(v_m_171_, 1);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_m_171_, 0);
lean_dec(v_unused_218_);
v___x_197_ = v_m_171_;
v_isShared_198_ = v_isSharedCheck_216_;
goto v_resetjp_196_;
}
else
{
lean_dec(v_m_171_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_216_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v_size_x27_200_; lean_object* v___x_201_; lean_object* v_buckets_x27_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v_size_x27_200_ = lean_nat_add(v_size_174_, v___x_199_);
lean_dec(v_size_174_);
lean_inc(v_bkt_194_);
v___x_201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_201_, 0, v_a_172_);
lean_ctor_set(v___x_201_, 1, v_b_173_);
lean_ctor_set(v___x_201_, 2, v_bkt_194_);
v_buckets_x27_202_ = lean_array_uset(v_buckets_175_, v___x_193_, v___x_201_);
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
v_val_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_202_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v_val_209_);
lean_ctor_set(v___x_197_, 0, v_size_x27_200_);
v___x_211_ = v___x_197_;
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
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v_buckets_x27_202_);
lean_ctor_set(v___x_197_, 0, v_size_x27_200_);
v___x_214_ = v___x_197_;
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
}
else
{
lean_dec(v_b_173_);
lean_dec_ref(v_a_172_);
return v_m_171_;
}
}
v___jp_219_:
{
uint64_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_221_ = 7ULL;
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_array_get_size(v_snd_177_);
v___x_224_ = lean_nat_dec_lt(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
v___y_180_ = v___y_220_;
v___y_181_ = v___x_221_;
goto v___jp_179_;
}
else
{
size_t v___x_225_; size_t v___x_226_; uint64_t v___x_227_; 
v___x_225_ = ((size_t)0ULL);
v___x_226_ = lean_usize_of_nat(v___x_223_);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_177_, v___x_225_, v___x_226_, v___x_221_);
v___y_180_ = v___y_220_;
v___y_181_ = v___x_227_;
goto v___jp_179_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object* v_m_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_buckets_232_; lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_235_; uint64_t v___y_237_; uint64_t v___y_238_; uint64_t v___y_254_; 
v_buckets_232_ = lean_ctor_get(v_m_230_, 1);
v_fst_233_ = lean_ctor_get(v_a_231_, 0);
v_snd_234_ = lean_ctor_get(v_a_231_, 1);
v___x_235_ = lean_array_get_size(v_buckets_232_);
if (lean_obj_tag(v_fst_233_) == 0)
{
uint64_t v___x_262_; 
v___x_262_ = 1723ULL;
v___y_254_ = v___x_262_;
goto v___jp_253_;
}
else
{
uint64_t v_hash_263_; 
v_hash_263_ = lean_ctor_get_uint64(v_fst_233_, sizeof(void*)*2);
v___y_254_ = v_hash_263_;
goto v___jp_253_;
}
v___jp_236_:
{
uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v_fold_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_239_ = lean_uint64_mix_hash(v___y_237_, v___y_238_);
v___x_240_ = 32ULL;
v___x_241_ = lean_uint64_shift_right(v___x_239_, v___x_240_);
v_fold_242_ = lean_uint64_xor(v___x_239_, v___x_241_);
v___x_243_ = 16ULL;
v___x_244_ = lean_uint64_shift_right(v_fold_242_, v___x_243_);
v___x_245_ = lean_uint64_xor(v_fold_242_, v___x_244_);
v___x_246_ = lean_uint64_to_usize(v___x_245_);
v___x_247_ = lean_usize_of_nat(v___x_235_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_sub(v___x_247_, v___x_248_);
v___x_250_ = lean_usize_land(v___x_246_, v___x_249_);
v___x_251_ = lean_array_uget_borrowed(v_buckets_232_, v___x_250_);
v___x_252_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_231_, v___x_251_);
return v___x_252_;
}
v___jp_253_:
{
uint64_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_255_ = 7ULL;
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_array_get_size(v_snd_234_);
v___x_258_ = lean_nat_dec_lt(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
v___y_237_ = v___y_254_;
v___y_238_ = v___x_255_;
goto v___jp_236_;
}
else
{
size_t v___x_259_; size_t v___x_260_; uint64_t v___x_261_; 
v___x_259_ = ((size_t)0ULL);
v___x_260_ = lean_usize_of_nat(v___x_257_);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_234_, v___x_259_, v___x_260_, v___x_255_);
v___y_237_ = v___y_254_;
v___y_238_ = v___x_261_;
goto v___jp_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object* v_m_264_, lean_object* v_a_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_264_, v_a_265_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_m_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object* v_calls_268_, lean_object* v_as_269_, size_t v_sz_270_, size_t v_i_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_a_275_; uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_lt(v_i_271_, v_sz_270_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_calls_268_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_b_272_);
return v___x_280_;
}
else
{
lean_object* v_snd_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_338_; 
v_snd_281_ = lean_ctor_get(v_b_272_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_b_272_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v_b_272_, 0);
lean_dec(v_unused_339_);
v___x_283_ = v_b_272_;
v_isShared_284_ = v_isSharedCheck_338_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_snd_281_);
lean_dec(v_b_272_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_338_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_snd_285_; lean_object* v_fst_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_337_; 
v_snd_285_ = lean_ctor_get(v_snd_281_, 1);
v_fst_286_ = lean_ctor_get(v_snd_281_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_snd_281_);
if (v_isSharedCheck_337_ == 0)
{
v___x_288_ = v_snd_281_;
v_isShared_289_ = v_isSharedCheck_337_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_snd_285_);
lean_inc(v_fst_286_);
lean_dec(v_snd_281_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_337_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_array_290_; lean_object* v_start_291_; lean_object* v_stop_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_array_290_ = lean_ctor_get(v_snd_285_, 0);
v_start_291_ = lean_ctor_get(v_snd_285_, 1);
v_stop_292_ = lean_ctor_get(v_snd_285_, 2);
v___x_293_ = lean_box(0);
v___x_294_ = lean_nat_dec_lt(v_start_291_, v_stop_292_);
if (v___x_294_ == 0)
{
lean_object* v___x_296_; 
lean_dec_ref(v_calls_268_);
if (v_isShared_289_ == 0)
{
v___x_296_ = v___x_288_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_fst_286_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_snd_285_);
v___x_296_ = v_reuseFailAlloc_301_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_296_);
lean_ctor_set(v___x_283_, 0, v___x_293_);
v___x_298_ = v___x_283_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
}
else
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_333_; 
lean_inc(v_stop_292_);
lean_inc(v_start_291_);
lean_inc_ref(v_array_290_);
v_isSharedCheck_333_ = !lean_is_exclusive(v_snd_285_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; lean_object* v_unused_335_; lean_object* v_unused_336_; 
v_unused_334_ = lean_ctor_get(v_snd_285_, 2);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_snd_285_, 1);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_snd_285_, 0);
lean_dec(v_unused_336_);
v___x_303_ = v_snd_285_;
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_snd_285_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_a_305_ = lean_array_uget_borrowed(v_as_269_, v_i_271_);
v___x_306_ = lean_array_fget(v_array_290_, v_start_291_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_start_291_, v___x_307_);
lean_dec(v_start_291_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_308_);
v___x_310_ = v___x_303_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_array_290_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_stop_292_);
v___x_310_ = v_reuseFailAlloc_332_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
uint8_t v___x_326_; 
v___x_326_ = lean_unbox(v___x_306_);
if (v___x_326_ == 2)
{
uint8_t v___x_327_; 
v___x_327_ = l_Lean_Expr_isFVar(v_a_305_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v___x_306_);
lean_del_object(v___x_288_);
lean_del_object(v___x_283_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_calls_268_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_fst_286_);
lean_ctor_set(v___x_329_, 1, v___x_310_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
goto v___jp_311_;
}
}
else
{
goto v___jp_311_;
}
v___jp_311_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_unbox(v___x_306_);
lean_dec(v___x_306_);
if (v___x_312_ == 0)
{
lean_object* v___x_314_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_310_);
v___x_314_ = v___x_288_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_fst_286_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_310_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_314_);
lean_ctor_set(v___x_283_, 0, v___x_293_);
v___x_316_ = v___x_283_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v_a_275_ = v___x_316_;
goto v___jp_274_;
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_inc(v_a_305_);
v___x_319_ = lean_array_push(v_fst_286_, v_a_305_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_310_);
lean_ctor_set(v___x_288_, 0, v___x_319_);
v___x_321_ = v___x_288_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_310_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_321_);
lean_ctor_set(v___x_283_, 0, v___x_293_);
v___x_323_ = v___x_283_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v_a_275_ = v___x_323_;
goto v___jp_274_;
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
v___jp_274_:
{
size_t v___x_276_; size_t v___x_277_; 
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_add(v_i_271_, v___x_276_);
v_i_271_ = v___x_277_;
v_b_272_ = v_a_275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object* v_calls_340_, lean_object* v_as_341_, lean_object* v_sz_342_, lean_object* v_i_343_, lean_object* v_b_344_, lean_object* v___y_345_){
_start:
{
size_t v_sz_boxed_346_; size_t v_i_boxed_347_; lean_object* v_res_348_; 
v_sz_boxed_346_ = lean_unbox_usize(v_sz_342_);
lean_dec(v_sz_342_);
v_i_boxed_347_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_res_348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_340_, v_as_341_, v_sz_boxed_346_, v_i_boxed_347_, v_b_344_);
lean_dec_ref(v_as_341_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object* v_e_349_, lean_object* v_funIndInfo_350_, lean_object* v_args_351_, lean_object* v_calls_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_funName_358_; lean_object* v_params_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_funName_358_ = lean_ctor_get(v_funIndInfo_350_, 0);
lean_inc(v_funName_358_);
v_params_359_ = lean_ctor_get(v_funIndInfo_350_, 3);
lean_inc_ref(v_params_359_);
lean_dec_ref(v_funIndInfo_350_);
v___x_360_ = lean_array_get_size(v_params_359_);
v___x_361_ = lean_array_get_size(v_args_351_);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec_ref(v_params_359_);
lean_dec(v_funName_358_);
lean_dec_ref(v_e_349_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_calls_352_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v_keys_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; size_t v_sz_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v_keys_365_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_366_ = l_Array_toSubarray___redArg(v_params_359_, v___x_364_, v___x_360_);
v___x_367_ = lean_box(0);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_keys_365_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v_sz_370_ = lean_array_size(v_args_351_);
v___x_371_ = ((size_t)0ULL);
lean_inc_ref(v_calls_352_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_352_, v_args_351_, v_sz_370_, v___x_371_, v___x_369_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_413_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_413_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_413_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_413_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_fst_377_; 
v_fst_377_ = lean_ctor_get(v_a_373_, 0);
if (lean_obj_tag(v_fst_377_) == 0)
{
lean_object* v_snd_378_; lean_object* v_fst_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_407_; 
v_snd_378_ = lean_ctor_get(v_a_373_, 1);
lean_inc(v_snd_378_);
lean_dec(v_a_373_);
v_fst_379_ = lean_ctor_get(v_snd_378_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_snd_378_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v_snd_378_, 1);
lean_dec(v_unused_408_);
v___x_381_ = v_snd_378_;
v_isShared_382_ = v_isSharedCheck_407_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_fst_379_);
lean_dec(v_snd_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_407_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_calls_383_; lean_object* v_seen_384_; lean_object* v___x_386_; 
v_calls_383_ = lean_ctor_get(v_calls_352_, 0);
v_seen_384_ = lean_ctor_get(v_calls_352_, 1);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v_fst_379_);
lean_ctor_set(v___x_381_, 0, v_funName_358_);
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_funName_358_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_fst_379_);
v___x_386_ = v_reuseFailAlloc_406_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
uint8_t v___x_387_; 
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_384_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_400_; 
lean_inc_ref(v_seen_384_);
lean_inc_ref(v_calls_383_);
v_isSharedCheck_400_ = !lean_is_exclusive(v_calls_352_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_401_ = lean_ctor_get(v_calls_352_, 1);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_calls_352_, 0);
lean_dec(v_unused_402_);
v___x_389_ = v_calls_352_;
v_isShared_390_ = v_isSharedCheck_400_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_calls_352_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_400_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_391_ = lean_array_push(v_calls_383_, v_e_349_);
v___x_392_ = lean_box(0);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_384_, v___x_386_, v___x_392_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_393_);
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_399_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_395_);
v___x_397_ = v___x_375_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v___x_386_);
lean_dec_ref(v_e_349_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v_calls_352_);
v___x_404_ = v___x_375_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_calls_352_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
else
{
lean_object* v_val_409_; lean_object* v___x_411_; 
lean_inc_ref(v_fst_377_);
lean_dec(v_a_373_);
lean_dec(v_funName_358_);
lean_dec_ref(v_calls_352_);
lean_dec_ref(v_e_349_);
v_val_409_ = lean_ctor_get(v_fst_377_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v_fst_377_, 1);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v_val_409_);
v___x_411_ = v___x_375_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_val_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_funName_358_);
lean_dec_ref(v_calls_352_);
lean_dec_ref(v_e_349_);
v_a_414_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_372_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_372_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object* v_e_422_, lean_object* v_funIndInfo_423_, lean_object* v_args_424_, lean_object* v_calls_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_422_, v_funIndInfo_423_, v_args_424_, v_calls_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec_ref(v_args_424_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object* v_calls_432_, lean_object* v_as_433_, size_t v_sz_434_, size_t v_i_435_, lean_object* v_b_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_432_, v_as_433_, v_sz_434_, v_i_435_, v_b_436_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object* v_calls_443_, lean_object* v_as_444_, lean_object* v_sz_445_, lean_object* v_i_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_sz_boxed_453_ = lean_unbox_usize(v_sz_445_);
lean_dec(v_sz_445_);
v_i_boxed_454_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_443_, v_as_444_, v_sz_boxed_453_, v_i_boxed_454_, v_b_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec_ref(v_as_444_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object* v_00_u03b2_456_, lean_object* v_m_457_, lean_object* v_a_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_457_, v_a_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object* v_00_u03b2_460_, lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(v_00_u03b2_460_, v_m_461_, v_a_462_);
lean_dec_ref(v_a_462_);
lean_dec_ref(v_m_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object* v_00_u03b2_465_, lean_object* v_m_466_, lean_object* v_a_467_, lean_object* v_b_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_466_, v_a_467_, v_b_468_);
return v___x_469_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_a_471_, lean_object* v_x_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object* v_00_u03b2_474_, lean_object* v_a_475_, lean_object* v_x_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_474_, v_a_475_, v_x_476_);
lean_dec(v_x_476_);
lean_dec_ref(v_a_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object* v_00_u03b2_479_, lean_object* v_data_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_480_);
return v___x_481_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(lean_object* v_xs_482_, lean_object* v_ys_483_, lean_object* v_hsz_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_482_, v_ys_483_, v_x_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_488_, lean_object* v_ys_489_, lean_object* v_hsz_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_488_, v_ys_489_, v_hsz_490_, v_x_491_, v_x_492_);
lean_dec_ref(v_ys_489_);
lean_dec_ref(v_xs_488_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_495_, lean_object* v_i_496_, lean_object* v_source_497_, lean_object* v_target_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_496_, v_source_497_, v_target_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_501_, v_x_502_);
return v___x_503_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object* v_snd_504_, lean_object* v_x_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = l_Lean_NameSet_contains(v_snd_504_, v_x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = 1;
return v___x_507_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = 0;
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object* v_snd_509_, lean_object* v_x_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_509_, v_x_510_);
lean_dec(v_x_510_);
lean_dec(v_snd_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
if (lean_obj_tag(v_a_513_) == 0)
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v_a_514_);
return v___x_515_;
}
else
{
lean_object* v_key_516_; lean_object* v_tail_517_; lean_object* v_fst_518_; lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_540_; 
v_key_516_ = lean_ctor_get(v_a_513_, 0);
lean_inc(v_key_516_);
v_tail_517_ = lean_ctor_get(v_a_513_, 2);
lean_inc(v_tail_517_);
lean_dec_ref_known(v_a_513_, 3);
v_fst_518_ = lean_ctor_get(v_key_516_, 0);
lean_inc(v_fst_518_);
lean_dec(v_key_516_);
v_fst_519_ = lean_ctor_get(v_a_514_, 0);
v_snd_520_ = lean_ctor_get(v_a_514_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_a_514_);
if (v_isSharedCheck_540_ == 0)
{
v___x_522_ = v_a_514_;
v_isShared_523_ = v_isSharedCheck_540_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_inc(v_fst_519_);
lean_dec(v_a_514_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_540_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_NameSet_contains(v_snd_520_, v_fst_518_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_NameSet_contains(v_fst_519_, v_fst_518_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_NameSet_insert(v_fst_519_, v_fst_518_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_526_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_520_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_a_513_ = v_tail_517_;
v_a_514_ = v___x_528_;
goto _start;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = l_Lean_NameSet_insert(v_snd_520_, v_fst_518_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_531_);
v___x_533_ = v___x_522_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v_a_513_ = v_tail_517_;
v_a_514_ = v___x_533_;
goto _start;
}
}
}
else
{
lean_object* v___x_537_; 
lean_dec(v_fst_518_);
if (v_isShared_523_ == 0)
{
v___x_537_ = v___x_522_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_520_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v_a_513_ = v_tail_517_;
v_a_514_ = v___x_537_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(lean_object* v_as_541_, size_t v_sz_542_, size_t v_i_543_, lean_object* v_b_544_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_lt(v_i_543_, v_sz_542_);
if (v___x_545_ == 0)
{
return v_b_544_;
}
else
{
lean_object* v_a_546_; lean_object* v___x_547_; 
v_a_546_ = lean_array_uget_borrowed(v_as_541_, v_i_543_);
lean_inc(v_a_546_);
v___x_547_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_546_, v_b_544_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
return v_a_548_;
}
else
{
lean_object* v_a_549_; size_t v___x_550_; size_t v___x_551_; 
v_a_549_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_547_, 1);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_543_, v___x_550_);
v_i_543_ = v___x_551_;
v_b_544_ = v_a_549_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(lean_object* v_as_553_, lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_b_556_){
_start:
{
size_t v_sz_boxed_557_; size_t v_i_boxed_558_; lean_object* v_res_559_; 
v_sz_boxed_557_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_553_, v_sz_boxed_557_, v_i_boxed_558_, v_b_556_);
lean_dec_ref(v_as_553_);
return v_res_559_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0(void){
_start:
{
lean_object* v_seen_560_; lean_object* v___x_561_; 
v_seen_560_ = l_Lean_NameSet_empty;
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_seen_560_);
lean_ctor_set(v___x_561_, 1, v_seen_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object* v_calls_562_){
_start:
{
lean_object* v_seen_563_; lean_object* v___x_564_; lean_object* v_buckets_565_; size_t v_sz_566_; size_t v___x_567_; lean_object* v___x_568_; lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
v_seen_563_ = lean_ctor_get(v_calls_562_, 1);
v___x_564_ = lean_obj_once(&l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0, &l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once, _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0);
v_buckets_565_ = lean_ctor_get(v_seen_563_, 1);
v_sz_566_ = lean_array_size(v_buckets_565_);
v___x_567_ = ((size_t)0ULL);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_565_, v_sz_566_, v___x_567_, v___x_564_);
v_fst_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_fst_569_);
v_snd_570_ = lean_ctor_get(v___x_568_, 1);
lean_inc(v_snd_570_);
lean_dec_ref(v___x_568_);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed), 2, 1);
lean_closure_set(v___f_571_, 0, v_snd_570_);
v___x_572_ = l_Lean_NameSet_filter(v___f_571_, v_fst_569_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object* v_calls_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_573_);
lean_dec_ref(v_calls_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object* v_e_575_, lean_object* v_funIndInfo_576_, lean_object* v_args_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_st_ref_get(v_a_578_);
v___x_585_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_575_, v_funIndInfo_576_, v_args_577_, v___x_584_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_595_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_595_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = lean_st_ref_swap(v_a_578_, v_a_586_);
lean_dec(v___x_590_);
v___x_591_ = lean_box(0);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_591_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_a_596_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_585_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_585_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object* v_e_604_, lean_object* v_funIndInfo_605_, lean_object* v_args_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_604_, v_funIndInfo_605_, v_args_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_args_606_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object* v_e_614_, lean_object* v_funIndInfo_615_, lean_object* v_args_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_614_, v_funIndInfo_615_, v_args_616_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object* v_e_625_, lean_object* v_funIndInfo_626_, lean_object* v_args_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_625_, v_funIndInfo_626_, v_args_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec_ref(v_args_627_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object* v_e_636_, lean_object* v_funIndInfo_637_, lean_object* v_args_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_636_, v_funIndInfo_637_, v_args_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object* v_e_646_, lean_object* v_funIndInfo_647_, lean_object* v_args_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_646_, v_funIndInfo_647_, v_args_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_args_648_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object* v_e_656_, lean_object* v_funIndInfo_657_, lean_object* v_args_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_656_, v_funIndInfo_657_, v_args_658_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object* v_e_667_, lean_object* v_funIndInfo_668_, lean_object* v_args_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_667_, v_funIndInfo_668_, v_args_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v_args_669_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
return v_x_678_;
}
else
{
lean_object* v_key_680_; lean_object* v_value_681_; lean_object* v_tail_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_708_; 
v_key_680_ = lean_ctor_get(v_x_679_, 0);
v_value_681_ = lean_ctor_get(v_x_679_, 1);
v_tail_682_ = lean_ctor_get(v_x_679_, 2);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_708_ == 0)
{
v___x_684_ = v_x_679_;
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_tail_682_);
lean_inc(v_value_681_);
lean_inc(v_key_680_);
lean_dec(v_x_679_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; size_t v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; uint64_t v___x_691_; uint64_t v___x_692_; uint64_t v_fold_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_686_ = lean_array_get_size(v_x_678_);
v___x_687_ = lean_ptr_addr(v_key_680_);
v___x_688_ = lean_usize_to_uint64(v___x_687_);
v___x_689_ = 11ULL;
v___x_690_ = lean_uint64_mix_hash(v___x_688_, v___x_689_);
v___x_691_ = 32ULL;
v___x_692_ = lean_uint64_shift_right(v___x_690_, v___x_691_);
v_fold_693_ = lean_uint64_xor(v___x_690_, v___x_692_);
v___x_694_ = 16ULL;
v___x_695_ = lean_uint64_shift_right(v_fold_693_, v___x_694_);
v___x_696_ = lean_uint64_xor(v_fold_693_, v___x_695_);
v___x_697_ = lean_uint64_to_usize(v___x_696_);
v___x_698_ = lean_usize_of_nat(v___x_686_);
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_sub(v___x_698_, v___x_699_);
v___x_701_ = lean_usize_land(v___x_697_, v___x_700_);
v___x_702_ = lean_array_uget_borrowed(v_x_678_, v___x_701_);
lean_inc(v___x_702_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 2, v___x_702_);
v___x_704_ = v___x_684_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_key_680_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_value_681_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v___x_702_);
v___x_704_ = v_reuseFailAlloc_707_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; 
v___x_705_ = lean_array_uset(v_x_678_, v___x_701_, v___x_704_);
v_x_678_ = v___x_705_;
v_x_679_ = v_tail_682_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(lean_object* v_i_709_, lean_object* v_source_710_, lean_object* v_target_711_){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_source_710_);
v___x_713_ = lean_nat_dec_lt(v_i_709_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec_ref(v_source_710_);
lean_dec(v_i_709_);
return v_target_711_;
}
else
{
lean_object* v_es_714_; lean_object* v___x_715_; lean_object* v_source_716_; lean_object* v_target_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_es_714_ = lean_array_fget(v_source_710_, v_i_709_);
v___x_715_ = lean_box(0);
v_source_716_ = lean_array_fset(v_source_710_, v_i_709_, v___x_715_);
v_target_717_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_711_, v_es_714_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_i_709_, v___x_718_);
lean_dec(v_i_709_);
v_i_709_ = v___x_719_;
v_source_710_ = v_source_716_;
v_target_711_ = v_target_717_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(lean_object* v_data_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_nbuckets_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_722_ = lean_array_get_size(v_data_721_);
v___x_723_ = lean_unsigned_to_nat(2u);
v_nbuckets_724_ = lean_nat_mul(v___x_722_, v___x_723_);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_box(0);
v___x_727_ = lean_mk_array(v_nbuckets_724_, v___x_726_);
v___x_728_ = lean_array_propagate_mark(v_data_721_, v___x_727_);
v___x_729_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_725_, v_data_721_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_a_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_731_) == 0)
{
uint8_t v___x_732_; 
v___x_732_ = 0;
return v___x_732_;
}
else
{
lean_object* v_key_733_; lean_object* v_tail_734_; size_t v___x_735_; size_t v___x_736_; uint8_t v___x_737_; 
v_key_733_ = lean_ctor_get(v_x_731_, 0);
v_tail_734_ = lean_ctor_get(v_x_731_, 2);
v___x_735_ = lean_ptr_addr(v_key_733_);
v___x_736_ = lean_ptr_addr(v_a_730_);
v___x_737_ = lean_usize_dec_eq(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
v_x_731_ = v_tail_734_;
goto _start;
}
else
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_739_, lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_739_, v_x_740_);
lean_dec(v_x_740_);
lean_dec_ref(v_a_739_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(lean_object* v_m_743_, lean_object* v_a_744_, lean_object* v_b_745_){
_start:
{
lean_object* v_size_746_; lean_object* v_buckets_747_; lean_object* v___x_748_; size_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v_fold_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v_bkt_764_; uint8_t v___x_765_; 
v_size_746_ = lean_ctor_get(v_m_743_, 0);
v_buckets_747_ = lean_ctor_get(v_m_743_, 1);
v___x_748_ = lean_array_get_size(v_buckets_747_);
v___x_749_ = lean_ptr_addr(v_a_744_);
v___x_750_ = lean_usize_to_uint64(v___x_749_);
v___x_751_ = 11ULL;
v___x_752_ = lean_uint64_mix_hash(v___x_750_, v___x_751_);
v___x_753_ = 32ULL;
v___x_754_ = lean_uint64_shift_right(v___x_752_, v___x_753_);
v_fold_755_ = lean_uint64_xor(v___x_752_, v___x_754_);
v___x_756_ = 16ULL;
v___x_757_ = lean_uint64_shift_right(v_fold_755_, v___x_756_);
v___x_758_ = lean_uint64_xor(v_fold_755_, v___x_757_);
v___x_759_ = lean_uint64_to_usize(v___x_758_);
v___x_760_ = lean_usize_of_nat(v___x_748_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_sub(v___x_760_, v___x_761_);
v___x_763_ = lean_usize_land(v___x_759_, v___x_762_);
v_bkt_764_ = lean_array_uget_borrowed(v_buckets_747_, v___x_763_);
v___x_765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_744_, v_bkt_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_786_; 
lean_inc_ref(v_buckets_747_);
lean_inc(v_size_746_);
v_isSharedCheck_786_ = !lean_is_exclusive(v_m_743_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; lean_object* v_unused_788_; 
v_unused_787_ = lean_ctor_get(v_m_743_, 1);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_m_743_, 0);
lean_dec(v_unused_788_);
v___x_767_ = v_m_743_;
v_isShared_768_ = v_isSharedCheck_786_;
goto v_resetjp_766_;
}
else
{
lean_dec(v_m_743_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_786_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v_size_x27_770_; lean_object* v___x_771_; lean_object* v_buckets_x27_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_769_ = lean_unsigned_to_nat(1u);
v_size_x27_770_ = lean_nat_add(v_size_746_, v___x_769_);
lean_dec(v_size_746_);
lean_inc(v_bkt_764_);
v___x_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_771_, 0, v_a_744_);
lean_ctor_set(v___x_771_, 1, v_b_745_);
lean_ctor_set(v___x_771_, 2, v_bkt_764_);
v_buckets_x27_772_ = lean_array_uset(v_buckets_747_, v___x_763_, v___x_771_);
v___x_773_ = lean_unsigned_to_nat(4u);
v___x_774_ = lean_nat_mul(v_size_x27_770_, v___x_773_);
v___x_775_ = lean_unsigned_to_nat(3u);
v___x_776_ = lean_nat_div(v___x_774_, v___x_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_array_get_size(v_buckets_x27_772_);
v___x_778_ = lean_nat_dec_le(v___x_776_, v___x_777_);
lean_dec(v___x_776_);
if (v___x_778_ == 0)
{
lean_object* v_val_779_; lean_object* v___x_781_; 
v_val_779_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_772_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_val_779_);
lean_ctor_set(v___x_767_, 0, v_size_x27_770_);
v___x_781_ = v___x_767_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_size_x27_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_val_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v___x_784_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_buckets_x27_772_);
lean_ctor_set(v___x_767_, 0, v_size_x27_770_);
v___x_784_ = v___x_767_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_size_x27_770_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_buckets_x27_772_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_dec(v_b_745_);
lean_dec_ref(v_a_744_);
return v_m_743_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_buckets_791_; lean_object* v___x_792_; size_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v___x_797_; uint64_t v___x_798_; uint64_t v_fold_799_; uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_buckets_791_ = lean_ctor_get(v_m_789_, 1);
v___x_792_ = lean_array_get_size(v_buckets_791_);
v___x_793_ = lean_ptr_addr(v_a_790_);
v___x_794_ = lean_usize_to_uint64(v___x_793_);
v___x_795_ = 11ULL;
v___x_796_ = lean_uint64_mix_hash(v___x_794_, v___x_795_);
v___x_797_ = 32ULL;
v___x_798_ = lean_uint64_shift_right(v___x_796_, v___x_797_);
v_fold_799_ = lean_uint64_xor(v___x_796_, v___x_798_);
v___x_800_ = 16ULL;
v___x_801_ = lean_uint64_shift_right(v_fold_799_, v___x_800_);
v___x_802_ = lean_uint64_xor(v_fold_799_, v___x_801_);
v___x_803_ = lean_uint64_to_usize(v___x_802_);
v___x_804_ = lean_usize_of_nat(v___x_792_);
v___x_805_ = ((size_t)1ULL);
v___x_806_ = lean_usize_sub(v___x_804_, v___x_805_);
v___x_807_ = lean_usize_land(v___x_803_, v___x_806_);
v___x_808_ = lean_array_uget_borrowed(v_buckets_791_, v___x_807_);
v___x_809_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_790_, v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_810_, lean_object* v_a_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_810_, v_a_811_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_m_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_814_; lean_object* v_dummy_815_; 
v___x_814_ = lean_box(0);
v_dummy_815_ = l_Lean_Expr_sort___override(v___x_814_);
return v_dummy_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_e_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; 
if (lean_obj_tag(v_x_817_) == 5)
{
lean_object* v_fn_849_; lean_object* v_arg_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_fn_849_ = lean_ctor_get(v_x_817_, 0);
lean_inc_ref(v_fn_849_);
v_arg_850_ = lean_ctor_get(v_x_817_, 1);
lean_inc_ref(v_arg_850_);
lean_dec_ref_known(v_x_817_, 2);
v___x_851_ = lean_array_set(v_x_818_, v_x_819_, v_arg_850_);
v___x_852_ = lean_unsigned_to_nat(1u);
v___x_853_ = lean_nat_sub(v_x_819_, v___x_852_);
lean_dec(v_x_819_);
v_x_817_ = v_fn_849_;
v_x_818_ = v___x_851_;
v_x_819_ = v___x_853_;
goto _start;
}
else
{
lean_dec(v_x_819_);
if (lean_obj_tag(v_x_817_) == 4)
{
lean_object* v_declName_855_; lean_object* v_funName_856_; uint8_t v___x_857_; 
v_declName_855_ = lean_ctor_get(v_x_817_, 0);
lean_inc(v_declName_855_);
lean_dec_ref_known(v_x_817_, 2);
v_funName_856_ = lean_ctor_get(v___y_821_, 0);
v___x_857_ = lean_name_eq(v_declName_855_, v_funName_856_);
lean_dec(v_declName_855_);
if (v___x_857_ == 0)
{
lean_dec_ref(v_e_816_);
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
v___y_835_ = v___y_826_;
goto v___jp_828_;
}
else
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_Expr_hasLooseBVars(v_e_816_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
lean_inc_ref(v___y_821_);
v___x_859_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_816_, v___y_821_, v_x_818_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_dec_ref_known(v___x_859_, 1);
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
v___y_835_ = v___y_826_;
goto v___jp_828_;
}
else
{
lean_dec_ref(v_x_818_);
return v___x_859_;
}
}
else
{
lean_dec_ref(v_e_816_);
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
v___y_835_ = v___y_826_;
goto v___jp_828_;
}
}
}
else
{
lean_object* v___x_860_; 
lean_dec_ref(v_e_816_);
v___x_860_ = l_Lean_Meta_FunInd_Collector_visit(v_x_817_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_dec_ref_known(v___x_860_, 1);
v___y_829_ = v___y_820_;
v___y_830_ = v___y_821_;
v___y_831_ = v___y_822_;
v___y_832_ = v___y_823_;
v___y_833_ = v___y_824_;
v___y_834_ = v___y_825_;
v___y_835_ = v___y_826_;
goto v___jp_828_;
}
else
{
lean_dec_ref(v_x_818_);
return v___x_860_;
}
}
}
v___jp_828_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_array_get_size(v_x_818_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_nat_dec_lt(v___x_836_, v___x_837_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_dec_ref(v_x_818_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
return v___x_840_;
}
else
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_le(v___x_837_, v___x_837_);
if (v___x_841_ == 0)
{
if (v___x_839_ == 0)
{
lean_object* v___x_842_; 
lean_dec_ref(v_x_818_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_838_);
return v___x_842_;
}
else
{
size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((size_t)0ULL);
v___x_844_ = lean_usize_of_nat(v___x_837_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_818_, v___x_843_, v___x_844_, v___x_838_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec_ref(v_x_818_);
return v___x_845_;
}
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((size_t)0ULL);
v___x_847_ = lean_usize_of_nat(v___x_837_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_818_, v___x_846_, v___x_847_, v___x_838_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec_ref(v_x_818_);
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_st_ref_get(v_a_862_);
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_870_, v_e_861_);
lean_dec(v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_d_877_; lean_object* v_b_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; 
v___x_872_ = lean_st_ref_take(v_a_862_);
v___x_873_ = lean_box(0);
lean_inc_ref(v_e_861_);
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_872_, v_e_861_, v___x_873_);
v___x_875_ = lean_st_ref_put(v_a_862_, v___x_874_);
switch(lean_obj_tag(v_e_861_))
{
case 4:
{
lean_object* v___x_888_; 
lean_dec_ref_known(v_e_861_, 2);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_873_);
return v___x_888_;
}
case 7:
{
lean_object* v_binderType_889_; lean_object* v_body_890_; 
v_binderType_889_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_binderType_889_);
v_body_890_ = lean_ctor_get(v_e_861_, 2);
lean_inc_ref(v_body_890_);
lean_dec_ref_known(v_e_861_, 3);
v_d_877_ = v_binderType_889_;
v_b_878_ = v_body_890_;
v___y_879_ = v_a_862_;
v___y_880_ = v_a_863_;
v___y_881_ = v_a_864_;
v___y_882_ = v_a_865_;
v___y_883_ = v_a_866_;
v___y_884_ = v_a_867_;
v___y_885_ = v_a_868_;
goto v___jp_876_;
}
case 6:
{
lean_object* v_binderType_891_; lean_object* v_body_892_; 
v_binderType_891_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_binderType_891_);
v_body_892_ = lean_ctor_get(v_e_861_, 2);
lean_inc_ref(v_body_892_);
lean_dec_ref_known(v_e_861_, 3);
v_d_877_ = v_binderType_891_;
v_b_878_ = v_body_892_;
v___y_879_ = v_a_862_;
v___y_880_ = v_a_863_;
v___y_881_ = v_a_864_;
v___y_882_ = v_a_865_;
v___y_883_ = v_a_866_;
v___y_884_ = v_a_867_;
v___y_885_ = v_a_868_;
goto v___jp_876_;
}
case 10:
{
lean_object* v_expr_893_; 
v_expr_893_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_expr_893_);
lean_dec_ref_known(v_e_861_, 2);
v_e_861_ = v_expr_893_;
goto _start;
}
case 8:
{
lean_object* v_type_895_; lean_object* v_value_896_; lean_object* v_body_897_; lean_object* v___x_898_; 
v_type_895_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_type_895_);
v_value_896_ = lean_ctor_get(v_e_861_, 2);
lean_inc_ref(v_value_896_);
v_body_897_ = lean_ctor_get(v_e_861_, 3);
lean_inc_ref(v_body_897_);
lean_dec_ref_known(v_e_861_, 4);
v___x_898_ = l_Lean_Meta_FunInd_Collector_visit(v_type_895_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_899_; 
lean_dec_ref_known(v___x_898_, 1);
v___x_899_ = l_Lean_Meta_FunInd_Collector_visit(v_value_896_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_dec_ref_known(v___x_899_, 1);
v_e_861_ = v_body_897_;
goto _start;
}
else
{
lean_dec_ref(v_body_897_);
return v___x_899_;
}
}
else
{
lean_dec_ref(v_body_897_);
lean_dec_ref(v_value_896_);
return v___x_898_;
}
}
case 5:
{
lean_object* v_dummy_901_; lean_object* v_nargs_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_dummy_901_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_902_ = l_Lean_Expr_getAppNumArgs(v_e_861_);
lean_inc(v_nargs_902_);
v___x_903_ = lean_mk_array(v_nargs_902_, v_dummy_901_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_sub(v_nargs_902_, v___x_904_);
lean_dec(v_nargs_902_);
lean_inc_ref(v_e_861_);
v___x_906_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_861_, v_e_861_, v___x_903_, v___x_905_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_906_;
}
case 11:
{
lean_object* v_struct_907_; 
v_struct_907_ = lean_ctor_get(v_e_861_, 2);
lean_inc_ref(v_struct_907_);
lean_dec_ref_known(v_e_861_, 3);
v_e_861_ = v_struct_907_;
goto _start;
}
default: 
{
lean_object* v___x_909_; 
lean_dec_ref(v_e_861_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_873_);
return v___x_909_;
}
}
v___jp_876_:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_FunInd_Collector_visit(v_d_877_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_dec_ref_known(v___x_886_, 1);
v_e_861_ = v_b_878_;
v_a_862_ = v___y_879_;
v_a_863_ = v___y_880_;
v_a_864_ = v___y_881_;
v_a_865_ = v___y_882_;
v_a_866_ = v___y_883_;
v_a_867_ = v___y_884_;
v_a_868_ = v___y_885_;
goto _start;
}
else
{
lean_dec_ref(v_b_878_);
return v___x_886_;
}
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref(v_e_861_);
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_912_, size_t v_i_913_, size_t v_stop_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v___x_924_; 
v___x_924_ = lean_usize_dec_eq(v_i_913_, v_stop_914_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_array_uget_borrowed(v_as_912_, v_i_913_);
lean_inc(v___x_925_);
v___x_926_ = l_Lean_Meta_FunInd_Collector_visit(v___x_925_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; size_t v___x_928_; size_t v___x_929_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_913_, v___x_928_);
v_i_913_ = v___x_929_;
v_b_915_ = v_a_927_;
goto _start;
}
else
{
return v___x_926_;
}
}
else
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_b_915_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_932_, lean_object* v_i_933_, lean_object* v_stop_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
size_t v_i_boxed_944_; size_t v_stop_boxed_945_; lean_object* v_res_946_; 
v_i_boxed_944_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_stop_boxed_945_ = lean_unbox_usize(v_stop_934_);
lean_dec(v_stop_934_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_932_, v_i_boxed_944_, v_stop_boxed_945_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v_as_932_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_FunInd_Collector_visit(v_e_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_e_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_957_, v_x_958_, v_x_959_, v_x_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
return v_res_969_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_970_, lean_object* v_m_971_, lean_object* v_a_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_971_, v_a_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_974_, lean_object* v_m_975_, lean_object* v_a_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_974_, v_m_975_, v_a_976_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_m_975_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_00_u03b2_979_, lean_object* v_m_980_, lean_object* v_a_981_, lean_object* v_b_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_980_, v_a_981_, v_b_982_);
return v___x_983_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_984_, lean_object* v_a_985_, lean_object* v_x_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_985_, v_x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_988_, lean_object* v_a_989_, lean_object* v_x_990_){
_start:
{
uint8_t v_res_991_; lean_object* v_r_992_; 
v_res_991_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_988_, v_a_989_, v_x_990_);
lean_dec(v_x_990_);
lean_dec_ref(v_a_989_);
v_r_992_ = lean_box(v_res_991_);
return v_r_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object* v_00_u03b2_993_, lean_object* v_data_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_996_, lean_object* v_i_997_, lean_object* v_source_998_, lean_object* v_target_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_997_, v_source_998_, v_target_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = l_Lean_Expr_hasMVar(v_e_1005_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_e_1005_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; lean_object* v_mctx_1011_; lean_object* v___x_1012_; lean_object* v_fst_1013_; lean_object* v_snd_1014_; lean_object* v___x_1015_; lean_object* v_cache_1016_; lean_object* v_zetaDeltaFVarIds_1017_; lean_object* v_postponed_1018_; lean_object* v_diag_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1028_; 
v___x_1010_ = lean_st_ref_get(v___y_1006_);
v_mctx_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc_ref(v_mctx_1011_);
lean_dec(v___x_1010_);
v___x_1012_ = l_Lean_instantiateMVarsCore(v_mctx_1011_, v_e_1005_);
v_fst_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_fst_1013_);
v_snd_1014_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_snd_1014_);
lean_dec_ref(v___x_1012_);
v___x_1015_ = lean_st_ref_take(v___y_1006_);
v_cache_1016_ = lean_ctor_get(v___x_1015_, 1);
v_zetaDeltaFVarIds_1017_ = lean_ctor_get(v___x_1015_, 2);
v_postponed_1018_ = lean_ctor_get(v___x_1015_, 3);
v_diag_1019_ = lean_ctor_get(v___x_1015_, 4);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v___x_1015_, 0);
lean_dec(v_unused_1029_);
v___x_1021_ = v___x_1015_;
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_diag_1019_);
lean_inc(v_postponed_1018_);
lean_inc(v_zetaDeltaFVarIds_1017_);
lean_inc(v_cache_1016_);
lean_dec(v___x_1015_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_snd_1014_);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_snd_1014_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_cache_1016_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_zetaDeltaFVarIds_1017_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_postponed_1018_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_diag_1019_);
v___x_1024_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_st_ref_put(v___y_1006_, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_fst_1013_);
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1030_, v___y_1031_);
lean_dec(v___y_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1034_, v___y_1039_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1054_, size_t v_sz_1055_, size_t v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_usize_dec_lt(v_i_1056_, v_sz_1055_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_b_1057_);
return v___x_1067_;
}
else
{
lean_object* v_snd_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1126_; 
v_snd_1068_ = lean_ctor_get(v_b_1057_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_b_1057_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_b_1057_, 0);
lean_dec(v_unused_1127_);
v___x_1070_ = v_b_1057_;
v_isShared_1071_ = v_isSharedCheck_1126_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snd_1068_);
lean_dec(v_b_1057_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1126_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v_a_1074_; lean_object* v_a_1081_; 
v___x_1072_ = lean_box(0);
v_a_1081_ = lean_array_uget_borrowed(v_as_1054_, v_i_1056_);
if (lean_obj_tag(v_a_1081_) == 0)
{
v_a_1074_ = v_snd_1068_;
goto v___jp_1073_;
}
else
{
lean_object* v_val_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
lean_dec(v_snd_1068_);
v_val_1082_ = lean_ctor_get(v_a_1081_, 0);
v___x_1083_ = lean_box(0);
v___x_1084_ = l_Lean_LocalDecl_isAuxDecl(v_val_1082_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_LocalDecl_value_x3f(v_val_1082_, v___x_1084_);
if (lean_obj_tag(v___x_1085_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; 
v_val_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1086_, v___y_1062_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1088_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_dec_ref_known(v___x_1089_, 1);
v_a_1074_ = v___x_1083_;
goto v___jp_1073_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_del_object(v___x_1070_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_del_object(v___x_1070_);
v_a_1098_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1087_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1087_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v___x_1085_);
v___x_1106_ = l_Lean_LocalDecl_type(v_val_1082_);
v___x_1107_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1106_, v___y_1062_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1109_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___x_1109_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1108_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_dec_ref_known(v___x_1109_, 1);
v_a_1074_ = v___x_1083_;
goto v___jp_1073_;
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_del_object(v___x_1070_);
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
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
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_del_object(v___x_1070_);
v_a_1118_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1107_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1107_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
else
{
v_a_1074_ = v___x_1083_;
goto v___jp_1073_;
}
}
v___jp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v_a_1074_);
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1076_ = v___x_1070_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_a_1074_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
size_t v___x_1077_; size_t v___x_1078_; 
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_add(v_i_1056_, v___x_1077_);
v_i_1056_ = v___x_1078_;
v_b_1057_ = v___x_1076_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1128_, lean_object* v_sz_1129_, lean_object* v_i_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
size_t v_sz_boxed_1140_; size_t v_i_boxed_1141_; lean_object* v_res_1142_; 
v_sz_boxed_1140_ = lean_unbox_usize(v_sz_1129_);
lean_dec(v_sz_1129_);
v_i_boxed_1141_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_res_1142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1128_, v_sz_boxed_1140_, v_i_boxed_1141_, v_b_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v_as_1128_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1143_, size_t v_sz_1144_, size_t v_i_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1145_, v_sz_1144_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_b_1146_);
return v___x_1156_;
}
else
{
lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1215_; 
v_snd_1157_ = lean_ctor_get(v_b_1146_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_b_1146_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_b_1146_, 0);
lean_dec(v_unused_1216_);
v___x_1159_ = v_b_1146_;
v_isShared_1160_ = v_isSharedCheck_1215_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_dec(v_b_1146_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1215_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_a_1163_; lean_object* v_a_1170_; 
v___x_1161_ = lean_box(0);
v_a_1170_ = lean_array_uget_borrowed(v_as_1143_, v_i_1145_);
if (lean_obj_tag(v_a_1170_) == 0)
{
v_a_1163_ = v_snd_1157_;
goto v___jp_1162_;
}
else
{
lean_object* v_val_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
lean_dec(v_snd_1157_);
v_val_1171_ = lean_ctor_get(v_a_1170_, 0);
v___x_1172_ = lean_box(0);
v___x_1173_ = l_Lean_LocalDecl_isAuxDecl(v_val_1171_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_LocalDecl_value_x3f(v_val_1171_, v___x_1173_);
if (lean_obj_tag(v___x_1174_) == 1)
{
lean_object* v_val_1175_; lean_object* v___x_1176_; 
v_val_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1175_, v___y_1151_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1177_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_dec_ref_known(v___x_1178_, 1);
v_a_1163_ = v___x_1172_;
goto v___jp_1162_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_del_object(v___x_1159_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_del_object(v___x_1159_);
v_a_1187_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1176_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1176_);
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
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v___x_1174_);
v___x_1195_ = l_Lean_LocalDecl_type(v_val_1171_);
v___x_1196_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1195_, v___y_1151_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1197_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_dec_ref_known(v___x_1198_, 1);
v_a_1163_ = v___x_1172_;
goto v___jp_1162_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_del_object(v___x_1159_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_del_object(v___x_1159_);
v_a_1207_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1196_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1196_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
else
{
v_a_1163_ = v___x_1172_;
goto v___jp_1162_;
}
}
v___jp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_a_1163_);
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1165_ = v___x_1159_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1163_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_add(v_i_1145_, v___x_1166_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1143_, v_sz_1144_, v___x_1167_, v___x_1165_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1217_, lean_object* v_sz_1218_, lean_object* v_i_1219_, lean_object* v_b_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
size_t v_sz_boxed_1229_; size_t v_i_boxed_1230_; lean_object* v_res_1231_; 
v_sz_boxed_1229_ = lean_unbox_usize(v_sz_1218_);
lean_dec(v_sz_1218_);
v_i_boxed_1230_ = lean_unbox_usize(v_i_1219_);
lean_dec(v_i_1219_);
v_res_1231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1217_, v_sz_boxed_1229_, v_i_boxed_1230_, v_b_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v_as_1217_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1232_, size_t v_sz_1233_, size_t v_i_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_usize_dec_lt(v_i_1234_, v_sz_1233_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_b_1235_);
return v___x_1245_;
}
else
{
lean_object* v_snd_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1304_; 
v_snd_1246_ = lean_ctor_get(v_b_1235_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_b_1235_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; 
v_unused_1305_ = lean_ctor_get(v_b_1235_, 0);
lean_dec(v_unused_1305_);
v___x_1248_ = v_b_1235_;
v_isShared_1249_ = v_isSharedCheck_1304_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_snd_1246_);
lean_dec(v_b_1235_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1304_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v_a_1252_; lean_object* v_a_1259_; 
v___x_1250_ = lean_box(0);
v_a_1259_ = lean_array_uget_borrowed(v_as_1232_, v_i_1234_);
if (lean_obj_tag(v_a_1259_) == 0)
{
v_a_1252_ = v_snd_1246_;
goto v___jp_1251_;
}
else
{
lean_object* v_val_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
lean_dec(v_snd_1246_);
v_val_1260_ = lean_ctor_get(v_a_1259_, 0);
v___x_1261_ = lean_box(0);
v___x_1262_ = l_Lean_LocalDecl_isAuxDecl(v_val_1260_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_LocalDecl_value_x3f(v_val_1260_, v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 1)
{
lean_object* v_val_1264_; lean_object* v___x_1265_; 
v_val_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1264_, v___y_1240_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1266_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_dec_ref_known(v___x_1267_, 1);
v_a_1252_ = v___x_1261_;
goto v___jp_1251_;
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_del_object(v___x_1248_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_del_object(v___x_1248_);
v_a_1276_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1265_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1265_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v___x_1263_);
v___x_1284_ = l_Lean_LocalDecl_type(v_val_1260_);
v___x_1285_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1284_, v___y_1240_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1286_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_dec_ref_known(v___x_1287_, 1);
v_a_1252_ = v___x_1261_;
goto v___jp_1251_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_del_object(v___x_1248_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_del_object(v___x_1248_);
v_a_1296_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1285_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1285_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
v_a_1252_ = v___x_1261_;
goto v___jp_1251_;
}
}
v___jp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_a_1252_);
lean_ctor_set(v___x_1248_, 0, v___x_1250_);
v___x_1254_ = v___x_1248_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_a_1252_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
size_t v___x_1255_; size_t v___x_1256_; 
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1234_, v___x_1255_);
v_i_1234_ = v___x_1256_;
v_b_1235_ = v___x_1254_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1306_, lean_object* v_sz_1307_, lean_object* v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
size_t v_sz_boxed_1318_; size_t v_i_boxed_1319_; lean_object* v_res_1320_; 
v_sz_boxed_1318_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v_i_boxed_1319_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1306_, v_sz_boxed_1318_, v_i_boxed_1319_, v_b_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v_as_1306_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1321_, size_t v_sz_1322_, size_t v_i_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_b_1324_);
return v___x_1334_;
}
else
{
lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1393_; 
v_snd_1335_ = lean_ctor_get(v_b_1324_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_b_1324_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v_b_1324_, 0);
lean_dec(v_unused_1394_);
v___x_1337_ = v_b_1324_;
v_isShared_1338_ = v_isSharedCheck_1393_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_dec(v_b_1324_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1393_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v_a_1341_; lean_object* v_a_1348_; 
v___x_1339_ = lean_box(0);
v_a_1348_ = lean_array_uget_borrowed(v_as_1321_, v_i_1323_);
if (lean_obj_tag(v_a_1348_) == 0)
{
v_a_1341_ = v_snd_1335_;
goto v___jp_1340_;
}
else
{
lean_object* v_val_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
lean_dec(v_snd_1335_);
v_val_1349_ = lean_ctor_get(v_a_1348_, 0);
v___x_1350_ = lean_box(0);
v___x_1351_ = l_Lean_LocalDecl_isAuxDecl(v_val_1349_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_LocalDecl_value_x3f(v_val_1349_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v___x_1354_; 
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1353_, v___y_1329_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1355_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref_known(v___x_1356_, 1);
v_a_1341_ = v___x_1350_;
goto v___jp_1340_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_del_object(v___x_1337_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_del_object(v___x_1337_);
v_a_1365_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1354_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1354_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec(v___x_1352_);
v___x_1373_ = l_Lean_LocalDecl_type(v_val_1349_);
v___x_1374_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1373_, v___y_1329_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1375_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_dec_ref_known(v___x_1376_, 1);
v_a_1341_ = v___x_1350_;
goto v___jp_1340_;
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_del_object(v___x_1337_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_del_object(v___x_1337_);
v_a_1385_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1374_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1374_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
else
{
v_a_1341_ = v___x_1350_;
goto v___jp_1340_;
}
}
v___jp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v_a_1341_);
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_a_1341_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_add(v_i_1323_, v___x_1344_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1321_, v_sz_1322_, v___x_1345_, v___x_1343_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1395_, lean_object* v_sz_1396_, lean_object* v_i_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
size_t v_sz_boxed_1407_; size_t v_i_boxed_1408_; lean_object* v_res_1409_; 
v_sz_boxed_1407_ = lean_unbox_usize(v_sz_1396_);
lean_dec(v_sz_1396_);
v_i_boxed_1408_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1395_, v_sz_boxed_1407_, v_i_boxed_1408_, v_b_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v_as_1395_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_init_1410_, lean_object* v_n_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
if (lean_obj_tag(v_n_1411_) == 0)
{
lean_object* v_cs_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; size_t v_sz_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v_cs_1421_ = lean_ctor_get(v_n_1411_, 0);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v_b_1412_);
v_sz_1424_ = lean_array_size(v_cs_1421_);
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1410_, v_cs_1421_, v_sz_1424_, v___x_1425_, v___x_1423_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1441_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_fst_1431_; 
v_fst_1431_ = lean_ctor_get(v_a_1427_, 0);
if (lean_obj_tag(v_fst_1431_) == 0)
{
lean_object* v_snd_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v_snd_1432_ = lean_ctor_get(v_a_1427_, 1);
lean_inc(v_snd_1432_);
lean_dec(v_a_1427_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_snd_1432_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1433_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
else
{
lean_object* v_val_1437_; lean_object* v___x_1439_; 
lean_inc_ref(v_fst_1431_);
lean_dec(v_a_1427_);
v_val_1437_ = lean_ctor_get(v_fst_1431_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v_fst_1431_, 1);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_val_1437_);
v___x_1439_ = v___x_1429_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_val_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_a_1442_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1426_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1426_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_vs_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v_vs_1450_ = lean_ctor_get(v_n_1411_, 0);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v_b_1412_);
v_sz_1453_ = lean_array_size(v_vs_1450_);
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1450_, v_sz_1453_, v___x_1454_, v___x_1452_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1470_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1470_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1470_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v_fst_1460_; 
v_fst_1460_ = lean_ctor_get(v_a_1456_, 0);
if (lean_obj_tag(v_fst_1460_) == 0)
{
lean_object* v_snd_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v_snd_1461_ = lean_ctor_get(v_a_1456_, 1);
lean_inc(v_snd_1461_);
lean_dec(v_a_1456_);
v___x_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_snd_1461_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1462_);
v___x_1464_ = v___x_1458_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1468_; 
lean_inc_ref(v_fst_1460_);
lean_dec(v_a_1456_);
v_val_1466_ = lean_ctor_get(v_fst_1460_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_fst_1460_, 1);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v_val_1466_);
v___x_1468_ = v___x_1458_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_val_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1455_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1455_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_init_1479_, lean_object* v_as_1480_, size_t v_sz_1481_, size_t v_i_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_lt(v_i_1482_, v_sz_1481_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_b_1483_);
return v___x_1493_;
}
else
{
lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1528_; 
v_snd_1494_ = lean_ctor_get(v_b_1483_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_b_1483_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v_b_1483_, 0);
lean_dec(v_unused_1529_);
v___x_1496_ = v_b_1483_;
v_isShared_1497_ = v_isSharedCheck_1528_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_dec(v_b_1483_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1528_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_array_uget_borrowed(v_as_1480_, v_i_1482_);
lean_inc(v_snd_1494_);
v___x_1499_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1479_, v_a_1498_, v_snd_1494_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1519_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1519_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1519_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
if (lean_obj_tag(v_a_1500_) == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_a_1500_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1504_);
v___x_1506_ = v___x_1496_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_snd_1494_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1506_);
v___x_1508_ = v___x_1502_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_del_object(v___x_1502_);
lean_dec(v_snd_1494_);
v_a_1511_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v_a_1500_, 1);
v___x_1512_ = lean_box(0);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v_a_1511_);
lean_ctor_set(v___x_1496_, 0, v___x_1512_);
v___x_1514_ = v___x_1496_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_a_1511_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
size_t v___x_1515_; size_t v___x_1516_; 
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_add(v_i_1482_, v___x_1515_);
v_i_1482_ = v___x_1516_;
v_b_1483_ = v___x_1514_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_del_object(v___x_1496_);
lean_dec(v_snd_1494_);
v_a_1520_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1499_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1499_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1530_, lean_object* v_as_1531_, lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_b_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1530_, v_as_1531_, v_sz_boxed_1543_, v_i_boxed_1544_, v_b_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v_as_1531_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_init_1546_, lean_object* v_n_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1546_, v_n_1547_, v_b_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v_n_1547_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1558_, lean_object* v_init_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_root_1568_; lean_object* v_tail_1569_; lean_object* v___x_1570_; 
v_root_1568_ = lean_ctor_get(v_t_1558_, 0);
v_tail_1569_ = lean_ctor_get(v_t_1558_, 1);
v___x_1570_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1559_, v_root_1568_, v_init_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1607_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1607_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1607_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
if (lean_obj_tag(v_a_1571_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; 
v_a_1575_ = lean_ctor_get(v_a_1571_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v_a_1571_, 1);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_a_1575_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; size_t v_sz_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
lean_del_object(v___x_1573_);
v_a_1579_ = lean_ctor_get(v_a_1571_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v_a_1571_, 1);
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v_a_1579_);
v_sz_1582_ = lean_array_size(v_tail_1569_);
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1569_, v_sz_1582_, v___x_1583_, v___x_1581_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1598_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1598_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1598_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_fst_1589_; 
v_fst_1589_ = lean_ctor_get(v_a_1585_, 0);
if (lean_obj_tag(v_fst_1589_) == 0)
{
lean_object* v_snd_1590_; lean_object* v___x_1592_; 
v_snd_1590_ = lean_ctor_get(v_a_1585_, 1);
lean_inc(v_snd_1590_);
lean_dec(v_a_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_snd_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_snd_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1596_; 
lean_inc_ref(v_fst_1589_);
lean_dec(v_a_1585_);
v_val_1594_ = lean_ctor_get(v_fst_1589_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_fst_1589_, 1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_val_1594_);
v___x_1596_ = v___x_1587_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_val_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1584_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1584_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_a_1608_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1570_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1570_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1616_, lean_object* v_init_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1616_, v_init_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v_t_1616_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_lctx_1636_; lean_object* v_decls_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_lctx_1636_ = lean_ctor_get(v_a_1631_, 2);
v_decls_1637_ = lean_ctor_get(v_lctx_1636_, 1);
v___x_1638_ = lean_box(0);
v___x_1639_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1637_, v___x_1638_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1640_; 
lean_dec_ref_known(v___x_1639_, 1);
v___x_1640_ = l_Lean_MVarId_getType(v_mvarId_1627_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1641_, v_a_1632_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v___x_1644_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1643_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
return v___x_1644_;
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1642_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1642_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1640_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1640_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_dec(v_mvarId_1627_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1671_, v_x_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_a_1687_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1678_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1678_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1695_, lean_object* v_x_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1695_, v_x_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1703_, lean_object* v_mvarId_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1704_, v_x_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_mvarId_1713_, lean_object* v_x_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1712_, v_mvarId_1713_, v_x_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_mvarId_1723_, lean_object* v_needle_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = lean_st_mk_ref(v___x_1721_);
v___x_1731_ = lean_st_mk_ref(v___x_1722_);
v___x_1732_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1723_, v___x_1731_, v_needle_1724_, v___x_1730_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1742_; 
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v___x_1732_, 0);
lean_dec(v_unused_1743_);
v___x_1734_ = v___x_1732_;
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v___x_1732_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1742_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_calls_1738_; lean_object* v___x_1740_; 
v___x_1736_ = lean_st_ref_get(v___x_1731_);
lean_dec(v___x_1731_);
lean_dec(v___x_1736_);
v___x_1737_ = lean_st_ref_get(v___x_1730_);
lean_dec(v___x_1730_);
v_calls_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_ref(v_calls_1738_);
lean_dec(v___x_1737_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_calls_1738_);
v___x_1740_ = v___x_1734_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_calls_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v___x_1731_);
lean_dec(v___x_1730_);
v_a_1744_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1732_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1732_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1752_, lean_object* v___x_1753_, lean_object* v_mvarId_1754_, lean_object* v_needle_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1752_, v___x_1753_, v_mvarId_1754_, v_needle_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec_ref(v_needle_1755_);
return v_res_1761_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_unsigned_to_nat(64u);
v___x_1763_ = l_Lean_mkPtrSet___redArg(v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1764_, lean_object* v_mvarId_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; 
v___x_1771_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_1772_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
lean_inc(v_mvarId_1765_);
v___f_1773_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1773_, 0, v___x_1772_);
lean_closure_set(v___f_1773_, 1, v___x_1771_);
lean_closure_set(v___f_1773_, 2, v_mvarId_1765_);
lean_closure_set(v___f_1773_, 3, v_needle_1764_);
v___x_1774_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1765_, v___f_1773_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_1775_, lean_object* v_mvarId_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1775_, v_mvarId_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_1783_, lean_object* v_mvarId_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1783_, v_mvarId_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_1791_, lean_object* v_mvarId_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1791_, v_mvarId_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_1799_, lean_object* v_mvarId_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1799_, v_mvarId_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_1807_, lean_object* v_mvarId_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Meta_FunInd_collect(v_needle_1807_, v_mvarId_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1814_;
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
