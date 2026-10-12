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
uint64_t l_Lean_Meta_FunInd_instHashableCall_hash(lean_object* v_x_1_){
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
LEAN_EXPORT void l_Lean_Meta_FunInd_instHashableCall_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint64_t v_res_9_;
v_res_9_ = l_Lean_Meta_FunInd_instHashableCall_hash(v_x_1_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instHashableCall_hash___boxed(lean_object* v_x_10_){
_start:
{
uint64_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_Meta_FunInd_instHashableCall_hash(v_x_10_);
lean_dec_ref(v_x_10_);
v_r_12_ = lean_box_uint64(v_res_11_);
return v_r_12_;
}
}
uint8_t l_Lean_Meta_FunInd_instBEqCall_beq(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_expr_17_; lean_object* v_relevantArgs_18_; lean_object* v_expr_19_; lean_object* v_relevantArgs_20_; uint8_t v___x_21_; 
v_expr_17_ = lean_ctor_get(v_x_15_, 0);
v_relevantArgs_18_ = lean_ctor_get(v_x_15_, 1);
v_expr_19_ = lean_ctor_get(v_x_16_, 0);
v_relevantArgs_20_ = lean_ctor_get(v_x_16_, 1);
v___x_21_ = lean_expr_eqv(v_expr_17_, v_expr_19_);
if (v___x_21_ == 0)
{
return v___x_21_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = lean_expr_eqv(v_relevantArgs_18_, v_relevantArgs_20_);
return v___x_22_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_instBEqCall_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_15_ = stack[0].m_obj;
lean_object* v_x_16_ = stack[1].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_Lean_Meta_FunInd_instBEqCall_beq(v_x_15_, v_x_16_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instBEqCall_beq___boxed(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Lean_Meta_FunInd_instBEqCall_beq(v_x_24_, v_x_25_);
lean_dec_ref(v_x_25_);
lean_dec_ref(v_x_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_unsigned_to_nat(16u);
v___x_34_ = lean_mk_array(v___x_33_, v___x_32_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2);
v___x_39_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
return v___x_41_;
}
}
uint8_t l_Lean_Meta_FunInd_SeenCalls_isEmpty(lean_object* v_sc_42_){
_start:
{
lean_object* v_calls_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_calls_43_ = lean_ctor_get(v_sc_42_, 0);
v___x_44_ = lean_array_get_size(v_calls_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_nat_dec_eq(v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_SeenCalls_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_sc_42_ = stack[0].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Lean_Meta_FunInd_SeenCalls_isEmpty(v_sc_42_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(lean_object* v_sc_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lean_Meta_FunInd_SeenCalls_isEmpty(v_sc_48_);
lean_dec_ref(v_sc_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(lean_object* v_xs_51_, lean_object* v_ys_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_zero_54_; uint8_t v_isZero_55_; 
v_zero_54_ = lean_unsigned_to_nat(0u);
v_isZero_55_ = lean_nat_dec_eq(v_x_53_, v_zero_54_);
if (v_isZero_55_ == 1)
{
lean_dec(v_x_53_);
return v_isZero_55_;
}
else
{
lean_object* v_one_56_; lean_object* v_n_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_one_56_ = lean_unsigned_to_nat(1u);
v_n_57_ = lean_nat_sub(v_x_53_, v_one_56_);
lean_dec(v_x_53_);
v___x_58_ = lean_array_fget_borrowed(v_xs_51_, v_n_57_);
v___x_59_ = lean_array_fget_borrowed(v_ys_52_, v_n_57_);
v___x_60_ = lean_expr_eqv(v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
lean_dec(v_n_57_);
return v___x_60_;
}
else
{
v_x_53_ = v_n_57_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_51_ = stack[0].m_obj;
lean_object* v_ys_52_ = stack[1].m_obj;
lean_object* v_x_53_ = stack[2].m_obj;
uint8_t v_res_62_;
v_res_62_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_51_, v_ys_52_, v_x_53_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_xs_63_, lean_object* v_ys_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_63_, v_ys_64_, v_x_65_);
lean_dec_ref(v_ys_64_);
lean_dec_ref(v_xs_63_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
else
{
lean_object* v_key_71_; lean_object* v_tail_72_; uint8_t v___y_74_; lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v_fst_78_; lean_object* v_snd_79_; uint8_t v___x_80_; 
v_key_71_ = lean_ctor_get(v_x_69_, 0);
v_tail_72_ = lean_ctor_get(v_x_69_, 2);
v_fst_76_ = lean_ctor_get(v_key_71_, 0);
v_snd_77_ = lean_ctor_get(v_key_71_, 1);
v_fst_78_ = lean_ctor_get(v_a_68_, 0);
v_snd_79_ = lean_ctor_get(v_a_68_, 1);
v___x_80_ = lean_name_eq(v_fst_76_, v_fst_78_);
if (v___x_80_ == 0)
{
v___y_74_ = v___x_80_;
goto v___jp_73_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_array_get_size(v_snd_77_);
v___x_82_ = lean_array_get_size(v_snd_79_);
v___x_83_ = lean_nat_dec_eq(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
v_x_69_ = v_tail_72_;
goto _start;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_snd_77_, v_snd_79_, v___x_81_);
v___y_74_ = v___x_85_;
goto v___jp_73_;
}
}
v___jp_73_:
{
if (v___y_74_ == 0)
{
v_x_69_ = v_tail_72_;
goto _start;
}
else
{
return v___y_74_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_68_ = stack[0].m_obj;
lean_object* v_x_69_ = stack[1].m_obj;
uint8_t v_res_86_;
v_res_86_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_68_, v_x_69_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg___boxed(lean_object* v_a_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec_ref(v_a_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(lean_object* v_as_91_, size_t v_i_92_, size_t v_stop_93_, uint64_t v_b_94_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = lean_usize_dec_eq(v_i_92_, v_stop_93_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; size_t v___x_99_; size_t v___x_100_; 
v___x_96_ = lean_array_uget_borrowed(v_as_91_, v_i_92_);
v___x_97_ = l_Lean_Expr_hash(v___x_96_);
v___x_98_ = lean_uint64_mix_hash(v_b_94_, v___x_97_);
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_add(v_i_92_, v___x_99_);
v_i_92_ = v___x_100_;
v_b_94_ = v___x_98_;
goto _start;
}
else
{
return v_b_94_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_91_ = stack[0].m_obj;
size_t v_i_92_ = stack[1].m_num;
size_t v_stop_93_ = stack[2].m_num;
uint64_t v_b_94_ = stack[3].m_num;
uint64_t v_res_102_;
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_as_91_, v_i_92_, v_stop_93_, v_b_94_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2___boxed(lean_object* v_as_103_, lean_object* v_i_104_, lean_object* v_stop_105_, lean_object* v_b_106_){
_start:
{
size_t v_i_boxed_107_; size_t v_stop_boxed_108_; uint64_t v_b_boxed_109_; uint64_t v_res_110_; lean_object* v_r_111_; 
v_i_boxed_107_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_stop_boxed_108_ = lean_unbox_usize(v_stop_105_);
lean_dec(v_stop_105_);
v_b_boxed_109_ = lean_unbox_uint64(v_b_106_);
lean_dec_ref(v_b_106_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_as_103_, v_i_boxed_107_, v_stop_boxed_108_, v_b_boxed_109_);
lean_dec_ref(v_as_103_);
v_r_111_ = lean_box_uint64(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
return v_x_112_;
}
else
{
lean_object* v_key_114_; lean_object* v_value_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_155_; 
v_key_114_ = lean_ctor_get(v_x_113_, 0);
v_value_115_ = lean_ctor_get(v_x_113_, 1);
v_tail_116_ = lean_ctor_get(v_x_113_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_155_ == 0)
{
v___x_118_ = v_x_113_;
v_isShared_119_ = v_isSharedCheck_155_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_value_115_);
lean_inc(v_key_114_);
lean_dec(v_x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_155_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_fst_120_; lean_object* v_snd_121_; lean_object* v___x_122_; uint64_t v___y_124_; uint64_t v___y_125_; uint64_t v___y_145_; 
v_fst_120_ = lean_ctor_get(v_key_114_, 0);
v_snd_121_ = lean_ctor_get(v_key_114_, 1);
v___x_122_ = lean_array_get_size(v_x_112_);
if (lean_obj_tag(v_fst_120_) == 0)
{
uint64_t v___x_153_; 
v___x_153_ = 1723ULL;
v___y_145_ = v___x_153_;
goto v___jp_144_;
}
else
{
uint64_t v_hash_154_; 
v_hash_154_ = lean_ctor_get_uint64(v_fst_120_, sizeof(void*)*2);
v___y_145_ = v_hash_154_;
goto v___jp_144_;
}
v___jp_123_:
{
uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_fold_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_126_ = lean_uint64_mix_hash(v___y_124_, v___y_125_);
v___x_127_ = 32ULL;
v___x_128_ = lean_uint64_shift_right(v___x_126_, v___x_127_);
v_fold_129_ = lean_uint64_xor(v___x_126_, v___x_128_);
v___x_130_ = 16ULL;
v___x_131_ = lean_uint64_shift_right(v_fold_129_, v___x_130_);
v___x_132_ = lean_uint64_xor(v_fold_129_, v___x_131_);
v___x_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = lean_usize_of_nat(v___x_122_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_sub(v___x_134_, v___x_135_);
v___x_137_ = lean_usize_land(v___x_133_, v___x_136_);
v___x_138_ = lean_array_uget_borrowed(v_x_112_, v___x_137_);
lean_inc(v___x_138_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 2, v___x_138_);
v___x_140_ = v___x_118_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_key_114_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_value_115_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v___x_138_);
v___x_140_ = v_reuseFailAlloc_143_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
v___x_141_ = lean_array_uset(v_x_112_, v___x_137_, v___x_140_);
v_x_112_ = v___x_141_;
v_x_113_ = v_tail_116_;
goto _start;
}
}
v___jp_144_:
{
uint64_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_146_ = 7ULL;
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_array_get_size(v_snd_121_);
v___x_149_ = lean_nat_dec_lt(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
v___y_124_ = v___y_145_;
v___y_125_ = v___x_146_;
goto v___jp_123_;
}
else
{
size_t v___x_150_; size_t v___x_151_; uint64_t v___x_152_; 
v___x_150_ = ((size_t)0ULL);
v___x_151_ = lean_usize_of_nat(v___x_148_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_121_, v___x_150_, v___x_151_, v___x_146_);
v___y_124_ = v___y_145_;
v___y_125_ = v___x_152_;
goto v___jp_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(lean_object* v_i_156_, lean_object* v_source_157_, lean_object* v_target_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_array_get_size(v_source_157_);
v___x_160_ = lean_nat_dec_lt(v_i_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v_source_157_);
lean_dec(v_i_156_);
return v_target_158_;
}
else
{
lean_object* v_es_161_; lean_object* v___x_162_; lean_object* v_source_163_; lean_object* v_target_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_es_161_ = lean_array_fget(v_source_157_, v_i_156_);
v___x_162_ = lean_box(0);
v_source_163_ = lean_array_fset(v_source_157_, v_i_156_, v___x_162_);
v_target_164_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_target_158_, v_es_161_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_156_, v___x_165_);
lean_dec(v_i_156_);
v_i_156_ = v___x_166_;
v_source_157_ = v_source_163_;
v_target_158_ = v_target_164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(lean_object* v_data_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_nbuckets_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_169_ = lean_array_get_size(v_data_168_);
v___x_170_ = lean_unsigned_to_nat(2u);
v_nbuckets_171_ = lean_nat_mul(v___x_169_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_box(0);
v___x_174_ = lean_mk_array(v_nbuckets_171_, v___x_173_);
v___x_175_ = lean_array_propagate_mark(v_data_168_, v___x_174_);
v___x_176_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_172_, v_data_168_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object* v_m_177_, lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_size_180_; lean_object* v_buckets_181_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v___x_184_; uint64_t v___y_186_; uint64_t v___y_187_; uint64_t v___y_226_; 
v_size_180_ = lean_ctor_get(v_m_177_, 0);
v_buckets_181_ = lean_ctor_get(v_m_177_, 1);
v_fst_182_ = lean_ctor_get(v_a_178_, 0);
v_snd_183_ = lean_ctor_get(v_a_178_, 1);
v___x_184_ = lean_array_get_size(v_buckets_181_);
if (lean_obj_tag(v_fst_182_) == 0)
{
uint64_t v___x_234_; 
v___x_234_ = 1723ULL;
v___y_226_ = v___x_234_;
goto v___jp_225_;
}
else
{
uint64_t v_hash_235_; 
v_hash_235_ = lean_ctor_get_uint64(v_fst_182_, sizeof(void*)*2);
v___y_226_ = v_hash_235_;
goto v___jp_225_;
}
v___jp_185_:
{
uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v_fold_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v_bkt_200_; uint8_t v___x_201_; 
v___x_188_ = lean_uint64_mix_hash(v___y_186_, v___y_187_);
v___x_189_ = 32ULL;
v___x_190_ = lean_uint64_shift_right(v___x_188_, v___x_189_);
v_fold_191_ = lean_uint64_xor(v___x_188_, v___x_190_);
v___x_192_ = 16ULL;
v___x_193_ = lean_uint64_shift_right(v_fold_191_, v___x_192_);
v___x_194_ = lean_uint64_xor(v_fold_191_, v___x_193_);
v___x_195_ = lean_uint64_to_usize(v___x_194_);
v___x_196_ = lean_usize_of_nat(v___x_184_);
v___x_197_ = ((size_t)1ULL);
v___x_198_ = lean_usize_sub(v___x_196_, v___x_197_);
v___x_199_ = lean_usize_land(v___x_195_, v___x_198_);
v_bkt_200_ = lean_array_uget_borrowed(v_buckets_181_, v___x_199_);
v___x_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_178_, v_bkt_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_222_; 
lean_inc_ref(v_buckets_181_);
lean_inc(v_size_180_);
v_isSharedCheck_222_ = !lean_is_exclusive(v_m_177_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; lean_object* v_unused_224_; 
v_unused_223_ = lean_ctor_get(v_m_177_, 1);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_m_177_, 0);
lean_dec(v_unused_224_);
v___x_203_ = v_m_177_;
v_isShared_204_ = v_isSharedCheck_222_;
goto v_resetjp_202_;
}
else
{
lean_dec(v_m_177_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_222_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v_size_x27_206_; lean_object* v___x_207_; lean_object* v_buckets_x27_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v_size_x27_206_ = lean_nat_add(v_size_180_, v___x_205_);
lean_dec(v_size_180_);
lean_inc(v_bkt_200_);
v___x_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_207_, 0, v_a_178_);
lean_ctor_set(v___x_207_, 1, v_b_179_);
lean_ctor_set(v___x_207_, 2, v_bkt_200_);
v_buckets_x27_208_ = lean_array_uset(v_buckets_181_, v___x_199_, v___x_207_);
v___x_209_ = lean_unsigned_to_nat(4u);
v___x_210_ = lean_nat_mul(v_size_x27_206_, v___x_209_);
v___x_211_ = lean_unsigned_to_nat(3u);
v___x_212_ = lean_nat_div(v___x_210_, v___x_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_array_get_size(v_buckets_x27_208_);
v___x_214_ = lean_nat_dec_le(v___x_212_, v___x_213_);
lean_dec(v___x_212_);
if (v___x_214_ == 0)
{
lean_object* v_val_215_; lean_object* v___x_217_; 
v_val_215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_208_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_val_215_);
lean_ctor_set(v___x_203_, 0, v_size_x27_206_);
v___x_217_ = v___x_203_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_size_x27_206_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_val_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
else
{
lean_object* v___x_220_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_buckets_x27_208_);
lean_ctor_set(v___x_203_, 0, v_size_x27_206_);
v___x_220_ = v___x_203_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_size_x27_206_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_buckets_x27_208_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_dec(v_b_179_);
lean_dec_ref(v_a_178_);
return v_m_177_;
}
}
v___jp_225_:
{
uint64_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_227_ = 7ULL;
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_array_get_size(v_snd_183_);
v___x_230_ = lean_nat_dec_lt(v___x_228_, v___x_229_);
if (v___x_230_ == 0)
{
v___y_186_ = v___y_226_;
v___y_187_ = v___x_227_;
goto v___jp_185_;
}
else
{
size_t v___x_231_; size_t v___x_232_; uint64_t v___x_233_; 
v___x_231_ = ((size_t)0ULL);
v___x_232_ = lean_usize_of_nat(v___x_229_);
v___x_233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_183_, v___x_231_, v___x_232_, v___x_227_);
v___y_186_ = v___y_226_;
v___y_187_ = v___x_233_;
goto v___jp_185_;
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_buckets_238_; lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v___x_241_; uint64_t v___y_243_; uint64_t v___y_244_; uint64_t v___y_260_; 
v_buckets_238_ = lean_ctor_get(v_m_236_, 1);
v_fst_239_ = lean_ctor_get(v_a_237_, 0);
v_snd_240_ = lean_ctor_get(v_a_237_, 1);
v___x_241_ = lean_array_get_size(v_buckets_238_);
if (lean_obj_tag(v_fst_239_) == 0)
{
uint64_t v___x_268_; 
v___x_268_ = 1723ULL;
v___y_260_ = v___x_268_;
goto v___jp_259_;
}
else
{
uint64_t v_hash_269_; 
v_hash_269_ = lean_ctor_get_uint64(v_fst_239_, sizeof(void*)*2);
v___y_260_ = v_hash_269_;
goto v___jp_259_;
}
v___jp_242_:
{
uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_245_ = lean_uint64_mix_hash(v___y_243_, v___y_244_);
v___x_246_ = 32ULL;
v___x_247_ = lean_uint64_shift_right(v___x_245_, v___x_246_);
v_fold_248_ = lean_uint64_xor(v___x_245_, v___x_247_);
v___x_249_ = 16ULL;
v___x_250_ = lean_uint64_shift_right(v_fold_248_, v___x_249_);
v___x_251_ = lean_uint64_xor(v_fold_248_, v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = lean_usize_of_nat(v___x_241_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v___x_253_, v___x_254_);
v___x_256_ = lean_usize_land(v___x_252_, v___x_255_);
v___x_257_ = lean_array_uget_borrowed(v_buckets_238_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_237_, v___x_257_);
return v___x_258_;
}
v___jp_259_:
{
uint64_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_261_ = 7ULL;
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_array_get_size(v_snd_240_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
v___y_243_ = v___y_260_;
v___y_244_ = v___x_261_;
goto v___jp_242_;
}
else
{
size_t v___x_265_; size_t v___x_266_; uint64_t v___x_267_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_263_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_240_, v___x_265_, v___x_266_, v___x_261_);
v___y_243_ = v___y_260_;
v___y_244_ = v___x_267_;
goto v___jp_242_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_236_ = stack[0].m_obj;
lean_object* v_a_237_ = stack[1].m_obj;
uint8_t v_res_270_;
v_res_270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_236_, v_a_237_);
stack->m_num = v_res_270_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_271_, v_a_272_);
lean_dec_ref(v_a_272_);
lean_dec_ref(v_m_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object* v_calls_275_, lean_object* v_as_276_, size_t v_sz_277_, size_t v_i_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_a_282_; uint8_t v___x_286_; 
v___x_286_ = lean_usize_dec_lt(v_i_278_, v_sz_277_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec_ref(v_calls_275_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_b_279_);
return v___x_287_;
}
else
{
lean_object* v_snd_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_345_; 
v_snd_288_ = lean_ctor_get(v_b_279_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_b_279_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_b_279_, 0);
lean_dec(v_unused_346_);
v___x_290_ = v_b_279_;
v_isShared_291_ = v_isSharedCheck_345_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_snd_288_);
lean_dec(v_b_279_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_345_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_snd_292_; lean_object* v_fst_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_344_; 
v_snd_292_ = lean_ctor_get(v_snd_288_, 1);
v_fst_293_ = lean_ctor_get(v_snd_288_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_snd_288_);
if (v_isSharedCheck_344_ == 0)
{
v___x_295_ = v_snd_288_;
v_isShared_296_ = v_isSharedCheck_344_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_snd_292_);
lean_inc(v_fst_293_);
lean_dec(v_snd_288_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_344_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_array_297_; lean_object* v_start_298_; lean_object* v_stop_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_array_297_ = lean_ctor_get(v_snd_292_, 0);
v_start_298_ = lean_ctor_get(v_snd_292_, 1);
v_stop_299_ = lean_ctor_get(v_snd_292_, 2);
v___x_300_ = lean_box(0);
v___x_301_ = lean_nat_dec_lt(v_start_298_, v_stop_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v_calls_275_);
if (v_isShared_296_ == 0)
{
v___x_303_ = v___x_295_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_fst_293_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_snd_292_);
v___x_303_ = v_reuseFailAlloc_308_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v___x_303_);
lean_ctor_set(v___x_290_, 0, v___x_300_);
v___x_305_ = v___x_290_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_303_);
v___x_305_ = v_reuseFailAlloc_307_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
else
{
lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_340_; 
lean_inc(v_stop_299_);
lean_inc(v_start_298_);
lean_inc_ref(v_array_297_);
v_isSharedCheck_340_ = !lean_is_exclusive(v_snd_292_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_341_ = lean_ctor_get(v_snd_292_, 2);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_snd_292_, 1);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_snd_292_, 0);
lean_dec(v_unused_343_);
v___x_310_ = v_snd_292_;
v_isShared_311_ = v_isSharedCheck_340_;
goto v_resetjp_309_;
}
else
{
lean_dec(v_snd_292_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_340_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v_a_312_ = lean_array_uget_borrowed(v_as_276_, v_i_278_);
v___x_313_ = lean_array_fget(v_array_297_, v_start_298_);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_start_298_, v___x_314_);
lean_dec(v_start_298_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_315_);
v___x_317_ = v___x_310_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_array_297_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_stop_299_);
v___x_317_ = v_reuseFailAlloc_339_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
uint8_t v___x_333_; 
v___x_333_ = lean_unbox(v___x_313_);
if (v___x_333_ == 2)
{
uint8_t v___x_334_; 
v___x_334_ = l_Lean_Expr_isFVar(v_a_312_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v___x_313_);
lean_del_object(v___x_295_);
lean_del_object(v___x_290_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_calls_275_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_fst_293_);
lean_ctor_set(v___x_336_, 1, v___x_317_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
else
{
goto v___jp_318_;
}
}
else
{
goto v___jp_318_;
}
v___jp_318_:
{
uint8_t v___x_319_; 
v___x_319_ = lean_unbox(v___x_313_);
lean_dec(v___x_313_);
if (v___x_319_ == 0)
{
lean_object* v___x_321_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_317_);
v___x_321_ = v___x_295_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_fst_293_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_317_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v___x_321_);
lean_ctor_set(v___x_290_, 0, v___x_300_);
v___x_323_ = v___x_290_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v_a_282_ = v___x_323_;
goto v___jp_281_;
}
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_328_; 
lean_inc(v_a_312_);
v___x_326_ = lean_array_push(v_fst_293_, v_a_312_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_317_);
lean_ctor_set(v___x_295_, 0, v___x_326_);
v___x_328_ = v___x_295_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_317_);
v___x_328_ = v_reuseFailAlloc_332_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v___x_328_);
lean_ctor_set(v___x_290_, 0, v___x_300_);
v___x_330_ = v___x_290_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v_a_282_ = v___x_330_;
goto v___jp_281_;
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
v___jp_281_:
{
size_t v___x_283_; size_t v___x_284_; 
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_278_, v___x_283_);
v_i_278_ = v___x_284_;
v_b_279_ = v_a_282_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_calls_275_ = stack[0].m_obj;
lean_object* v_as_276_ = stack[1].m_obj;
size_t v_sz_277_ = stack[2].m_num;
size_t v_i_278_ = stack[3].m_num;
lean_object* v_b_279_ = stack[4].m_obj;
lean_object* v_res_347_;
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_275_, v_as_276_, v_sz_277_, v_i_278_, v_b_279_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object* v_calls_348_, lean_object* v_as_349_, lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_b_352_, lean_object* v___y_353_){
_start:
{
size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v_sz_boxed_354_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_355_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_348_, v_as_349_, v_sz_boxed_354_, v_i_boxed_355_, v_b_352_);
lean_dec_ref(v_as_349_);
return v_res_356_;
}
}
lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object* v_e_357_, lean_object* v_funIndInfo_358_, lean_object* v_args_359_, lean_object* v_calls_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_funName_366_; lean_object* v_params_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_funName_366_ = lean_ctor_get(v_funIndInfo_358_, 0);
lean_inc(v_funName_366_);
v_params_367_ = lean_ctor_get(v_funIndInfo_358_, 3);
lean_inc_ref(v_params_367_);
lean_dec_ref(v_funIndInfo_358_);
v___x_368_ = lean_array_get_size(v_params_367_);
v___x_369_ = lean_array_get_size(v_args_359_);
v___x_370_ = lean_nat_dec_eq(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec_ref(v_params_367_);
lean_dec(v_funName_366_);
lean_dec_ref(v_e_357_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_calls_360_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v_keys_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; size_t v_sz_378_; size_t v___x_379_; lean_object* v___x_380_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v_keys_373_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_374_ = l_Array_toSubarray___redArg(v_params_367_, v___x_372_, v___x_368_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_keys_373_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v_sz_378_ = lean_array_size(v_args_359_);
v___x_379_ = ((size_t)0ULL);
lean_inc_ref(v_calls_360_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_360_, v_args_359_, v_sz_378_, v___x_379_, v___x_377_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_421_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_421_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_421_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_421_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_fst_385_; 
v_fst_385_ = lean_ctor_get(v_a_381_, 0);
if (lean_obj_tag(v_fst_385_) == 0)
{
lean_object* v_snd_386_; lean_object* v_fst_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_415_; 
v_snd_386_ = lean_ctor_get(v_a_381_, 1);
lean_inc(v_snd_386_);
lean_dec(v_a_381_);
v_fst_387_ = lean_ctor_get(v_snd_386_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_snd_386_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_snd_386_, 1);
lean_dec(v_unused_416_);
v___x_389_ = v_snd_386_;
v_isShared_390_ = v_isSharedCheck_415_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_fst_387_);
lean_dec(v_snd_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_415_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_calls_391_; lean_object* v_seen_392_; lean_object* v___x_394_; 
v_calls_391_ = lean_ctor_get(v_calls_360_, 0);
v_seen_392_ = lean_ctor_get(v_calls_360_, 1);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v_fst_387_);
lean_ctor_set(v___x_389_, 0, v_funName_366_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_funName_366_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_fst_387_);
v___x_394_ = v_reuseFailAlloc_414_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
uint8_t v___x_395_; 
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_392_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_408_; 
lean_inc_ref(v_seen_392_);
lean_inc_ref(v_calls_391_);
v_isSharedCheck_408_ = !lean_is_exclusive(v_calls_360_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; lean_object* v_unused_410_; 
v_unused_409_ = lean_ctor_get(v_calls_360_, 1);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_calls_360_, 0);
lean_dec(v_unused_410_);
v___x_397_ = v_calls_360_;
v_isShared_398_ = v_isSharedCheck_408_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_calls_360_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_408_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_399_ = lean_array_push(v_calls_391_, v_e_357_);
v___x_400_ = lean_box(0);
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_392_, v___x_394_, v___x_400_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_401_);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_403_ = v___x_397_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_403_);
v___x_405_ = v___x_383_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v___x_412_; 
lean_dec_ref(v___x_394_);
lean_dec_ref(v_e_357_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_calls_360_);
v___x_412_ = v___x_383_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_calls_360_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
lean_object* v_val_417_; lean_object* v___x_419_; 
lean_inc_ref(v_fst_385_);
lean_dec(v_a_381_);
lean_dec(v_funName_366_);
lean_dec_ref(v_calls_360_);
lean_dec_ref(v_e_357_);
v_val_417_ = lean_ctor_get(v_fst_385_, 0);
lean_inc(v_val_417_);
lean_dec_ref_known(v_fst_385_, 1);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_val_417_);
v___x_419_ = v___x_383_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_val_417_);
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
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_funName_366_);
lean_dec_ref(v_calls_360_);
lean_dec_ref(v_e_357_);
v_a_422_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_380_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_380_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_SeenCalls_push_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_357_ = stack[0].m_obj;
lean_object* v_funIndInfo_358_ = stack[1].m_obj;
lean_object* v_args_359_ = stack[2].m_obj;
lean_object* v_calls_360_ = stack[3].m_obj;
lean_object* v_a_361_ = stack[4].m_obj;
lean_object* v_a_362_ = stack[5].m_obj;
lean_object* v_a_363_ = stack[6].m_obj;
lean_object* v_a_364_ = stack[7].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_357_, v_funIndInfo_358_, v_args_359_, v_calls_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object* v_e_431_, lean_object* v_funIndInfo_432_, lean_object* v_args_433_, lean_object* v_calls_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_431_, v_funIndInfo_432_, v_args_433_, v_calls_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec_ref(v_args_433_);
return v_res_440_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object* v_calls_441_, lean_object* v_as_442_, size_t v_sz_443_, size_t v_i_444_, lean_object* v_b_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_441_, v_as_442_, v_sz_443_, v_i_444_, v_b_445_);
return v___x_451_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_calls_441_ = stack[0].m_obj;
lean_object* v_as_442_ = stack[1].m_obj;
size_t v_sz_443_ = stack[2].m_num;
size_t v_i_444_ = stack[3].m_num;
lean_object* v_b_445_ = stack[4].m_obj;
lean_object* v___y_446_ = stack[5].m_obj;
lean_object* v___y_447_ = stack[6].m_obj;
lean_object* v___y_448_ = stack[7].m_obj;
lean_object* v___y_449_ = stack[8].m_obj;
lean_object* v_res_452_;
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_441_, v_as_442_, v_sz_443_, v_i_444_, v_b_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object* v_calls_453_, lean_object* v_as_454_, lean_object* v_sz_455_, lean_object* v_i_456_, lean_object* v_b_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
size_t v_sz_boxed_463_; size_t v_i_boxed_464_; lean_object* v_res_465_; 
v_sz_boxed_463_ = lean_unbox_usize(v_sz_455_);
lean_dec(v_sz_455_);
v_i_boxed_464_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_453_, v_as_454_, v_sz_boxed_463_, v_i_boxed_464_, v_b_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_as_454_);
return v_res_465_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object* v_00_u03b2_466_, lean_object* v_m_467_, lean_object* v_a_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_467_, v_a_468_);
return v___x_469_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_467_ = stack[1].m_obj;
lean_object* v_a_468_ = stack[2].m_obj;
uint8_t v_res_470_;
v_res_470_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_box(0), v_m_467_, v_a_468_);
stack->m_num = v_res_470_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object* v_00_u03b2_471_, lean_object* v_m_472_, lean_object* v_a_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(v_00_u03b2_471_, v_m_472_, v_a_473_);
lean_dec_ref(v_a_473_);
lean_dec_ref(v_m_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object* v_00_u03b2_476_, lean_object* v_m_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_477_, v_a_478_, v_b_479_);
return v___x_480_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object* v_00_u03b2_481_, lean_object* v_a_482_, lean_object* v_x_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_482_, v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_482_ = stack[1].m_obj;
lean_object* v_x_483_ = stack[2].m_obj;
uint8_t v_res_485_;
v_res_485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_box(0), v_a_482_, v_x_483_);
stack->m_num = v_res_485_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object* v_00_u03b2_486_, lean_object* v_a_487_, lean_object* v_x_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_486_, v_a_487_, v_x_488_);
lean_dec(v_x_488_);
lean_dec_ref(v_a_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object* v_00_u03b2_491_, lean_object* v_data_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_492_);
return v___x_493_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(lean_object* v_xs_494_, lean_object* v_ys_495_, lean_object* v_hsz_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_494_, v_ys_495_, v_x_497_);
return v___x_499_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_494_ = stack[0].m_obj;
lean_object* v_ys_495_ = stack[1].m_obj;
lean_object* v_x_497_ = stack[3].m_obj;
uint8_t v_res_500_;
v_res_500_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_494_, v_ys_495_, lean_box(0), v_x_497_, lean_box(0));
stack->m_num = v_res_500_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_501_, lean_object* v_ys_502_, lean_object* v_hsz_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_501_, v_ys_502_, v_hsz_503_, v_x_504_, v_x_505_);
lean_dec_ref(v_ys_502_);
lean_dec_ref(v_xs_501_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_508_, lean_object* v_i_509_, lean_object* v_source_510_, lean_object* v_target_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_509_, v_source_510_, v_target_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_514_, v_x_515_);
return v___x_516_;
}
}
uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object* v_snd_517_, lean_object* v_x_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_NameSet_contains(v_snd_517_, v_x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
v___x_520_ = 1;
return v___x_520_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = 0;
return v___x_521_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_517_ = stack[0].m_obj;
lean_object* v_x_518_ = stack[1].m_obj;
uint8_t v_res_522_;
v_res_522_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_517_, v_x_518_);
stack->m_num = v_res_522_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object* v_snd_523_, lean_object* v_x_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_523_, v_x_524_);
lean_dec(v_x_524_);
lean_dec(v_snd_523_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
if (lean_obj_tag(v_a_527_) == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_a_528_);
return v___x_529_;
}
else
{
lean_object* v_key_530_; lean_object* v_tail_531_; lean_object* v_fst_532_; lean_object* v_fst_533_; lean_object* v_snd_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_554_; 
v_key_530_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_key_530_);
v_tail_531_ = lean_ctor_get(v_a_527_, 2);
lean_inc(v_tail_531_);
lean_dec_ref_known(v_a_527_, 3);
v_fst_532_ = lean_ctor_get(v_key_530_, 0);
lean_inc(v_fst_532_);
lean_dec(v_key_530_);
v_fst_533_ = lean_ctor_get(v_a_528_, 0);
v_snd_534_ = lean_ctor_get(v_a_528_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_a_528_);
if (v_isSharedCheck_554_ == 0)
{
v___x_536_ = v_a_528_;
v_isShared_537_ = v_isSharedCheck_554_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snd_534_);
lean_inc(v_fst_533_);
lean_dec(v_a_528_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_554_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_NameSet_contains(v_snd_534_, v_fst_532_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; 
v___x_539_ = l_Lean_NameSet_contains(v_fst_533_, v_fst_532_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = l_Lean_NameSet_insert(v_fst_533_, v_fst_532_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_540_);
v___x_542_ = v___x_536_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_snd_534_);
v___x_542_ = v_reuseFailAlloc_544_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
v_a_527_ = v_tail_531_;
v_a_528_ = v___x_542_;
goto _start;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = l_Lean_NameSet_insert(v_snd_534_, v_fst_532_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_545_);
v___x_547_ = v___x_536_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_545_);
v___x_547_ = v_reuseFailAlloc_549_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
v_a_527_ = v_tail_531_;
v_a_528_ = v___x_547_;
goto _start;
}
}
}
else
{
lean_object* v___x_551_; 
lean_dec(v_fst_532_);
if (v_isShared_537_ == 0)
{
v___x_551_ = v___x_536_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_snd_534_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v_a_527_ = v_tail_531_;
v_a_528_ = v___x_551_;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(lean_object* v_as_555_, size_t v_sz_556_, size_t v_i_557_, lean_object* v_b_558_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_lt(v_i_557_, v_sz_556_);
if (v___x_559_ == 0)
{
return v_b_558_;
}
else
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_array_uget_borrowed(v_as_555_, v_i_557_);
lean_inc(v_a_560_);
v___x_561_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_560_, v_b_558_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
return v_a_562_;
}
else
{
lean_object* v_a_563_; size_t v___x_564_; size_t v___x_565_; 
v_a_563_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_561_, 1);
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_add(v_i_557_, v___x_564_);
v_i_557_ = v___x_565_;
v_b_558_ = v_a_563_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_555_ = stack[0].m_obj;
size_t v_sz_556_ = stack[1].m_num;
size_t v_i_557_ = stack[2].m_num;
lean_object* v_b_558_ = stack[3].m_obj;
lean_object* v_res_567_;
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_555_, v_sz_556_, v_i_557_, v_b_558_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(lean_object* v_as_568_, lean_object* v_sz_569_, lean_object* v_i_570_, lean_object* v_b_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_569_);
lean_dec(v_sz_569_);
v_i_boxed_573_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_568_, v_sz_boxed_572_, v_i_boxed_573_, v_b_571_);
lean_dec_ref(v_as_568_);
return v_res_574_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0(void){
_start:
{
lean_object* v_seen_575_; lean_object* v___x_576_; 
v_seen_575_ = l_Lean_NameSet_empty;
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_seen_575_);
lean_ctor_set(v___x_576_, 1, v_seen_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object* v_calls_577_){
_start:
{
lean_object* v_seen_578_; lean_object* v___x_579_; lean_object* v_buckets_580_; size_t v_sz_581_; size_t v___x_582_; lean_object* v___x_583_; lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___f_586_; lean_object* v___x_587_; 
v_seen_578_ = lean_ctor_get(v_calls_577_, 1);
v___x_579_ = lean_obj_once(&l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0, &l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once, _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0);
v_buckets_580_ = lean_ctor_get(v_seen_578_, 1);
v_sz_581_ = lean_array_size(v_buckets_580_);
v___x_582_ = ((size_t)0ULL);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_580_, v_sz_581_, v___x_582_, v___x_579_);
v_fst_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_fst_584_);
v_snd_585_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_snd_585_);
lean_dec_ref(v___x_583_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed), 2, 1);
lean_closure_set(v___f_586_, 0, v_snd_585_);
v___x_587_ = l_Lean_NameSet_filter(v___f_586_, v_fst_584_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object* v_calls_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_588_);
lean_dec_ref(v_calls_588_);
return v_res_589_;
}
}
lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object* v_e_590_, lean_object* v_funIndInfo_591_, lean_object* v_args_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_st_ref_get(v_a_593_);
v___x_600_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_590_, v_funIndInfo_591_, v_args_592_, v___x_599_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_610_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_610_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_605_ = lean_box(0);
v___x_606_ = lean_st_ref_swap(v_a_593_, v_a_601_);
lean_dec(v___x_606_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_608_ = v___x_603_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_605_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_a_611_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_600_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_600_);
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
LEAN_EXPORT void l_Lean_Meta_FunInd_Collector_saveFunInd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_590_ = stack[0].m_obj;
lean_object* v_funIndInfo_591_ = stack[1].m_obj;
lean_object* v_args_592_ = stack[2].m_obj;
lean_object* v_a_593_ = stack[3].m_obj;
lean_object* v_a_594_ = stack[4].m_obj;
lean_object* v_a_595_ = stack[5].m_obj;
lean_object* v_a_596_ = stack[6].m_obj;
lean_object* v_a_597_ = stack[7].m_obj;
lean_object* v_res_619_;
v_res_619_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_590_, v_funIndInfo_591_, v_args_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
stack->m_obj
 = v_res_619_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object* v_e_620_, lean_object* v_funIndInfo_621_, lean_object* v_args_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_620_, v_funIndInfo_621_, v_args_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_args_622_);
return v_res_629_;
}
}
lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object* v_e_630_, lean_object* v_funIndInfo_631_, lean_object* v_args_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_630_, v_funIndInfo_631_, v_args_632_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
return v___x_640_;
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_Collector_saveFunInd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_630_ = stack[0].m_obj;
lean_object* v_funIndInfo_631_ = stack[1].m_obj;
lean_object* v_args_632_ = stack[2].m_obj;
lean_object* v_a_633_ = stack[3].m_obj;
lean_object* v_a_634_ = stack[4].m_obj;
lean_object* v_a_635_ = stack[5].m_obj;
lean_object* v_a_636_ = stack[6].m_obj;
lean_object* v_a_637_ = stack[7].m_obj;
lean_object* v_a_638_ = stack[8].m_obj;
lean_object* v_res_641_;
v_res_641_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_630_, v_funIndInfo_631_, v_args_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
stack->m_obj
 = v_res_641_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object* v_e_642_, lean_object* v_funIndInfo_643_, lean_object* v_args_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_642_, v_funIndInfo_643_, v_args_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_args_644_);
return v_res_652_;
}
}
lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object* v_e_653_, lean_object* v_funIndInfo_654_, lean_object* v_args_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_653_, v_funIndInfo_654_, v_args_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
return v___x_662_;
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_Collector_visitApp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_653_ = stack[0].m_obj;
lean_object* v_funIndInfo_654_ = stack[1].m_obj;
lean_object* v_args_655_ = stack[2].m_obj;
lean_object* v_a_656_ = stack[3].m_obj;
lean_object* v_a_657_ = stack[4].m_obj;
lean_object* v_a_658_ = stack[5].m_obj;
lean_object* v_a_659_ = stack[6].m_obj;
lean_object* v_a_660_ = stack[7].m_obj;
lean_object* v_res_663_;
v_res_663_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_653_, v_funIndInfo_654_, v_args_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object* v_e_664_, lean_object* v_funIndInfo_665_, lean_object* v_args_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_664_, v_funIndInfo_665_, v_args_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_args_666_);
return v_res_673_;
}
}
lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object* v_e_674_, lean_object* v_funIndInfo_675_, lean_object* v_args_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_674_, v_funIndInfo_675_, v_args_676_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v___x_684_;
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_Collector_visitApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_674_ = stack[0].m_obj;
lean_object* v_funIndInfo_675_ = stack[1].m_obj;
lean_object* v_args_676_ = stack[2].m_obj;
lean_object* v_a_677_ = stack[3].m_obj;
lean_object* v_a_678_ = stack[4].m_obj;
lean_object* v_a_679_ = stack[5].m_obj;
lean_object* v_a_680_ = stack[6].m_obj;
lean_object* v_a_681_ = stack[7].m_obj;
lean_object* v_a_682_ = stack[8].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_674_, v_funIndInfo_675_, v_args_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object* v_e_686_, lean_object* v_funIndInfo_687_, lean_object* v_args_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_686_, v_funIndInfo_687_, v_args_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec_ref(v_args_688_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
if (lean_obj_tag(v_x_698_) == 0)
{
return v_x_697_;
}
else
{
lean_object* v_key_699_; lean_object* v_value_700_; lean_object* v_tail_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_727_; 
v_key_699_ = lean_ctor_get(v_x_698_, 0);
v_value_700_ = lean_ctor_get(v_x_698_, 1);
v_tail_701_ = lean_ctor_get(v_x_698_, 2);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_698_);
if (v_isSharedCheck_727_ == 0)
{
v___x_703_ = v_x_698_;
v_isShared_704_ = v_isSharedCheck_727_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_tail_701_);
lean_inc(v_value_700_);
lean_inc(v_key_699_);
lean_dec(v_x_698_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_727_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; size_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v_fold_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_705_ = lean_array_get_size(v_x_697_);
v___x_706_ = lean_ptr_addr(v_key_699_);
v___x_707_ = lean_usize_to_uint64(v___x_706_);
v___x_708_ = 11ULL;
v___x_709_ = lean_uint64_mix_hash(v___x_707_, v___x_708_);
v___x_710_ = 32ULL;
v___x_711_ = lean_uint64_shift_right(v___x_709_, v___x_710_);
v_fold_712_ = lean_uint64_xor(v___x_709_, v___x_711_);
v___x_713_ = 16ULL;
v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
v___x_717_ = lean_usize_of_nat(v___x_705_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
v___x_721_ = lean_array_uget_borrowed(v_x_697_, v___x_720_);
lean_inc(v___x_721_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 2, v___x_721_);
v___x_723_ = v___x_703_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_key_699_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_value_700_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v___x_721_);
v___x_723_ = v_reuseFailAlloc_726_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; 
v___x_724_ = lean_array_uset(v_x_697_, v___x_720_, v___x_723_);
v_x_697_ = v___x_724_;
v_x_698_ = v_tail_701_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(lean_object* v_i_728_, lean_object* v_source_729_, lean_object* v_target_730_){
_start:
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_get_size(v_source_729_);
v___x_732_ = lean_nat_dec_lt(v_i_728_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec_ref(v_source_729_);
lean_dec(v_i_728_);
return v_target_730_;
}
else
{
lean_object* v_es_733_; lean_object* v___x_734_; lean_object* v_source_735_; lean_object* v_target_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_es_733_ = lean_array_fget(v_source_729_, v_i_728_);
v___x_734_ = lean_box(0);
v_source_735_ = lean_array_fset(v_source_729_, v_i_728_, v___x_734_);
v_target_736_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_730_, v_es_733_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_i_728_, v___x_737_);
lean_dec(v_i_728_);
v_i_728_ = v___x_738_;
v_source_729_ = v_source_735_;
v_target_730_ = v_target_736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(lean_object* v_data_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_nbuckets_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_741_ = lean_array_get_size(v_data_740_);
v___x_742_ = lean_unsigned_to_nat(2u);
v_nbuckets_743_ = lean_nat_mul(v___x_741_, v___x_742_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_box(0);
v___x_746_ = lean_mk_array(v_nbuckets_743_, v___x_745_);
v___x_747_ = lean_array_propagate_mark(v_data_740_, v___x_746_);
v___x_748_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_744_, v_data_740_, v___x_747_);
return v___x_748_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_a_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
uint8_t v___x_751_; 
v___x_751_ = 0;
return v___x_751_;
}
else
{
lean_object* v_key_752_; lean_object* v_tail_753_; size_t v___x_754_; size_t v___x_755_; uint8_t v___x_756_; 
v_key_752_ = lean_ctor_get(v_x_750_, 0);
v_tail_753_ = lean_ctor_get(v_x_750_, 2);
v___x_754_ = lean_ptr_addr(v_key_752_);
v___x_755_ = lean_ptr_addr(v_a_749_);
v___x_756_ = lean_usize_dec_eq(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
v_x_750_ = v_tail_753_;
goto _start;
}
else
{
return v___x_756_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_749_ = stack[0].m_obj;
lean_object* v_x_750_ = stack[1].m_obj;
uint8_t v_res_758_;
v_res_758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_749_, v_x_750_);
stack->m_num = v_res_758_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_759_, lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_759_, v_x_760_);
lean_dec(v_x_760_);
lean_dec_ref(v_a_759_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(lean_object* v_m_763_, lean_object* v_a_764_, lean_object* v_b_765_){
_start:
{
lean_object* v_size_766_; lean_object* v_buckets_767_; lean_object* v___x_768_; size_t v___x_769_; uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v___x_772_; uint64_t v___x_773_; uint64_t v___x_774_; uint64_t v_fold_775_; uint64_t v___x_776_; uint64_t v___x_777_; uint64_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; size_t v___x_783_; lean_object* v_bkt_784_; uint8_t v___x_785_; 
v_size_766_ = lean_ctor_get(v_m_763_, 0);
v_buckets_767_ = lean_ctor_get(v_m_763_, 1);
v___x_768_ = lean_array_get_size(v_buckets_767_);
v___x_769_ = lean_ptr_addr(v_a_764_);
v___x_770_ = lean_usize_to_uint64(v___x_769_);
v___x_771_ = 11ULL;
v___x_772_ = lean_uint64_mix_hash(v___x_770_, v___x_771_);
v___x_773_ = 32ULL;
v___x_774_ = lean_uint64_shift_right(v___x_772_, v___x_773_);
v_fold_775_ = lean_uint64_xor(v___x_772_, v___x_774_);
v___x_776_ = 16ULL;
v___x_777_ = lean_uint64_shift_right(v_fold_775_, v___x_776_);
v___x_778_ = lean_uint64_xor(v_fold_775_, v___x_777_);
v___x_779_ = lean_uint64_to_usize(v___x_778_);
v___x_780_ = lean_usize_of_nat(v___x_768_);
v___x_781_ = ((size_t)1ULL);
v___x_782_ = lean_usize_sub(v___x_780_, v___x_781_);
v___x_783_ = lean_usize_land(v___x_779_, v___x_782_);
v_bkt_784_ = lean_array_uget_borrowed(v_buckets_767_, v___x_783_);
v___x_785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_764_, v_bkt_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_806_; 
lean_inc_ref(v_buckets_767_);
lean_inc(v_size_766_);
v_isSharedCheck_806_ = !lean_is_exclusive(v_m_763_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; lean_object* v_unused_808_; 
v_unused_807_ = lean_ctor_get(v_m_763_, 1);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_m_763_, 0);
lean_dec(v_unused_808_);
v___x_787_ = v_m_763_;
v_isShared_788_ = v_isSharedCheck_806_;
goto v_resetjp_786_;
}
else
{
lean_dec(v_m_763_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_806_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v_size_x27_790_; lean_object* v___x_791_; lean_object* v_buckets_x27_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v_size_x27_790_ = lean_nat_add(v_size_766_, v___x_789_);
lean_dec(v_size_766_);
lean_inc(v_bkt_784_);
v___x_791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_791_, 0, v_a_764_);
lean_ctor_set(v___x_791_, 1, v_b_765_);
lean_ctor_set(v___x_791_, 2, v_bkt_784_);
v_buckets_x27_792_ = lean_array_uset(v_buckets_767_, v___x_783_, v___x_791_);
v___x_793_ = lean_unsigned_to_nat(4u);
v___x_794_ = lean_nat_mul(v_size_x27_790_, v___x_793_);
v___x_795_ = lean_unsigned_to_nat(3u);
v___x_796_ = lean_nat_div(v___x_794_, v___x_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_array_get_size(v_buckets_x27_792_);
v___x_798_ = lean_nat_dec_le(v___x_796_, v___x_797_);
lean_dec(v___x_796_);
if (v___x_798_ == 0)
{
lean_object* v_val_799_; lean_object* v___x_801_; 
v_val_799_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_792_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_val_799_);
lean_ctor_set(v___x_787_, 0, v_size_x27_790_);
v___x_801_ = v___x_787_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_size_x27_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_val_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
else
{
lean_object* v___x_804_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_buckets_x27_792_);
lean_ctor_set(v___x_787_, 0, v_size_x27_790_);
v___x_804_ = v___x_787_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_size_x27_790_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_buckets_x27_792_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_dec(v_b_765_);
lean_dec_ref(v_a_764_);
return v_m_763_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_buckets_811_; lean_object* v___x_812_; size_t v___x_813_; uint64_t v___x_814_; uint64_t v___x_815_; uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v___x_818_; uint64_t v_fold_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_buckets_811_ = lean_ctor_get(v_m_809_, 1);
v___x_812_ = lean_array_get_size(v_buckets_811_);
v___x_813_ = lean_ptr_addr(v_a_810_);
v___x_814_ = lean_usize_to_uint64(v___x_813_);
v___x_815_ = 11ULL;
v___x_816_ = lean_uint64_mix_hash(v___x_814_, v___x_815_);
v___x_817_ = 32ULL;
v___x_818_ = lean_uint64_shift_right(v___x_816_, v___x_817_);
v_fold_819_ = lean_uint64_xor(v___x_816_, v___x_818_);
v___x_820_ = 16ULL;
v___x_821_ = lean_uint64_shift_right(v_fold_819_, v___x_820_);
v___x_822_ = lean_uint64_xor(v_fold_819_, v___x_821_);
v___x_823_ = lean_uint64_to_usize(v___x_822_);
v___x_824_ = lean_usize_of_nat(v___x_812_);
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_sub(v___x_824_, v___x_825_);
v___x_827_ = lean_usize_land(v___x_823_, v___x_826_);
v___x_828_ = lean_array_uget_borrowed(v_buckets_811_, v___x_827_);
v___x_829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_810_, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_809_ = stack[0].m_obj;
lean_object* v_a_810_ = stack[1].m_obj;
uint8_t v_res_830_;
v_res_830_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_809_, v_a_810_);
stack->m_num = v_res_830_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_831_, lean_object* v_a_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_831_, v_a_832_);
lean_dec_ref(v_a_832_);
lean_dec_ref(v_m_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_835_; lean_object* v_dummy_836_; 
v___x_835_ = lean_box(0);
v_dummy_836_ = l_Lean_Expr_sort___override(v___x_835_);
return v_dummy_836_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_e_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; 
if (lean_obj_tag(v_x_838_) == 5)
{
lean_object* v_fn_870_; lean_object* v_arg_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_fn_870_ = lean_ctor_get(v_x_838_, 0);
lean_inc_ref(v_fn_870_);
v_arg_871_ = lean_ctor_get(v_x_838_, 1);
lean_inc_ref(v_arg_871_);
lean_dec_ref_known(v_x_838_, 2);
v___x_872_ = lean_array_set(v_x_839_, v_x_840_, v_arg_871_);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_sub(v_x_840_, v___x_873_);
lean_dec(v_x_840_);
v_x_838_ = v_fn_870_;
v_x_839_ = v___x_872_;
v_x_840_ = v___x_874_;
goto _start;
}
else
{
lean_dec(v_x_840_);
if (lean_obj_tag(v_x_838_) == 4)
{
lean_object* v_declName_876_; lean_object* v_funName_877_; uint8_t v___x_878_; 
v_declName_876_ = lean_ctor_get(v_x_838_, 0);
lean_inc(v_declName_876_);
lean_dec_ref_known(v_x_838_, 2);
v_funName_877_ = lean_ctor_get(v___y_842_, 0);
v___x_878_ = lean_name_eq(v_declName_876_, v_funName_877_);
lean_dec(v_declName_876_);
if (v___x_878_ == 0)
{
lean_dec_ref(v_e_837_);
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
v___y_856_ = v___y_847_;
goto v___jp_849_;
}
else
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_Expr_hasLooseBVars(v_e_837_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
lean_inc_ref(v___y_842_);
v___x_880_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_837_, v___y_842_, v_x_839_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_dec_ref_known(v___x_880_, 1);
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
v___y_856_ = v___y_847_;
goto v___jp_849_;
}
else
{
lean_dec_ref(v_x_839_);
return v___x_880_;
}
}
else
{
lean_dec_ref(v_e_837_);
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
v___y_856_ = v___y_847_;
goto v___jp_849_;
}
}
}
else
{
lean_object* v___x_881_; 
lean_dec_ref(v_e_837_);
v___x_881_ = l_Lean_Meta_FunInd_Collector_visit(v_x_838_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_dec_ref_known(v___x_881_, 1);
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
v___y_856_ = v___y_847_;
goto v___jp_849_;
}
else
{
lean_dec_ref(v_x_839_);
return v___x_881_;
}
}
}
v___jp_849_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_array_get_size(v_x_839_);
v___x_859_ = lean_box(0);
v___x_860_ = lean_nat_dec_lt(v___x_857_, v___x_858_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_dec_ref(v_x_839_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
return v___x_861_;
}
else
{
uint8_t v___x_862_; 
v___x_862_ = lean_nat_dec_le(v___x_858_, v___x_858_);
if (v___x_862_ == 0)
{
if (v___x_860_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_x_839_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_859_);
return v___x_863_;
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_858_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_839_, v___x_864_, v___x_865_, v___x_859_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec_ref(v_x_839_);
return v___x_866_;
}
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((size_t)0ULL);
v___x_868_ = lean_usize_of_nat(v___x_858_);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_839_, v___x_867_, v___x_868_, v___x_859_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec_ref(v_x_839_);
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_837_ = stack[0].m_obj;
lean_object* v_x_838_ = stack[1].m_obj;
lean_object* v_x_839_ = stack[2].m_obj;
lean_object* v_x_840_ = stack[3].m_obj;
lean_object* v___y_841_ = stack[4].m_obj;
lean_object* v___y_842_ = stack[5].m_obj;
lean_object* v___y_843_ = stack[6].m_obj;
lean_object* v___y_844_ = stack[7].m_obj;
lean_object* v___y_845_ = stack[8].m_obj;
lean_object* v___y_846_ = stack[9].m_obj;
lean_object* v___y_847_ = stack[10].m_obj;
lean_object* v_res_882_;
v_res_882_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_837_, v_x_838_, v_x_839_, v_x_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
stack->m_obj
 = v_res_882_;
}
lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_d_893_; lean_object* v_b_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_st_ref_get(v_a_884_);
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_904_, v_e_883_);
lean_dec(v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = lean_st_ref_take(v_a_884_);
v___x_907_ = lean_box(0);
lean_inc_ref(v_e_883_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_906_, v_e_883_, v___x_907_);
v___x_909_ = lean_st_ref_put(v_a_884_, v___x_908_);
switch(lean_obj_tag(v_e_883_))
{
case 7:
{
lean_object* v_binderType_910_; lean_object* v_body_911_; 
v_binderType_910_ = lean_ctor_get(v_e_883_, 1);
lean_inc_ref(v_binderType_910_);
v_body_911_ = lean_ctor_get(v_e_883_, 2);
lean_inc_ref(v_body_911_);
lean_dec_ref_known(v_e_883_, 3);
v_d_893_ = v_binderType_910_;
v_b_894_ = v_body_911_;
v___y_895_ = v_a_884_;
v___y_896_ = v_a_885_;
v___y_897_ = v_a_886_;
v___y_898_ = v_a_887_;
v___y_899_ = v_a_888_;
v___y_900_ = v_a_889_;
v___y_901_ = v_a_890_;
goto v___jp_892_;
}
case 6:
{
lean_object* v_binderType_912_; lean_object* v_body_913_; 
v_binderType_912_ = lean_ctor_get(v_e_883_, 1);
lean_inc_ref(v_binderType_912_);
v_body_913_ = lean_ctor_get(v_e_883_, 2);
lean_inc_ref(v_body_913_);
lean_dec_ref_known(v_e_883_, 3);
v_d_893_ = v_binderType_912_;
v_b_894_ = v_body_913_;
v___y_895_ = v_a_884_;
v___y_896_ = v_a_885_;
v___y_897_ = v_a_886_;
v___y_898_ = v_a_887_;
v___y_899_ = v_a_888_;
v___y_900_ = v_a_889_;
v___y_901_ = v_a_890_;
goto v___jp_892_;
}
case 10:
{
lean_object* v_expr_914_; 
v_expr_914_ = lean_ctor_get(v_e_883_, 1);
lean_inc_ref(v_expr_914_);
lean_dec_ref_known(v_e_883_, 2);
v_e_883_ = v_expr_914_;
goto _start;
}
case 8:
{
lean_object* v_type_916_; lean_object* v_value_917_; lean_object* v_body_918_; lean_object* v___x_919_; 
v_type_916_ = lean_ctor_get(v_e_883_, 1);
lean_inc_ref(v_type_916_);
v_value_917_ = lean_ctor_get(v_e_883_, 2);
lean_inc_ref(v_value_917_);
v_body_918_ = lean_ctor_get(v_e_883_, 3);
lean_inc_ref(v_body_918_);
lean_dec_ref_known(v_e_883_, 4);
v___x_919_ = l_Lean_Meta_FunInd_Collector_visit(v_type_916_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_920_; 
lean_dec_ref_known(v___x_919_, 1);
v___x_920_ = l_Lean_Meta_FunInd_Collector_visit(v_value_917_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_dec_ref_known(v___x_920_, 1);
v_e_883_ = v_body_918_;
goto _start;
}
else
{
lean_dec_ref(v_body_918_);
return v___x_920_;
}
}
else
{
lean_dec_ref(v_body_918_);
lean_dec_ref(v_value_917_);
return v___x_919_;
}
}
case 5:
{
lean_object* v_dummy_922_; lean_object* v_nargs_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_dummy_922_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_923_ = l_Lean_Expr_getAppNumArgs(v_e_883_);
lean_inc(v_nargs_923_);
v___x_924_ = lean_mk_array(v_nargs_923_, v_dummy_922_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_sub(v_nargs_923_, v___x_925_);
lean_dec(v_nargs_923_);
lean_inc_ref(v_e_883_);
v___x_927_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_883_, v_e_883_, v___x_924_, v___x_926_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_927_;
}
case 11:
{
lean_object* v_struct_928_; 
v_struct_928_ = lean_ctor_get(v_e_883_, 2);
lean_inc_ref(v_struct_928_);
lean_dec_ref_known(v_e_883_, 3);
v_e_883_ = v_struct_928_;
goto _start;
}
default: 
{
lean_object* v___x_930_; 
lean_dec_ref(v_e_883_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_907_);
return v___x_930_;
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v_e_883_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
v___jp_892_:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Meta_FunInd_Collector_visit(v_d_893_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_dec_ref_known(v___x_902_, 1);
v_e_883_ = v_b_894_;
v_a_884_ = v___y_895_;
v_a_885_ = v___y_896_;
v_a_886_ = v___y_897_;
v_a_887_ = v___y_898_;
v_a_888_ = v___y_899_;
v_a_889_ = v___y_900_;
v_a_890_ = v___y_901_;
goto _start;
}
else
{
lean_dec_ref(v_b_894_);
return v___x_902_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_Collector_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_883_ = stack[0].m_obj;
lean_object* v_a_884_ = stack[1].m_obj;
lean_object* v_a_885_ = stack[2].m_obj;
lean_object* v_a_886_ = stack[3].m_obj;
lean_object* v_a_887_ = stack[4].m_obj;
lean_object* v_a_888_ = stack[5].m_obj;
lean_object* v_a_889_ = stack[6].m_obj;
lean_object* v_a_890_ = stack[7].m_obj;
lean_object* v_res_933_;
v_res_933_ = l_Lean_Meta_FunInd_Collector_visit(v_e_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
stack->m_obj
 = v_res_933_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_934_, size_t v_i_935_, size_t v_stop_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_eq(v_i_935_, v_stop_936_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_array_uget_borrowed(v_as_934_, v_i_935_);
lean_inc(v___x_947_);
v___x_948_ = l_Lean_Meta_FunInd_Collector_visit(v___x_947_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; size_t v___x_950_; size_t v___x_951_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_935_, v___x_950_);
v_i_935_ = v___x_951_;
v_b_937_ = v_a_949_;
goto _start;
}
else
{
return v___x_948_;
}
}
else
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_937_);
return v___x_953_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_934_ = stack[0].m_obj;
size_t v_i_935_ = stack[1].m_num;
size_t v_stop_936_ = stack[2].m_num;
lean_object* v_b_937_ = stack[3].m_obj;
lean_object* v___y_938_ = stack[4].m_obj;
lean_object* v___y_939_ = stack[5].m_obj;
lean_object* v___y_940_ = stack[6].m_obj;
lean_object* v___y_941_ = stack[7].m_obj;
lean_object* v___y_942_ = stack[8].m_obj;
lean_object* v___y_943_ = stack[9].m_obj;
lean_object* v___y_944_ = stack[10].m_obj;
lean_object* v_res_954_;
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_934_, v_i_935_, v_stop_936_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_955_, lean_object* v_i_956_, lean_object* v_stop_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
size_t v_i_boxed_967_; size_t v_stop_boxed_968_; lean_object* v_res_969_; 
v_i_boxed_967_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_stop_boxed_968_ = lean_unbox_usize(v_stop_957_);
lean_dec(v_stop_957_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_955_, v_i_boxed_967_, v_stop_boxed_968_, v_b_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v_as_955_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_FunInd_Collector_visit(v_e_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_e_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_980_, v_x_981_, v_x_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
return v_res_992_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_993_, lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_994_, v_a_995_);
return v___x_996_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_994_ = stack[1].m_obj;
lean_object* v_a_995_ = stack[2].m_obj;
uint8_t v_res_997_;
v_res_997_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_box(0), v_m_994_, v_a_995_);
stack->m_num = v_res_997_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_998_, lean_object* v_m_999_, lean_object* v_a_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_998_, v_m_999_, v_a_1000_);
lean_dec_ref(v_a_1000_);
lean_dec_ref(v_m_999_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_00_u03b2_1003_, lean_object* v_m_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_1004_, v_a_1005_, v_b_1006_);
return v___x_1007_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_1008_, lean_object* v_a_1009_, lean_object* v_x_1010_){
_start:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_1009_, v_x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1009_ = stack[1].m_obj;
lean_object* v_x_1010_ = stack[2].m_obj;
uint8_t v_res_1012_;
v_res_1012_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_box(0), v_a_1009_, v_x_1010_);
stack->m_num = v_res_1012_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1013_, lean_object* v_a_1014_, lean_object* v_x_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_1013_, v_a_1014_, v_x_1015_);
lean_dec(v_x_1015_);
lean_dec_ref(v_a_1014_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object* v_00_u03b2_1018_, lean_object* v_data_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1021_, lean_object* v_i_1022_, lean_object* v_source_1023_, lean_object* v_target_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_1022_, v_source_1023_, v_target_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1027_, v_x_1028_);
return v___x_1029_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_1030_, lean_object* v___y_1031_){
_start:
{
uint8_t v___x_1033_; 
v___x_1033_ = l_Lean_Expr_hasMVar(v_e_1030_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_e_1030_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; lean_object* v_mctx_1036_; lean_object* v___x_1037_; lean_object* v_fst_1038_; lean_object* v_snd_1039_; lean_object* v___x_1040_; lean_object* v_cache_1041_; lean_object* v_zetaDeltaFVarIds_1042_; lean_object* v_postponed_1043_; lean_object* v_diag_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1053_; 
v___x_1035_ = lean_st_ref_get(v___y_1031_);
v_mctx_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_ref(v_mctx_1036_);
lean_dec(v___x_1035_);
v___x_1037_ = l_Lean_instantiateMVarsCore(v_mctx_1036_, v_e_1030_);
v_fst_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_fst_1038_);
v_snd_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_snd_1039_);
lean_dec_ref(v___x_1037_);
v___x_1040_ = lean_st_ref_take(v___y_1031_);
v_cache_1041_ = lean_ctor_get(v___x_1040_, 1);
v_zetaDeltaFVarIds_1042_ = lean_ctor_get(v___x_1040_, 2);
v_postponed_1043_ = lean_ctor_get(v___x_1040_, 3);
v_diag_1044_ = lean_ctor_get(v___x_1040_, 4);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1040_, 0);
lean_dec(v_unused_1054_);
v___x_1046_ = v___x_1040_;
v_isShared_1047_ = v_isSharedCheck_1053_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_diag_1044_);
lean_inc(v_postponed_1043_);
lean_inc(v_zetaDeltaFVarIds_1042_);
lean_inc(v_cache_1041_);
lean_dec(v___x_1040_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1053_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v_snd_1039_);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_snd_1039_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_cache_1041_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_zetaDeltaFVarIds_1042_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_postponed_1043_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_diag_1044_);
v___x_1049_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_st_ref_put(v___y_1031_, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_fst_1038_);
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1030_ = stack[0].m_obj;
lean_object* v___y_1031_ = stack[1].m_obj;
lean_object* v_res_1055_;
v_res_1055_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1030_, v___y_1031_);
stack->m_obj
 = v_res_1055_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1056_, v___y_1057_);
lean_dec(v___y_1057_);
return v_res_1059_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1060_, v___y_1065_);
return v___x_1069_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1060_ = stack[0].m_obj;
lean_object* v___y_1061_ = stack[1].m_obj;
lean_object* v___y_1062_ = stack[2].m_obj;
lean_object* v___y_1063_ = stack[3].m_obj;
lean_object* v___y_1064_ = stack[4].m_obj;
lean_object* v___y_1065_ = stack[5].m_obj;
lean_object* v___y_1066_ = stack[6].m_obj;
lean_object* v___y_1067_ = stack[7].m_obj;
lean_object* v_res_1070_;
v_res_1070_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
stack->m_obj
 = v_res_1070_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
return v_res_1080_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1081_, size_t v_sz_1082_, size_t v_i_1083_, lean_object* v_b_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_usize_dec_lt(v_i_1083_, v_sz_1082_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_b_1084_);
return v___x_1094_;
}
else
{
lean_object* v_snd_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1153_; 
v_snd_1095_ = lean_ctor_get(v_b_1084_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_b_1084_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_b_1084_, 0);
lean_dec(v_unused_1154_);
v___x_1097_ = v_b_1084_;
v_isShared_1098_ = v_isSharedCheck_1153_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_snd_1095_);
lean_dec(v_b_1084_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1153_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v_a_1101_; lean_object* v_a_1108_; 
v___x_1099_ = lean_box(0);
v_a_1108_ = lean_array_uget_borrowed(v_as_1081_, v_i_1083_);
if (lean_obj_tag(v_a_1108_) == 0)
{
v_a_1101_ = v_snd_1095_;
goto v___jp_1100_;
}
else
{
lean_object* v_val_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
lean_dec(v_snd_1095_);
v_val_1109_ = lean_ctor_get(v_a_1108_, 0);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_LocalDecl_isAuxDecl(v_val_1109_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_LocalDecl_value_x3f(v_val_1109_, v___x_1111_);
if (lean_obj_tag(v___x_1112_) == 1)
{
lean_object* v_val_1113_; lean_object* v___x_1114_; 
v_val_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1113_, v___y_1089_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1115_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_dec_ref_known(v___x_1116_, 1);
v_a_1101_ = v___x_1110_;
goto v___jp_1100_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1097_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_del_object(v___x_1097_);
v_a_1125_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1114_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1114_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v___x_1112_);
v___x_1133_ = l_Lean_LocalDecl_type(v_val_1109_);
v___x_1134_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1133_, v___y_1089_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1135_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec_ref_known(v___x_1136_, 1);
v_a_1101_ = v___x_1110_;
goto v___jp_1100_;
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_del_object(v___x_1097_);
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
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
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_1097_);
v_a_1145_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1134_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1134_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
v_a_1101_ = v___x_1110_;
goto v___jp_1100_;
}
}
v___jp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 1, v_a_1101_);
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1103_ = v___x_1097_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_a_1101_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
size_t v___x_1104_; size_t v___x_1105_; 
v___x_1104_ = ((size_t)1ULL);
v___x_1105_ = lean_usize_add(v_i_1083_, v___x_1104_);
v_i_1083_ = v___x_1105_;
v_b_1084_ = v___x_1103_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1081_ = stack[0].m_obj;
size_t v_sz_1082_ = stack[1].m_num;
size_t v_i_1083_ = stack[2].m_num;
lean_object* v_b_1084_ = stack[3].m_obj;
lean_object* v___y_1085_ = stack[4].m_obj;
lean_object* v___y_1086_ = stack[5].m_obj;
lean_object* v___y_1087_ = stack[6].m_obj;
lean_object* v___y_1088_ = stack[7].m_obj;
lean_object* v___y_1089_ = stack[8].m_obj;
lean_object* v___y_1090_ = stack[9].m_obj;
lean_object* v___y_1091_ = stack[10].m_obj;
lean_object* v_res_1155_;
v_res_1155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1081_, v_sz_1082_, v_i_1083_, v_b_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
stack->m_obj
 = v_res_1155_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1156_, lean_object* v_sz_1157_, lean_object* v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
size_t v_sz_boxed_1168_; size_t v_i_boxed_1169_; lean_object* v_res_1170_; 
v_sz_boxed_1168_ = lean_unbox_usize(v_sz_1157_);
lean_dec(v_sz_1157_);
v_i_boxed_1169_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_res_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1156_, v_sz_boxed_1168_, v_i_boxed_1169_, v_b_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v_as_1156_);
return v_res_1170_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1171_, size_t v_sz_1172_, size_t v_i_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_lt(v_i_1173_, v_sz_1172_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_b_1174_);
return v___x_1184_;
}
else
{
lean_object* v_snd_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1243_; 
v_snd_1185_ = lean_ctor_get(v_b_1174_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_b_1174_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_b_1174_, 0);
lean_dec(v_unused_1244_);
v___x_1187_ = v_b_1174_;
v_isShared_1188_ = v_isSharedCheck_1243_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_snd_1185_);
lean_dec(v_b_1174_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1243_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v_a_1191_; lean_object* v_a_1198_; 
v___x_1189_ = lean_box(0);
v_a_1198_ = lean_array_uget_borrowed(v_as_1171_, v_i_1173_);
if (lean_obj_tag(v_a_1198_) == 0)
{
v_a_1191_ = v_snd_1185_;
goto v___jp_1190_;
}
else
{
lean_object* v_val_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
lean_dec(v_snd_1185_);
v_val_1199_ = lean_ctor_get(v_a_1198_, 0);
v___x_1200_ = lean_box(0);
v___x_1201_ = l_Lean_LocalDecl_isAuxDecl(v_val_1199_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_LocalDecl_value_x3f(v_val_1199_, v___x_1201_);
if (lean_obj_tag(v___x_1202_) == 1)
{
lean_object* v_val_1203_; lean_object* v___x_1204_; 
v_val_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_val_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1203_, v___y_1179_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1206_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1205_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_dec_ref_known(v___x_1206_, 1);
v_a_1191_ = v___x_1200_;
goto v___jp_1190_;
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_del_object(v___x_1187_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
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
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_del_object(v___x_1187_);
v_a_1215_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1204_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1204_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v___x_1202_);
v___x_1223_ = l_Lean_LocalDecl_type(v_val_1199_);
v___x_1224_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1223_, v___y_1179_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1226_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1225_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_dec_ref_known(v___x_1226_, 1);
v_a_1191_ = v___x_1200_;
goto v___jp_1190_;
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_del_object(v___x_1187_);
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_del_object(v___x_1187_);
v_a_1235_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1224_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1224_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
v_a_1191_ = v___x_1200_;
goto v___jp_1190_;
}
}
v___jp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v_a_1191_);
lean_ctor_set(v___x_1187_, 0, v___x_1189_);
v___x_1193_ = v___x_1187_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_a_1191_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1173_, v___x_1194_);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1171_, v_sz_1172_, v___x_1195_, v___x_1193_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1171_ = stack[0].m_obj;
size_t v_sz_1172_ = stack[1].m_num;
size_t v_i_1173_ = stack[2].m_num;
lean_object* v_b_1174_ = stack[3].m_obj;
lean_object* v___y_1175_ = stack[4].m_obj;
lean_object* v___y_1176_ = stack[5].m_obj;
lean_object* v___y_1177_ = stack[6].m_obj;
lean_object* v___y_1178_ = stack[7].m_obj;
lean_object* v___y_1179_ = stack[8].m_obj;
lean_object* v___y_1180_ = stack[9].m_obj;
lean_object* v___y_1181_ = stack[10].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1171_, v_sz_1172_, v_i_1173_, v_b_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1246_, lean_object* v_sz_1247_, lean_object* v_i_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
size_t v_sz_boxed_1258_; size_t v_i_boxed_1259_; lean_object* v_res_1260_; 
v_sz_boxed_1258_ = lean_unbox_usize(v_sz_1247_);
lean_dec(v_sz_1247_);
v_i_boxed_1259_ = lean_unbox_usize(v_i_1248_);
lean_dec(v_i_1248_);
v_res_1260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1246_, v_sz_boxed_1258_, v_i_boxed_1259_, v_b_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v_as_1246_);
return v_res_1260_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1261_, size_t v_sz_1262_, size_t v_i_1263_, lean_object* v_b_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_lt(v_i_1263_, v_sz_1262_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_b_1264_);
return v___x_1274_;
}
else
{
lean_object* v_snd_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1333_; 
v_snd_1275_ = lean_ctor_get(v_b_1264_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_b_1264_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_b_1264_, 0);
lean_dec(v_unused_1334_);
v___x_1277_ = v_b_1264_;
v_isShared_1278_ = v_isSharedCheck_1333_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_snd_1275_);
lean_dec(v_b_1264_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1333_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v_a_1281_; lean_object* v_a_1288_; 
v___x_1279_ = lean_box(0);
v_a_1288_ = lean_array_uget_borrowed(v_as_1261_, v_i_1263_);
if (lean_obj_tag(v_a_1288_) == 0)
{
v_a_1281_ = v_snd_1275_;
goto v___jp_1280_;
}
else
{
lean_object* v_val_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
lean_dec(v_snd_1275_);
v_val_1289_ = lean_ctor_get(v_a_1288_, 0);
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Lean_LocalDecl_isAuxDecl(v_val_1289_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_LocalDecl_value_x3f(v_val_1289_, v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 1)
{
lean_object* v_val_1293_; lean_object* v___x_1294_; 
v_val_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1294_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1293_, v___y_1269_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1295_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_dec_ref_known(v___x_1296_, 1);
v_a_1281_ = v___x_1290_;
goto v___jp_1280_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_del_object(v___x_1277_);
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_del_object(v___x_1277_);
v_a_1305_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1294_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1294_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec(v___x_1292_);
v___x_1313_ = l_Lean_LocalDecl_type(v_val_1289_);
v___x_1314_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1313_, v___y_1269_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1315_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_dec_ref_known(v___x_1316_, 1);
v_a_1281_ = v___x_1290_;
goto v___jp_1280_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1277_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_del_object(v___x_1277_);
v_a_1325_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1314_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1314_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
else
{
v_a_1281_ = v___x_1290_;
goto v___jp_1280_;
}
}
v___jp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_a_1281_);
lean_ctor_set(v___x_1277_, 0, v___x_1279_);
v___x_1283_ = v___x_1277_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_a_1281_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
size_t v___x_1284_; size_t v___x_1285_; 
v___x_1284_ = ((size_t)1ULL);
v___x_1285_ = lean_usize_add(v_i_1263_, v___x_1284_);
v_i_1263_ = v___x_1285_;
v_b_1264_ = v___x_1283_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1261_ = stack[0].m_obj;
size_t v_sz_1262_ = stack[1].m_num;
size_t v_i_1263_ = stack[2].m_num;
lean_object* v_b_1264_ = stack[3].m_obj;
lean_object* v___y_1265_ = stack[4].m_obj;
lean_object* v___y_1266_ = stack[5].m_obj;
lean_object* v___y_1267_ = stack[6].m_obj;
lean_object* v___y_1268_ = stack[7].m_obj;
lean_object* v___y_1269_ = stack[8].m_obj;
lean_object* v___y_1270_ = stack[9].m_obj;
lean_object* v___y_1271_ = stack[10].m_obj;
lean_object* v_res_1335_;
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1261_, v_sz_1262_, v_i_1263_, v_b_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
stack->m_obj
 = v_res_1335_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1336_, lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1336_, v_sz_boxed_1348_, v_i_boxed_1349_, v_b_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v_as_1336_);
return v_res_1350_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1351_, size_t v_sz_1352_, size_t v_i_1353_, lean_object* v_b_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_lt(v_i_1353_, v_sz_1352_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_b_1354_);
return v___x_1364_;
}
else
{
lean_object* v_snd_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1423_; 
v_snd_1365_ = lean_ctor_get(v_b_1354_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_b_1354_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_b_1354_, 0);
lean_dec(v_unused_1424_);
v___x_1367_ = v_b_1354_;
v_isShared_1368_ = v_isSharedCheck_1423_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snd_1365_);
lean_dec(v_b_1354_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1423_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v_a_1371_; lean_object* v_a_1378_; 
v___x_1369_ = lean_box(0);
v_a_1378_ = lean_array_uget_borrowed(v_as_1351_, v_i_1353_);
if (lean_obj_tag(v_a_1378_) == 0)
{
v_a_1371_ = v_snd_1365_;
goto v___jp_1370_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
lean_dec(v_snd_1365_);
v_val_1379_ = lean_ctor_get(v_a_1378_, 0);
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Lean_LocalDecl_isAuxDecl(v_val_1379_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_LocalDecl_value_x3f(v_val_1379_, v___x_1381_);
if (lean_obj_tag(v___x_1382_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1384_; 
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1383_, v___y_1359_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1385_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_dec_ref_known(v___x_1386_, 1);
v_a_1371_ = v___x_1380_;
goto v___jp_1370_;
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_del_object(v___x_1367_);
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_del_object(v___x_1367_);
v_a_1395_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1384_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1384_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v___x_1382_);
v___x_1403_ = l_Lean_LocalDecl_type(v_val_1379_);
v___x_1404_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1403_, v___y_1359_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1405_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec_ref_known(v___x_1406_, 1);
v_a_1371_ = v___x_1380_;
goto v___jp_1370_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_del_object(v___x_1367_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_del_object(v___x_1367_);
v_a_1415_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1404_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1404_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
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
v_a_1371_ = v___x_1380_;
goto v___jp_1370_;
}
}
v___jp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v_a_1371_);
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1373_ = v___x_1367_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_a_1371_);
v___x_1373_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_i_1353_, v___x_1374_);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1351_, v_sz_1352_, v___x_1375_, v___x_1373_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1351_ = stack[0].m_obj;
size_t v_sz_1352_ = stack[1].m_num;
size_t v_i_1353_ = stack[2].m_num;
lean_object* v_b_1354_ = stack[3].m_obj;
lean_object* v___y_1355_ = stack[4].m_obj;
lean_object* v___y_1356_ = stack[5].m_obj;
lean_object* v___y_1357_ = stack[6].m_obj;
lean_object* v___y_1358_ = stack[7].m_obj;
lean_object* v___y_1359_ = stack[8].m_obj;
lean_object* v___y_1360_ = stack[9].m_obj;
lean_object* v___y_1361_ = stack[10].m_obj;
lean_object* v_res_1425_;
v_res_1425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1351_, v_sz_1352_, v_i_1353_, v_b_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
stack->m_obj
 = v_res_1425_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1426_, lean_object* v_sz_1427_, lean_object* v_i_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
size_t v_sz_boxed_1438_; size_t v_i_boxed_1439_; lean_object* v_res_1440_; 
v_sz_boxed_1438_ = lean_unbox_usize(v_sz_1427_);
lean_dec(v_sz_1427_);
v_i_boxed_1439_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1426_, v_sz_boxed_1438_, v_i_boxed_1439_, v_b_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v_as_1426_);
return v_res_1440_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_init_1441_, lean_object* v_n_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
if (lean_obj_tag(v_n_1442_) == 0)
{
lean_object* v_cs_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; size_t v_sz_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v_cs_1452_ = lean_ctor_get(v_n_1442_, 0);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v_b_1443_);
v_sz_1455_ = lean_array_size(v_cs_1452_);
v___x_1456_ = ((size_t)0ULL);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1441_, v_cs_1452_, v_sz_1455_, v___x_1456_, v___x_1454_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1472_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1472_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1472_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v_fst_1462_; 
v_fst_1462_ = lean_ctor_get(v_a_1458_, 0);
if (lean_obj_tag(v_fst_1462_) == 0)
{
lean_object* v_snd_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v_snd_1463_ = lean_ctor_get(v_a_1458_, 1);
lean_inc(v_snd_1463_);
lean_dec(v_a_1458_);
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_snd_1463_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1464_);
v___x_1466_ = v___x_1460_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
else
{
lean_object* v_val_1468_; lean_object* v___x_1470_; 
lean_inc_ref(v_fst_1462_);
lean_dec(v_a_1458_);
v_val_1468_ = lean_ctor_get(v_fst_1462_, 0);
lean_inc(v_val_1468_);
lean_dec_ref_known(v_fst_1462_, 1);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_val_1468_);
v___x_1470_ = v___x_1460_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_val_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1457_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1457_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_vs_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; size_t v_sz_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v_vs_1481_ = lean_ctor_get(v_n_1442_, 0);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v_b_1443_);
v_sz_1484_ = lean_array_size(v_vs_1481_);
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1481_, v_sz_1484_, v___x_1485_, v___x_1483_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1501_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1501_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1501_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_fst_1491_; 
v_fst_1491_ = lean_ctor_get(v_a_1487_, 0);
if (lean_obj_tag(v_fst_1491_) == 0)
{
lean_object* v_snd_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v_snd_1492_ = lean_ctor_get(v_a_1487_, 1);
lean_inc(v_snd_1492_);
lean_dec(v_a_1487_);
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_snd_1492_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1493_);
v___x_1495_ = v___x_1489_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
else
{
lean_object* v_val_1497_; lean_object* v___x_1499_; 
lean_inc_ref(v_fst_1491_);
lean_dec(v_a_1487_);
v_val_1497_ = lean_ctor_get(v_fst_1491_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v_fst_1491_, 1);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v_val_1497_);
v___x_1499_ = v___x_1489_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_val_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1486_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1486_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1441_ = stack[0].m_obj;
lean_object* v_n_1442_ = stack[1].m_obj;
lean_object* v_b_1443_ = stack[2].m_obj;
lean_object* v___y_1444_ = stack[3].m_obj;
lean_object* v___y_1445_ = stack[4].m_obj;
lean_object* v___y_1446_ = stack[5].m_obj;
lean_object* v___y_1447_ = stack[6].m_obj;
lean_object* v___y_1448_ = stack[7].m_obj;
lean_object* v___y_1449_ = stack[8].m_obj;
lean_object* v___y_1450_ = stack[9].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1441_, v_n_1442_, v_b_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
stack->m_obj
 = v_res_1510_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_init_1511_, lean_object* v_as_1512_, size_t v_sz_1513_, size_t v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_lt(v_i_1514_, v_sz_1513_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1515_);
return v___x_1525_;
}
else
{
lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1560_; 
v_snd_1526_ = lean_ctor_get(v_b_1515_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_b_1515_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_b_1515_, 0);
lean_dec(v_unused_1561_);
v___x_1528_ = v_b_1515_;
v_isShared_1529_ = v_isSharedCheck_1560_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_dec(v_b_1515_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1560_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v_a_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_box(0);
v_a_1531_ = lean_array_uget_borrowed(v_as_1512_, v_i_1514_);
lean_inc(v_snd_1526_);
v___x_1532_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1511_, v_a_1531_, v_snd_1526_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1551_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1551_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1551_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
if (lean_obj_tag(v_a_1533_) == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1533_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1537_);
v___x_1539_ = v___x_1528_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_snd_1526_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1541_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1539_);
v___x_1541_ = v___x_1535_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; 
lean_del_object(v___x_1535_);
lean_dec(v_snd_1526_);
v_a_1544_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v_a_1533_, 1);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_a_1544_);
lean_ctor_set(v___x_1528_, 0, v___x_1530_);
v___x_1546_ = v___x_1528_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_a_1544_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
size_t v___x_1547_; size_t v___x_1548_; 
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1514_, v___x_1547_);
v_i_1514_ = v___x_1548_;
v_b_1515_ = v___x_1546_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_del_object(v___x_1528_);
lean_dec(v_snd_1526_);
v_a_1552_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1532_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1532_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1511_ = stack[0].m_obj;
lean_object* v_as_1512_ = stack[1].m_obj;
size_t v_sz_1513_ = stack[2].m_num;
size_t v_i_1514_ = stack[3].m_num;
lean_object* v_b_1515_ = stack[4].m_obj;
lean_object* v___y_1516_ = stack[5].m_obj;
lean_object* v___y_1517_ = stack[6].m_obj;
lean_object* v___y_1518_ = stack[7].m_obj;
lean_object* v___y_1519_ = stack[8].m_obj;
lean_object* v___y_1520_ = stack[9].m_obj;
lean_object* v___y_1521_ = stack[10].m_obj;
lean_object* v___y_1522_ = stack[11].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1511_, v_as_1512_, v_sz_1513_, v_i_1514_, v_b_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1563_, lean_object* v_as_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
size_t v_sz_boxed_1576_; size_t v_i_boxed_1577_; lean_object* v_res_1578_; 
v_sz_boxed_1576_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1577_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1563_, v_as_1564_, v_sz_boxed_1576_, v_i_boxed_1577_, v_b_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v_as_1564_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_init_1579_, lean_object* v_n_1580_, lean_object* v_b_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1579_, v_n_1580_, v_b_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v_n_1580_);
return v_res_1590_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1591_, lean_object* v_init_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_root_1601_; lean_object* v_tail_1602_; lean_object* v___x_1603_; 
v_root_1601_ = lean_ctor_get(v_t_1591_, 0);
v_tail_1602_ = lean_ctor_get(v_t_1591_, 1);
v___x_1603_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1592_, v_root_1601_, v_init_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1640_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1640_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1640_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
if (lean_obj_tag(v_a_1604_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; 
v_a_1608_ = lean_ctor_get(v_a_1604_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v_a_1604_, 1);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v_a_1608_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; size_t v_sz_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
lean_del_object(v___x_1606_);
v_a_1612_ = lean_ctor_get(v_a_1604_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v_a_1604_, 1);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v_a_1612_);
v_sz_1615_ = lean_array_size(v_tail_1602_);
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1602_, v_sz_1615_, v___x_1616_, v___x_1614_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1631_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_fst_1622_; 
v_fst_1622_ = lean_ctor_get(v_a_1618_, 0);
if (lean_obj_tag(v_fst_1622_) == 0)
{
lean_object* v_snd_1623_; lean_object* v___x_1625_; 
v_snd_1623_ = lean_ctor_get(v_a_1618_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_a_1618_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_snd_1623_);
v___x_1625_ = v___x_1620_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_snd_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v_val_1627_; lean_object* v___x_1629_; 
lean_inc_ref(v_fst_1622_);
lean_dec(v_a_1618_);
v_val_1627_ = lean_ctor_get(v_fst_1622_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v_fst_1622_, 1);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_val_1627_);
v___x_1629_ = v___x_1620_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_val_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1617_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1617_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1603_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1603_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1591_ = stack[0].m_obj;
lean_object* v_init_1592_ = stack[1].m_obj;
lean_object* v___y_1593_ = stack[2].m_obj;
lean_object* v___y_1594_ = stack[3].m_obj;
lean_object* v___y_1595_ = stack[4].m_obj;
lean_object* v___y_1596_ = stack[5].m_obj;
lean_object* v___y_1597_ = stack[6].m_obj;
lean_object* v___y_1598_ = stack[7].m_obj;
lean_object* v___y_1599_ = stack[8].m_obj;
lean_object* v_res_1649_;
v_res_1649_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1591_, v_init_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
stack->m_obj
 = v_res_1649_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1650_, lean_object* v_init_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1650_, v_init_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v_t_1650_);
return v_res_1660_;
}
}
lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_lctx_1670_; lean_object* v_decls_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_lctx_1670_ = lean_ctor_get(v_a_1665_, 2);
v_decls_1671_ = lean_ctor_get(v_lctx_1670_, 1);
v___x_1672_ = lean_box(0);
v___x_1673_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1671_, v___x_1672_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref_known(v___x_1673_, 1);
v___x_1674_ = l_Lean_MVarId_getType(v_mvarId_1661_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
v___x_1676_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1675_, v_a_1666_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1677_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
return v___x_1678_;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1676_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1676_);
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
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_a_1687_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1674_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1674_);
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
else
{
lean_dec(v_mvarId_1661_);
return v___x_1673_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1661_ = stack[0].m_obj;
lean_object* v_a_1662_ = stack[1].m_obj;
lean_object* v_a_1663_ = stack[2].m_obj;
lean_object* v_a_1664_ = stack[3].m_obj;
lean_object* v_a_1665_ = stack[4].m_obj;
lean_object* v_a_1666_ = stack[5].m_obj;
lean_object* v_a_1667_ = stack[6].m_obj;
lean_object* v_a_1668_ = stack[7].m_obj;
lean_object* v_res_1695_;
v_res_1695_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
stack->m_obj
 = v_res_1695_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
return v_res_1705_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1713_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1713_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1706_ = stack[0].m_obj;
lean_object* v_x_1707_ = stack[1].m_obj;
lean_object* v___y_1708_ = stack[2].m_obj;
lean_object* v___y_1709_ = stack[3].m_obj;
lean_object* v___y_1710_ = stack[4].m_obj;
lean_object* v___y_1711_ = stack[5].m_obj;
lean_object* v_res_1730_;
v_res_1730_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
stack->m_obj
 = v_res_1730_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1731_, lean_object* v_x_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1731_, v_x_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1738_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1739_, lean_object* v_mvarId_1740_, lean_object* v_x_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1740_, v_x_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1740_ = stack[1].m_obj;
lean_object* v_x_1741_ = stack[2].m_obj;
lean_object* v___y_1742_ = stack[3].m_obj;
lean_object* v___y_1743_ = stack[4].m_obj;
lean_object* v___y_1744_ = stack[5].m_obj;
lean_object* v___y_1745_ = stack[6].m_obj;
lean_object* v_res_1748_;
v_res_1748_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_box(0), v_mvarId_1740_, v_x_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
stack->m_obj
 = v_res_1748_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1749_, lean_object* v_mvarId_1750_, lean_object* v_x_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1749_, v_mvarId_1750_, v_x_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1757_;
}
}
lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1758_, lean_object* v___x_1759_, lean_object* v_mvarId_1760_, lean_object* v_needle_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_st_mk_ref(v___x_1758_);
v___x_1768_ = lean_st_mk_ref(v___x_1759_);
v___x_1769_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1760_, v___x_1768_, v_needle_1761_, v___x_1767_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1779_; 
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v___x_1769_, 0);
lean_dec(v_unused_1780_);
v___x_1771_ = v___x_1769_;
v_isShared_1772_ = v_isSharedCheck_1779_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v___x_1769_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1779_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_calls_1775_; lean_object* v___x_1777_; 
v___x_1773_ = lean_st_ref_get(v___x_1768_);
lean_dec(v___x_1768_);
lean_dec(v___x_1773_);
v___x_1774_ = lean_st_ref_get(v___x_1767_);
lean_dec(v___x_1767_);
v_calls_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_ref(v_calls_1775_);
lean_dec(v___x_1774_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v_calls_1775_);
v___x_1777_ = v___x_1771_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_calls_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v___x_1768_);
lean_dec(v___x_1767_);
v_a_1781_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1769_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1769_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_Collector_main___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1758_ = stack[0].m_obj;
lean_object* v___x_1759_ = stack[1].m_obj;
lean_object* v_mvarId_1760_ = stack[2].m_obj;
lean_object* v_needle_1761_ = stack[3].m_obj;
lean_object* v___y_1762_ = stack[4].m_obj;
lean_object* v___y_1763_ = stack[5].m_obj;
lean_object* v___y_1764_ = stack[6].m_obj;
lean_object* v___y_1765_ = stack[7].m_obj;
lean_object* v_res_1789_;
v_res_1789_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1758_, v___x_1759_, v_mvarId_1760_, v_needle_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
stack->m_obj
 = v_res_1789_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1790_, lean_object* v___x_1791_, lean_object* v_mvarId_1792_, lean_object* v_needle_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1790_, v___x_1791_, v_mvarId_1792_, v_needle_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v_needle_1793_);
return v_res_1799_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_unsigned_to_nat(64u);
v___x_1801_ = l_Lean_mkPtrSet___redArg(v___x_1800_);
return v___x_1801_;
}
}
lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1802_, lean_object* v_mvarId_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___f_1811_; lean_object* v___x_1812_; 
v___x_1809_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_1810_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
lean_inc(v_mvarId_1803_);
v___f_1811_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1811_, 0, v___x_1810_);
lean_closure_set(v___f_1811_, 1, v___x_1809_);
lean_closure_set(v___f_1811_, 2, v_mvarId_1803_);
lean_closure_set(v___f_1811_, 3, v_needle_1802_);
v___x_1812_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1803_, v___f_1811_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
return v___x_1812_;
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_Collector_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_needle_1802_ = stack[0].m_obj;
lean_object* v_mvarId_1803_ = stack[1].m_obj;
lean_object* v_a_1804_ = stack[2].m_obj;
lean_object* v_a_1805_ = stack[3].m_obj;
lean_object* v_a_1806_ = stack[4].m_obj;
lean_object* v_a_1807_ = stack[5].m_obj;
lean_object* v_res_1813_;
v_res_1813_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1802_, v_mvarId_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
stack->m_obj
 = v_res_1813_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_1814_, lean_object* v_mvarId_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1814_, v_mvarId_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1821_;
}
}
lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_1822_, lean_object* v_mvarId_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1822_, v_mvarId_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_needle_1822_ = stack[0].m_obj;
lean_object* v_mvarId_1823_ = stack[1].m_obj;
lean_object* v_a_1824_ = stack[2].m_obj;
lean_object* v_a_1825_ = stack[3].m_obj;
lean_object* v_a_1826_ = stack[4].m_obj;
lean_object* v_a_1827_ = stack[5].m_obj;
lean_object* v_res_1830_;
v_res_1830_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1822_, v_mvarId_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
stack->m_obj
 = v_res_1830_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_1831_, lean_object* v_mvarId_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1831_, v_mvarId_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1838_;
}
}
lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_1839_, lean_object* v_mvarId_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1839_, v_mvarId_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT void l_Lean_Meta_FunInd_collect_0interp(lean_interpreter_value* stack)
{
lean_object* v_needle_1839_ = stack[0].m_obj;
lean_object* v_mvarId_1840_ = stack[1].m_obj;
lean_object* v_a_1841_ = stack[2].m_obj;
lean_object* v_a_1842_ = stack[3].m_obj;
lean_object* v_a_1843_ = stack[4].m_obj;
lean_object* v_a_1844_ = stack[5].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l_Lean_Meta_FunInd_collect(v_needle_1839_, v_mvarId_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_1848_, lean_object* v_mvarId_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Meta_FunInd_collect(v_needle_1848_, v_mvarId_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1855_;
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
