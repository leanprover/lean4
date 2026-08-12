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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* v_key_108_; lean_object* v_value_109_; lean_object* v_tail_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_153_; 
v_key_108_ = lean_ctor_get(v_x_107_, 0);
v_value_109_ = lean_ctor_get(v_x_107_, 1);
v_tail_110_ = lean_ctor_get(v_x_107_, 2);
v_isSharedCheck_153_ = !lean_is_exclusive(v_x_107_);
if (v_isSharedCheck_153_ == 0)
{
v___x_112_ = v_x_107_;
v_isShared_113_ = v_isSharedCheck_153_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_tail_110_);
lean_inc(v_value_109_);
lean_inc(v_key_108_);
lean_dec(v_x_107_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_153_;
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
uint64_t v___x_151_; 
v___x_151_ = 1723ULL;
v___y_139_ = v___x_151_;
goto v___jp_138_;
}
else
{
uint64_t v_hash_152_; 
v_hash_152_ = lean_ctor_get_uint64(v_fst_114_, sizeof(void*)*2);
v___y_139_ = v_hash_152_;
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
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_le(v___x_142_, v___x_142_);
if (v___x_144_ == 0)
{
if (v___x_143_ == 0)
{
v___y_118_ = v___y_139_;
v___y_119_ = v___x_140_;
goto v___jp_117_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint64_t v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_142_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_115_, v___x_145_, v___x_146_, v___x_140_);
v___y_118_ = v___y_139_;
v___y_119_ = v___x_147_;
goto v___jp_117_;
}
}
else
{
size_t v___x_148_; size_t v___x_149_; uint64_t v___x_150_; 
v___x_148_ = ((size_t)0ULL);
v___x_149_ = lean_usize_of_nat(v___x_142_);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_115_, v___x_148_, v___x_149_, v___x_140_);
v___y_118_ = v___y_139_;
v___y_119_ = v___x_150_;
goto v___jp_117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(lean_object* v_i_154_, lean_object* v_source_155_, lean_object* v_target_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_array_get_size(v_source_155_);
v___x_158_ = lean_nat_dec_lt(v_i_154_, v___x_157_);
if (v___x_158_ == 0)
{
lean_dec_ref(v_source_155_);
lean_dec(v_i_154_);
return v_target_156_;
}
else
{
lean_object* v_es_159_; lean_object* v___x_160_; lean_object* v_source_161_; lean_object* v_target_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_es_159_ = lean_array_fget(v_source_155_, v_i_154_);
v___x_160_ = lean_box(0);
v_source_161_ = lean_array_fset(v_source_155_, v_i_154_, v___x_160_);
v_target_162_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_target_156_, v_es_159_);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_i_154_, v___x_163_);
lean_dec(v_i_154_);
v_i_154_ = v___x_164_;
v_source_155_ = v_source_161_;
v_target_156_ = v_target_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(lean_object* v_data_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_nbuckets_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_167_ = lean_array_get_size(v_data_166_);
v___x_168_ = lean_unsigned_to_nat(2u);
v_nbuckets_169_ = lean_nat_mul(v___x_167_, v___x_168_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_box(0);
v___x_172_ = lean_mk_array(v_nbuckets_169_, v___x_171_);
v___x_173_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_170_, v_data_166_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object* v_m_174_, lean_object* v_a_175_, lean_object* v_b_176_){
_start:
{
lean_object* v_size_177_; lean_object* v_buckets_178_; lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v___x_181_; uint64_t v___y_183_; uint64_t v___y_184_; uint64_t v___y_223_; 
v_size_177_ = lean_ctor_get(v_m_174_, 0);
v_buckets_178_ = lean_ctor_get(v_m_174_, 1);
v_fst_179_ = lean_ctor_get(v_a_175_, 0);
v_snd_180_ = lean_ctor_get(v_a_175_, 1);
v___x_181_ = lean_array_get_size(v_buckets_178_);
if (lean_obj_tag(v_fst_179_) == 0)
{
uint64_t v___x_235_; 
v___x_235_ = 1723ULL;
v___y_223_ = v___x_235_;
goto v___jp_222_;
}
else
{
uint64_t v_hash_236_; 
v_hash_236_ = lean_ctor_get_uint64(v_fst_179_, sizeof(void*)*2);
v___y_223_ = v_hash_236_;
goto v___jp_222_;
}
v___jp_182_:
{
uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v_fold_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v_bkt_197_; uint8_t v___x_198_; 
v___x_185_ = lean_uint64_mix_hash(v___y_183_, v___y_184_);
v___x_186_ = 32ULL;
v___x_187_ = lean_uint64_shift_right(v___x_185_, v___x_186_);
v_fold_188_ = lean_uint64_xor(v___x_185_, v___x_187_);
v___x_189_ = 16ULL;
v___x_190_ = lean_uint64_shift_right(v_fold_188_, v___x_189_);
v___x_191_ = lean_uint64_xor(v_fold_188_, v___x_190_);
v___x_192_ = lean_uint64_to_usize(v___x_191_);
v___x_193_ = lean_usize_of_nat(v___x_181_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v___x_193_, v___x_194_);
v___x_196_ = lean_usize_land(v___x_192_, v___x_195_);
v_bkt_197_ = lean_array_uget_borrowed(v_buckets_178_, v___x_196_);
v___x_198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_175_, v_bkt_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_219_; 
lean_inc_ref(v_buckets_178_);
lean_inc(v_size_177_);
v_isSharedCheck_219_ = !lean_is_exclusive(v_m_174_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; lean_object* v_unused_221_; 
v_unused_220_ = lean_ctor_get(v_m_174_, 1);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_m_174_, 0);
lean_dec(v_unused_221_);
v___x_200_ = v_m_174_;
v_isShared_201_ = v_isSharedCheck_219_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_m_174_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_219_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v_size_x27_203_; lean_object* v___x_204_; lean_object* v_buckets_x27_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v_size_x27_203_ = lean_nat_add(v_size_177_, v___x_202_);
lean_dec(v_size_177_);
lean_inc(v_bkt_197_);
v___x_204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_204_, 0, v_a_175_);
lean_ctor_set(v___x_204_, 1, v_b_176_);
lean_ctor_set(v___x_204_, 2, v_bkt_197_);
v_buckets_x27_205_ = lean_array_uset(v_buckets_178_, v___x_196_, v___x_204_);
v___x_206_ = lean_unsigned_to_nat(4u);
v___x_207_ = lean_nat_mul(v_size_x27_203_, v___x_206_);
v___x_208_ = lean_unsigned_to_nat(3u);
v___x_209_ = lean_nat_div(v___x_207_, v___x_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_array_get_size(v_buckets_x27_205_);
v___x_211_ = lean_nat_dec_le(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
if (v___x_211_ == 0)
{
lean_object* v_val_212_; lean_object* v___x_214_; 
v_val_212_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_205_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 1, v_val_212_);
lean_ctor_set(v___x_200_, 0, v_size_x27_203_);
v___x_214_ = v___x_200_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_size_x27_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_val_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
else
{
lean_object* v___x_217_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 1, v_buckets_x27_205_);
lean_ctor_set(v___x_200_, 0, v_size_x27_203_);
v___x_217_ = v___x_200_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_size_x27_203_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_buckets_x27_205_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_dec(v_b_176_);
lean_dec_ref(v_a_175_);
return v_m_174_;
}
}
v___jp_222_:
{
uint64_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_224_ = 7ULL;
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_array_get_size(v_snd_180_);
v___x_227_ = lean_nat_dec_lt(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
v___y_183_ = v___y_223_;
v___y_184_ = v___x_224_;
goto v___jp_182_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = lean_nat_dec_le(v___x_226_, v___x_226_);
if (v___x_228_ == 0)
{
if (v___x_227_ == 0)
{
v___y_183_ = v___y_223_;
v___y_184_ = v___x_224_;
goto v___jp_182_;
}
else
{
size_t v___x_229_; size_t v___x_230_; uint64_t v___x_231_; 
v___x_229_ = ((size_t)0ULL);
v___x_230_ = lean_usize_of_nat(v___x_226_);
v___x_231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_180_, v___x_229_, v___x_230_, v___x_224_);
v___y_183_ = v___y_223_;
v___y_184_ = v___x_231_;
goto v___jp_182_;
}
}
else
{
size_t v___x_232_; size_t v___x_233_; uint64_t v___x_234_; 
v___x_232_ = ((size_t)0ULL);
v___x_233_ = lean_usize_of_nat(v___x_226_);
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_180_, v___x_232_, v___x_233_, v___x_224_);
v___y_183_ = v___y_223_;
v___y_184_ = v___x_234_;
goto v___jp_182_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object* v_m_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_buckets_239_; lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v___x_242_; uint64_t v___y_244_; uint64_t v___y_245_; uint64_t v___y_261_; 
v_buckets_239_ = lean_ctor_get(v_m_237_, 1);
v_fst_240_ = lean_ctor_get(v_a_238_, 0);
v_snd_241_ = lean_ctor_get(v_a_238_, 1);
v___x_242_ = lean_array_get_size(v_buckets_239_);
if (lean_obj_tag(v_fst_240_) == 0)
{
uint64_t v___x_273_; 
v___x_273_ = 1723ULL;
v___y_261_ = v___x_273_;
goto v___jp_260_;
}
else
{
uint64_t v_hash_274_; 
v_hash_274_ = lean_ctor_get_uint64(v_fst_240_, sizeof(void*)*2);
v___y_261_ = v_hash_274_;
goto v___jp_260_;
}
v___jp_243_:
{
uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v_fold_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_246_ = lean_uint64_mix_hash(v___y_244_, v___y_245_);
v___x_247_ = 32ULL;
v___x_248_ = lean_uint64_shift_right(v___x_246_, v___x_247_);
v_fold_249_ = lean_uint64_xor(v___x_246_, v___x_248_);
v___x_250_ = 16ULL;
v___x_251_ = lean_uint64_shift_right(v_fold_249_, v___x_250_);
v___x_252_ = lean_uint64_xor(v_fold_249_, v___x_251_);
v___x_253_ = lean_uint64_to_usize(v___x_252_);
v___x_254_ = lean_usize_of_nat(v___x_242_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_sub(v___x_254_, v___x_255_);
v___x_257_ = lean_usize_land(v___x_253_, v___x_256_);
v___x_258_ = lean_array_uget_borrowed(v_buckets_239_, v___x_257_);
v___x_259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_238_, v___x_258_);
return v___x_259_;
}
v___jp_260_:
{
uint64_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_262_ = 7ULL;
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_array_get_size(v_snd_241_);
v___x_265_ = lean_nat_dec_lt(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
v___y_244_ = v___y_261_;
v___y_245_ = v___x_262_;
goto v___jp_243_;
}
else
{
uint8_t v___x_266_; 
v___x_266_ = lean_nat_dec_le(v___x_264_, v___x_264_);
if (v___x_266_ == 0)
{
if (v___x_265_ == 0)
{
v___y_244_ = v___y_261_;
v___y_245_ = v___x_262_;
goto v___jp_243_;
}
else
{
size_t v___x_267_; size_t v___x_268_; uint64_t v___x_269_; 
v___x_267_ = ((size_t)0ULL);
v___x_268_ = lean_usize_of_nat(v___x_264_);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_241_, v___x_267_, v___x_268_, v___x_262_);
v___y_244_ = v___y_261_;
v___y_245_ = v___x_269_;
goto v___jp_243_;
}
}
else
{
size_t v___x_270_; size_t v___x_271_; uint64_t v___x_272_; 
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_264_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_241_, v___x_270_, v___x_271_, v___x_262_);
v___y_244_ = v___y_261_;
v___y_245_ = v___x_272_;
goto v___jp_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object* v_m_275_, lean_object* v_a_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_275_, v_a_276_);
lean_dec_ref(v_a_276_);
lean_dec_ref(v_m_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object* v_calls_279_, lean_object* v_as_280_, size_t v_sz_281_, size_t v_i_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_a_286_; uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_lt(v_i_282_, v_sz_281_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
lean_dec_ref(v_calls_279_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v_b_283_);
return v___x_291_;
}
else
{
lean_object* v_snd_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_349_; 
v_snd_292_ = lean_ctor_get(v_b_283_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_b_283_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_b_283_, 0);
lean_dec(v_unused_350_);
v___x_294_ = v_b_283_;
v_isShared_295_ = v_isSharedCheck_349_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_snd_292_);
lean_dec(v_b_283_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_349_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_snd_296_; lean_object* v_fst_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_348_; 
v_snd_296_ = lean_ctor_get(v_snd_292_, 1);
v_fst_297_ = lean_ctor_get(v_snd_292_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_snd_292_);
if (v_isSharedCheck_348_ == 0)
{
v___x_299_ = v_snd_292_;
v_isShared_300_ = v_isSharedCheck_348_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_snd_296_);
lean_inc(v_fst_297_);
lean_dec(v_snd_292_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_348_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_array_301_; lean_object* v_start_302_; lean_object* v_stop_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_array_301_ = lean_ctor_get(v_snd_296_, 0);
v_start_302_ = lean_ctor_get(v_snd_296_, 1);
v_stop_303_ = lean_ctor_get(v_snd_296_, 2);
v___x_304_ = lean_box(0);
v___x_305_ = lean_nat_dec_lt(v_start_302_, v_stop_303_);
if (v___x_305_ == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v_calls_279_);
if (v_isShared_300_ == 0)
{
v___x_307_ = v___x_299_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_fst_297_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_snd_296_);
v___x_307_ = v_reuseFailAlloc_312_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v___x_307_);
lean_ctor_set(v___x_294_, 0, v___x_304_);
v___x_309_ = v___x_294_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_311_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
}
else
{
lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_344_; 
lean_inc(v_stop_303_);
lean_inc(v_start_302_);
lean_inc_ref(v_array_301_);
v_isSharedCheck_344_ = !lean_is_exclusive(v_snd_296_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_345_ = lean_ctor_get(v_snd_296_, 2);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_snd_296_, 1);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_snd_296_, 0);
lean_dec(v_unused_347_);
v___x_314_ = v_snd_296_;
v_isShared_315_ = v_isSharedCheck_344_;
goto v_resetjp_313_;
}
else
{
lean_dec(v_snd_296_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_344_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_a_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v_a_316_ = lean_array_uget_borrowed(v_as_280_, v_i_282_);
v___x_317_ = lean_array_fget(v_array_301_, v_start_302_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_start_302_, v___x_318_);
lean_dec(v_start_302_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_319_);
v___x_321_ = v___x_314_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_array_301_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_stop_303_);
v___x_321_ = v_reuseFailAlloc_343_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
uint8_t v___x_337_; 
v___x_337_ = lean_unbox(v___x_317_);
if (v___x_337_ == 2)
{
uint8_t v___x_338_; 
v___x_338_ = l_Lean_Expr_isFVar(v_a_316_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec(v___x_317_);
lean_del_object(v___x_299_);
lean_del_object(v___x_294_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_calls_279_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v_fst_297_);
lean_ctor_set(v___x_340_, 1, v___x_321_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
else
{
goto v___jp_322_;
}
}
else
{
goto v___jp_322_;
}
v___jp_322_:
{
uint8_t v___x_323_; 
v___x_323_ = lean_unbox(v___x_317_);
lean_dec(v___x_317_);
if (v___x_323_ == 0)
{
lean_object* v___x_325_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_321_);
v___x_325_ = v___x_299_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_fst_297_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_321_);
v___x_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v___x_325_);
lean_ctor_set(v___x_294_, 0, v___x_304_);
v___x_327_ = v___x_294_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v_a_286_ = v___x_327_;
goto v___jp_285_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_332_; 
lean_inc(v_a_316_);
v___x_330_ = lean_array_push(v_fst_297_, v_a_316_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_321_);
lean_ctor_set(v___x_299_, 0, v___x_330_);
v___x_332_ = v___x_299_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_321_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v___x_332_);
lean_ctor_set(v___x_294_, 0, v___x_304_);
v___x_334_ = v___x_294_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
v_a_286_ = v___x_334_;
goto v___jp_285_;
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
v___jp_285_:
{
size_t v___x_287_; size_t v___x_288_; 
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_i_282_, v___x_287_);
v_i_282_ = v___x_288_;
v_b_283_ = v_a_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object* v_calls_351_, lean_object* v_as_352_, lean_object* v_sz_353_, lean_object* v_i_354_, lean_object* v_b_355_, lean_object* v___y_356_){
_start:
{
size_t v_sz_boxed_357_; size_t v_i_boxed_358_; lean_object* v_res_359_; 
v_sz_boxed_357_ = lean_unbox_usize(v_sz_353_);
lean_dec(v_sz_353_);
v_i_boxed_358_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_351_, v_as_352_, v_sz_boxed_357_, v_i_boxed_358_, v_b_355_);
lean_dec_ref(v_as_352_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object* v_e_360_, lean_object* v_funIndInfo_361_, lean_object* v_args_362_, lean_object* v_calls_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_funName_369_; lean_object* v_params_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_funName_369_ = lean_ctor_get(v_funIndInfo_361_, 0);
lean_inc(v_funName_369_);
v_params_370_ = lean_ctor_get(v_funIndInfo_361_, 3);
lean_inc_ref(v_params_370_);
lean_dec_ref(v_funIndInfo_361_);
v___x_371_ = lean_array_get_size(v_params_370_);
v___x_372_ = lean_array_get_size(v_args_362_);
v___x_373_ = lean_nat_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec_ref(v_params_370_);
lean_dec(v_funName_369_);
lean_dec_ref(v_e_360_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_calls_363_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; lean_object* v_keys_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; size_t v_sz_381_; size_t v___x_382_; lean_object* v___x_383_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v_keys_376_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_377_ = l_Array_toSubarray___redArg(v_params_370_, v___x_375_, v___x_371_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_keys_376_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v_sz_381_ = lean_array_size(v_args_362_);
v___x_382_ = ((size_t)0ULL);
lean_inc_ref(v_calls_363_);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_363_, v_args_362_, v_sz_381_, v___x_382_, v___x_380_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_424_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_424_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_424_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_424_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_fst_388_; 
v_fst_388_ = lean_ctor_get(v_a_384_, 0);
if (lean_obj_tag(v_fst_388_) == 0)
{
lean_object* v_snd_389_; lean_object* v_fst_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_418_; 
v_snd_389_ = lean_ctor_get(v_a_384_, 1);
lean_inc(v_snd_389_);
lean_dec(v_a_384_);
v_fst_390_ = lean_ctor_get(v_snd_389_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_snd_389_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_snd_389_, 1);
lean_dec(v_unused_419_);
v___x_392_ = v_snd_389_;
v_isShared_393_ = v_isSharedCheck_418_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_fst_390_);
lean_dec(v_snd_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_418_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_calls_394_; lean_object* v_seen_395_; lean_object* v___x_397_; 
v_calls_394_ = lean_ctor_get(v_calls_363_, 0);
v_seen_395_ = lean_ctor_get(v_calls_363_, 1);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_fst_390_);
lean_ctor_set(v___x_392_, 0, v_funName_369_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_funName_369_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_fst_390_);
v___x_397_ = v_reuseFailAlloc_417_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
uint8_t v___x_398_; 
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_395_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_411_; 
lean_inc_ref(v_seen_395_);
lean_inc_ref(v_calls_394_);
v_isSharedCheck_411_ = !lean_is_exclusive(v_calls_363_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_412_ = lean_ctor_get(v_calls_363_, 1);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_calls_363_, 0);
lean_dec(v_unused_413_);
v___x_400_ = v_calls_363_;
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_calls_363_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_402_ = lean_array_push(v_calls_394_, v_e_360_);
v___x_403_ = lean_box(0);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_395_, v___x_397_, v___x_403_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_404_);
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_406_);
v___x_408_ = v___x_386_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_object* v___x_415_; 
lean_dec_ref(v___x_397_);
lean_dec_ref(v_e_360_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_calls_363_);
v___x_415_ = v___x_386_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_calls_363_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
else
{
lean_object* v_val_420_; lean_object* v___x_422_; 
lean_inc_ref(v_fst_388_);
lean_dec(v_a_384_);
lean_dec(v_funName_369_);
lean_dec_ref(v_calls_363_);
lean_dec_ref(v_e_360_);
v_val_420_ = lean_ctor_get(v_fst_388_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_fst_388_, 1);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_val_420_);
v___x_422_ = v___x_386_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_val_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_funName_369_);
lean_dec_ref(v_calls_363_);
lean_dec_ref(v_e_360_);
v_a_425_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_383_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_383_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object* v_e_433_, lean_object* v_funIndInfo_434_, lean_object* v_args_435_, lean_object* v_calls_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_433_, v_funIndInfo_434_, v_args_435_, v_calls_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec_ref(v_args_435_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object* v_calls_443_, lean_object* v_as_444_, size_t v_sz_445_, size_t v_i_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_443_, v_as_444_, v_sz_445_, v_i_446_, v_b_447_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object* v_calls_454_, lean_object* v_as_455_, lean_object* v_sz_456_, lean_object* v_i_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
size_t v_sz_boxed_464_; size_t v_i_boxed_465_; lean_object* v_res_466_; 
v_sz_boxed_464_ = lean_unbox_usize(v_sz_456_);
lean_dec(v_sz_456_);
v_i_boxed_465_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_454_, v_as_455_, v_sz_boxed_464_, v_i_boxed_465_, v_b_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec_ref(v_as_455_);
return v_res_466_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object* v_00_u03b2_467_, lean_object* v_m_468_, lean_object* v_a_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_468_, v_a_469_);
return v___x_470_;
}
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object* v_00_u03b2_481_, lean_object* v_a_482_, lean_object* v_x_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_482_, v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object* v_00_u03b2_485_, lean_object* v_a_486_, lean_object* v_x_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_485_, v_a_486_, v_x_487_);
lean_dec(v_x_487_);
lean_dec_ref(v_a_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object* v_00_u03b2_490_, lean_object* v_data_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_491_);
return v___x_492_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(lean_object* v_xs_493_, lean_object* v_ys_494_, lean_object* v_hsz_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_493_, v_ys_494_, v_x_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_499_, lean_object* v_ys_500_, lean_object* v_hsz_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
uint8_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_499_, v_ys_500_, v_hsz_501_, v_x_502_, v_x_503_);
lean_dec_ref(v_ys_500_);
lean_dec_ref(v_xs_499_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_506_, lean_object* v_i_507_, lean_object* v_source_508_, lean_object* v_target_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_507_, v_source_508_, v_target_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object* v_snd_515_, lean_object* v_x_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = l_Lean_NameSet_contains(v_snd_515_, v_x_516_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; 
v___x_518_ = 1;
return v___x_518_;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = 0;
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object* v_snd_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_520_, v_x_521_);
lean_dec(v_x_521_);
lean_dec(v_snd_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
if (lean_obj_tag(v_a_524_) == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_a_525_);
return v___x_526_;
}
else
{
lean_object* v_key_527_; lean_object* v_tail_528_; lean_object* v_fst_529_; lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_551_; 
v_key_527_ = lean_ctor_get(v_a_524_, 0);
lean_inc(v_key_527_);
v_tail_528_ = lean_ctor_get(v_a_524_, 2);
lean_inc(v_tail_528_);
lean_dec_ref_known(v_a_524_, 3);
v_fst_529_ = lean_ctor_get(v_key_527_, 0);
lean_inc(v_fst_529_);
lean_dec(v_key_527_);
v_fst_530_ = lean_ctor_get(v_a_525_, 0);
v_snd_531_ = lean_ctor_get(v_a_525_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_551_ == 0)
{
v___x_533_ = v_a_525_;
v_isShared_534_ = v_isSharedCheck_551_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_inc(v_fst_530_);
lean_dec(v_a_525_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_551_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_NameSet_contains(v_snd_531_, v_fst_529_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_NameSet_contains(v_fst_530_, v_fst_529_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = l_Lean_NameSet_insert(v_fst_530_, v_fst_529_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_537_);
v___x_539_ = v___x_533_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_snd_531_);
v___x_539_ = v_reuseFailAlloc_541_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
v_a_524_ = v_tail_528_;
v_a_525_ = v___x_539_;
goto _start;
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = l_Lean_NameSet_insert(v_snd_531_, v_fst_529_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_542_);
v___x_544_ = v___x_533_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_fst_530_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_a_524_ = v_tail_528_;
v_a_525_ = v___x_544_;
goto _start;
}
}
}
else
{
lean_object* v___x_548_; 
lean_dec(v_fst_529_);
if (v_isShared_534_ == 0)
{
v___x_548_ = v___x_533_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_fst_530_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_531_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v_a_524_ = v_tail_528_;
v_a_525_ = v___x_548_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(lean_object* v_as_552_, size_t v_sz_553_, size_t v_i_554_, lean_object* v_b_555_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_lt(v_i_554_, v_sz_553_);
if (v___x_556_ == 0)
{
return v_b_555_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_array_uget_borrowed(v_as_552_, v_i_554_);
lean_inc(v_a_557_);
v___x_558_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_557_, v_b_555_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
return v_a_559_;
}
else
{
lean_object* v_a_560_; size_t v___x_561_; size_t v___x_562_; 
v_a_560_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_558_, 1);
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_i_554_, v___x_561_);
v_i_554_ = v___x_562_;
v_b_555_ = v_a_560_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(lean_object* v_as_564_, lean_object* v_sz_565_, lean_object* v_i_566_, lean_object* v_b_567_){
_start:
{
size_t v_sz_boxed_568_; size_t v_i_boxed_569_; lean_object* v_res_570_; 
v_sz_boxed_568_ = lean_unbox_usize(v_sz_565_);
lean_dec(v_sz_565_);
v_i_boxed_569_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_564_, v_sz_boxed_568_, v_i_boxed_569_, v_b_567_);
lean_dec_ref(v_as_564_);
return v_res_570_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0(void){
_start:
{
lean_object* v_seen_571_; lean_object* v___x_572_; 
v_seen_571_ = l_Lean_NameSet_empty;
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_seen_571_);
lean_ctor_set(v___x_572_, 1, v_seen_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object* v_calls_573_){
_start:
{
lean_object* v_seen_574_; lean_object* v___x_575_; lean_object* v_buckets_576_; size_t v_sz_577_; size_t v___x_578_; lean_object* v___x_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___f_582_; lean_object* v___x_583_; 
v_seen_574_ = lean_ctor_get(v_calls_573_, 1);
v___x_575_ = lean_obj_once(&l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0, &l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once, _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0);
v_buckets_576_ = lean_ctor_get(v_seen_574_, 1);
v_sz_577_ = lean_array_size(v_buckets_576_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_576_, v_sz_577_, v___x_578_, v___x_575_);
v_fst_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_fst_580_);
v_snd_581_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_snd_581_);
lean_dec_ref(v___x_579_);
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed), 2, 1);
lean_closure_set(v___f_582_, 0, v_snd_581_);
v___x_583_ = l_Lean_NameSet_filter(v___f_582_, v_fst_580_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object* v_calls_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_584_);
lean_dec_ref(v_calls_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object* v_e_586_, lean_object* v_funIndInfo_587_, lean_object* v_args_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_st_ref_get(v_a_589_);
v___x_596_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_586_, v_funIndInfo_587_, v_args_588_, v___x_595_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_605_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_st_ref_set(v_a_589_, v_a_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_a_606_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_596_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_596_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object* v_e_614_, lean_object* v_funIndInfo_615_, lean_object* v_args_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_614_, v_funIndInfo_615_, v_args_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_args_616_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object* v_e_624_, lean_object* v_funIndInfo_625_, lean_object* v_args_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_624_, v_funIndInfo_625_, v_args_626_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object* v_e_635_, lean_object* v_funIndInfo_636_, lean_object* v_args_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_635_, v_funIndInfo_636_, v_args_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec_ref(v_args_637_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object* v_e_646_, lean_object* v_funIndInfo_647_, lean_object* v_args_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_646_, v_funIndInfo_647_, v_args_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object* v_e_656_, lean_object* v_funIndInfo_657_, lean_object* v_args_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_656_, v_funIndInfo_657_, v_args_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_args_658_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object* v_e_666_, lean_object* v_funIndInfo_667_, lean_object* v_args_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_666_, v_funIndInfo_667_, v_args_668_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object* v_e_677_, lean_object* v_funIndInfo_678_, lean_object* v_args_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_677_, v_funIndInfo_678_, v_args_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec_ref(v_args_679_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
return v_x_688_;
}
else
{
lean_object* v_key_690_; lean_object* v_value_691_; lean_object* v_tail_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_718_; 
v_key_690_ = lean_ctor_get(v_x_689_, 0);
v_value_691_ = lean_ctor_get(v_x_689_, 1);
v_tail_692_ = lean_ctor_get(v_x_689_, 2);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_718_ == 0)
{
v___x_694_ = v_x_689_;
v_isShared_695_ = v_isSharedCheck_718_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_tail_692_);
lean_inc(v_value_691_);
lean_inc(v_key_690_);
lean_dec(v_x_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_718_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; size_t v___x_697_; uint64_t v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v_fold_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_696_ = lean_array_get_size(v_x_688_);
v___x_697_ = lean_ptr_addr(v_key_690_);
v___x_698_ = lean_usize_to_uint64(v___x_697_);
v___x_699_ = 11ULL;
v___x_700_ = lean_uint64_mix_hash(v___x_698_, v___x_699_);
v___x_701_ = 32ULL;
v___x_702_ = lean_uint64_shift_right(v___x_700_, v___x_701_);
v_fold_703_ = lean_uint64_xor(v___x_700_, v___x_702_);
v___x_704_ = 16ULL;
v___x_705_ = lean_uint64_shift_right(v_fold_703_, v___x_704_);
v___x_706_ = lean_uint64_xor(v_fold_703_, v___x_705_);
v___x_707_ = lean_uint64_to_usize(v___x_706_);
v___x_708_ = lean_usize_of_nat(v___x_696_);
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_sub(v___x_708_, v___x_709_);
v___x_711_ = lean_usize_land(v___x_707_, v___x_710_);
v___x_712_ = lean_array_uget_borrowed(v_x_688_, v___x_711_);
lean_inc(v___x_712_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 2, v___x_712_);
v___x_714_ = v___x_694_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_key_690_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_value_691_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v___x_712_);
v___x_714_ = v_reuseFailAlloc_717_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; 
v___x_715_ = lean_array_uset(v_x_688_, v___x_711_, v___x_714_);
v_x_688_ = v___x_715_;
v_x_689_ = v_tail_692_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(lean_object* v_i_719_, lean_object* v_source_720_, lean_object* v_target_721_){
_start:
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_array_get_size(v_source_720_);
v___x_723_ = lean_nat_dec_lt(v_i_719_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec_ref(v_source_720_);
lean_dec(v_i_719_);
return v_target_721_;
}
else
{
lean_object* v_es_724_; lean_object* v___x_725_; lean_object* v_source_726_; lean_object* v_target_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_es_724_ = lean_array_fget(v_source_720_, v_i_719_);
v___x_725_ = lean_box(0);
v_source_726_ = lean_array_fset(v_source_720_, v_i_719_, v___x_725_);
v_target_727_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_721_, v_es_724_);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_i_719_, v___x_728_);
lean_dec(v_i_719_);
v_i_719_ = v___x_729_;
v_source_720_ = v_source_726_;
v_target_721_ = v_target_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(lean_object* v_data_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_nbuckets_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_732_ = lean_array_get_size(v_data_731_);
v___x_733_ = lean_unsigned_to_nat(2u);
v_nbuckets_734_ = lean_nat_mul(v___x_732_, v___x_733_);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_box(0);
v___x_737_ = lean_mk_array(v_nbuckets_734_, v___x_736_);
v___x_738_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_735_, v_data_731_, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_a_739_, lean_object* v_x_740_){
_start:
{
if (lean_obj_tag(v_x_740_) == 0)
{
uint8_t v___x_741_; 
v___x_741_ = 0;
return v___x_741_;
}
else
{
lean_object* v_key_742_; lean_object* v_tail_743_; size_t v___x_744_; size_t v___x_745_; uint8_t v___x_746_; 
v_key_742_ = lean_ctor_get(v_x_740_, 0);
v_tail_743_ = lean_ctor_get(v_x_740_, 2);
v___x_744_ = lean_ptr_addr(v_key_742_);
v___x_745_ = lean_ptr_addr(v_a_739_);
v___x_746_ = lean_usize_dec_eq(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
v_x_740_ = v_tail_743_;
goto _start;
}
else
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_748_, lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_748_, v_x_749_);
lean_dec(v_x_749_);
lean_dec_ref(v_a_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(lean_object* v_m_752_, lean_object* v_a_753_, lean_object* v_b_754_){
_start:
{
lean_object* v_size_755_; lean_object* v_buckets_756_; lean_object* v___x_757_; size_t v___x_758_; uint64_t v___x_759_; uint64_t v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; uint64_t v___x_763_; uint64_t v_fold_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v___x_767_; size_t v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; lean_object* v_bkt_773_; uint8_t v___x_774_; 
v_size_755_ = lean_ctor_get(v_m_752_, 0);
v_buckets_756_ = lean_ctor_get(v_m_752_, 1);
v___x_757_ = lean_array_get_size(v_buckets_756_);
v___x_758_ = lean_ptr_addr(v_a_753_);
v___x_759_ = lean_usize_to_uint64(v___x_758_);
v___x_760_ = 11ULL;
v___x_761_ = lean_uint64_mix_hash(v___x_759_, v___x_760_);
v___x_762_ = 32ULL;
v___x_763_ = lean_uint64_shift_right(v___x_761_, v___x_762_);
v_fold_764_ = lean_uint64_xor(v___x_761_, v___x_763_);
v___x_765_ = 16ULL;
v___x_766_ = lean_uint64_shift_right(v_fold_764_, v___x_765_);
v___x_767_ = lean_uint64_xor(v_fold_764_, v___x_766_);
v___x_768_ = lean_uint64_to_usize(v___x_767_);
v___x_769_ = lean_usize_of_nat(v___x_757_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_sub(v___x_769_, v___x_770_);
v___x_772_ = lean_usize_land(v___x_768_, v___x_771_);
v_bkt_773_ = lean_array_uget_borrowed(v_buckets_756_, v___x_772_);
v___x_774_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_753_, v_bkt_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_795_; 
lean_inc_ref(v_buckets_756_);
lean_inc(v_size_755_);
v_isSharedCheck_795_ = !lean_is_exclusive(v_m_752_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; 
v_unused_796_ = lean_ctor_get(v_m_752_, 1);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_m_752_, 0);
lean_dec(v_unused_797_);
v___x_776_ = v_m_752_;
v_isShared_777_ = v_isSharedCheck_795_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_m_752_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_795_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v_size_x27_779_; lean_object* v___x_780_; lean_object* v_buckets_x27_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_778_ = lean_unsigned_to_nat(1u);
v_size_x27_779_ = lean_nat_add(v_size_755_, v___x_778_);
lean_dec(v_size_755_);
lean_inc(v_bkt_773_);
v___x_780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_780_, 0, v_a_753_);
lean_ctor_set(v___x_780_, 1, v_b_754_);
lean_ctor_set(v___x_780_, 2, v_bkt_773_);
v_buckets_x27_781_ = lean_array_uset(v_buckets_756_, v___x_772_, v___x_780_);
v___x_782_ = lean_unsigned_to_nat(4u);
v___x_783_ = lean_nat_mul(v_size_x27_779_, v___x_782_);
v___x_784_ = lean_unsigned_to_nat(3u);
v___x_785_ = lean_nat_div(v___x_783_, v___x_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_array_get_size(v_buckets_x27_781_);
v___x_787_ = lean_nat_dec_le(v___x_785_, v___x_786_);
lean_dec(v___x_785_);
if (v___x_787_ == 0)
{
lean_object* v_val_788_; lean_object* v___x_790_; 
v_val_788_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_781_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v_val_788_);
lean_ctor_set(v___x_776_, 0, v_size_x27_779_);
v___x_790_ = v___x_776_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_size_x27_779_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_val_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v___x_793_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v_buckets_x27_781_);
lean_ctor_set(v___x_776_, 0, v_size_x27_779_);
v___x_793_ = v___x_776_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_size_x27_779_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_buckets_x27_781_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_dec(v_b_754_);
lean_dec_ref(v_a_753_);
return v_m_752_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_buckets_800_; lean_object* v___x_801_; size_t v___x_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v_fold_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_buckets_800_ = lean_ctor_get(v_m_798_, 1);
v___x_801_ = lean_array_get_size(v_buckets_800_);
v___x_802_ = lean_ptr_addr(v_a_799_);
v___x_803_ = lean_usize_to_uint64(v___x_802_);
v___x_804_ = 11ULL;
v___x_805_ = lean_uint64_mix_hash(v___x_803_, v___x_804_);
v___x_806_ = 32ULL;
v___x_807_ = lean_uint64_shift_right(v___x_805_, v___x_806_);
v_fold_808_ = lean_uint64_xor(v___x_805_, v___x_807_);
v___x_809_ = 16ULL;
v___x_810_ = lean_uint64_shift_right(v_fold_808_, v___x_809_);
v___x_811_ = lean_uint64_xor(v_fold_808_, v___x_810_);
v___x_812_ = lean_uint64_to_usize(v___x_811_);
v___x_813_ = lean_usize_of_nat(v___x_801_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_sub(v___x_813_, v___x_814_);
v___x_816_ = lean_usize_land(v___x_812_, v___x_815_);
v___x_817_ = lean_array_uget_borrowed(v_buckets_800_, v___x_816_);
v___x_818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_799_, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_819_, lean_object* v_a_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_819_, v_a_820_);
lean_dec_ref(v_a_820_);
lean_dec_ref(v_m_819_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_823_; lean_object* v_dummy_824_; 
v___x_823_ = lean_box(0);
v_dummy_824_ = l_Lean_Expr_sort___override(v___x_823_);
return v_dummy_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_e_825_, lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; 
if (lean_obj_tag(v_x_826_) == 5)
{
lean_object* v_fn_858_; lean_object* v_arg_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_fn_858_ = lean_ctor_get(v_x_826_, 0);
lean_inc_ref(v_fn_858_);
v_arg_859_ = lean_ctor_get(v_x_826_, 1);
lean_inc_ref(v_arg_859_);
lean_dec_ref_known(v_x_826_, 2);
v___x_860_ = lean_array_set(v_x_827_, v_x_828_, v_arg_859_);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_sub(v_x_828_, v___x_861_);
lean_dec(v_x_828_);
v_x_826_ = v_fn_858_;
v_x_827_ = v___x_860_;
v_x_828_ = v___x_862_;
goto _start;
}
else
{
lean_dec(v_x_828_);
if (lean_obj_tag(v_x_826_) == 4)
{
lean_object* v_declName_864_; lean_object* v_funName_865_; uint8_t v___x_866_; 
v_declName_864_ = lean_ctor_get(v_x_826_, 0);
lean_inc(v_declName_864_);
lean_dec_ref_known(v_x_826_, 2);
v_funName_865_ = lean_ctor_get(v___y_830_, 0);
v___x_866_ = lean_name_eq(v_declName_864_, v_funName_865_);
lean_dec(v_declName_864_);
if (v___x_866_ == 0)
{
lean_dec_ref(v_e_825_);
v___y_838_ = v___y_829_;
v___y_839_ = v___y_830_;
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
goto v___jp_837_;
}
else
{
uint8_t v___x_867_; 
v___x_867_ = l_Lean_Expr_hasLooseBVars(v_e_825_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_inc_ref(v___y_830_);
v___x_868_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_825_, v___y_830_, v_x_827_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_dec_ref_known(v___x_868_, 1);
v___y_838_ = v___y_829_;
v___y_839_ = v___y_830_;
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
goto v___jp_837_;
}
else
{
lean_dec_ref(v_x_827_);
return v___x_868_;
}
}
else
{
lean_dec_ref(v_e_825_);
v___y_838_ = v___y_829_;
v___y_839_ = v___y_830_;
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
goto v___jp_837_;
}
}
}
else
{
lean_object* v___x_869_; 
lean_dec_ref(v_e_825_);
v___x_869_ = l_Lean_Meta_FunInd_Collector_visit(v_x_826_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_dec_ref_known(v___x_869_, 1);
v___y_838_ = v___y_829_;
v___y_839_ = v___y_830_;
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
goto v___jp_837_;
}
else
{
lean_dec_ref(v_x_827_);
return v___x_869_;
}
}
}
v___jp_837_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_array_get_size(v_x_827_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_dec_ref(v_x_827_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
return v___x_849_;
}
else
{
uint8_t v___x_850_; 
v___x_850_ = lean_nat_dec_le(v___x_846_, v___x_846_);
if (v___x_850_ == 0)
{
if (v___x_848_ == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v_x_827_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_847_);
return v___x_851_;
}
else
{
size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((size_t)0ULL);
v___x_853_ = lean_usize_of_nat(v___x_846_);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_827_, v___x_852_, v___x_853_, v___x_847_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec_ref(v_x_827_);
return v___x_854_;
}
}
else
{
size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((size_t)0ULL);
v___x_856_ = lean_usize_of_nat(v___x_846_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_827_, v___x_855_, v___x_856_, v___x_847_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec_ref(v_x_827_);
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_st_ref_get(v_a_871_);
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_879_, v_e_870_);
lean_dec(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_d_886_; lean_object* v_b_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; 
v___x_881_ = lean_st_ref_take(v_a_871_);
v___x_882_ = lean_box(0);
lean_inc_ref(v_e_870_);
v___x_883_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_881_, v_e_870_, v___x_882_);
v___x_884_ = lean_st_ref_set(v_a_871_, v___x_883_);
switch(lean_obj_tag(v_e_870_))
{
case 4:
{
lean_object* v___x_897_; 
lean_dec_ref_known(v_e_870_, 2);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_882_);
return v___x_897_;
}
case 7:
{
lean_object* v_binderType_898_; lean_object* v_body_899_; 
v_binderType_898_ = lean_ctor_get(v_e_870_, 1);
lean_inc_ref(v_binderType_898_);
v_body_899_ = lean_ctor_get(v_e_870_, 2);
lean_inc_ref(v_body_899_);
lean_dec_ref_known(v_e_870_, 3);
v_d_886_ = v_binderType_898_;
v_b_887_ = v_body_899_;
v___y_888_ = v_a_871_;
v___y_889_ = v_a_872_;
v___y_890_ = v_a_873_;
v___y_891_ = v_a_874_;
v___y_892_ = v_a_875_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
goto v___jp_885_;
}
case 6:
{
lean_object* v_binderType_900_; lean_object* v_body_901_; 
v_binderType_900_ = lean_ctor_get(v_e_870_, 1);
lean_inc_ref(v_binderType_900_);
v_body_901_ = lean_ctor_get(v_e_870_, 2);
lean_inc_ref(v_body_901_);
lean_dec_ref_known(v_e_870_, 3);
v_d_886_ = v_binderType_900_;
v_b_887_ = v_body_901_;
v___y_888_ = v_a_871_;
v___y_889_ = v_a_872_;
v___y_890_ = v_a_873_;
v___y_891_ = v_a_874_;
v___y_892_ = v_a_875_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
goto v___jp_885_;
}
case 10:
{
lean_object* v_expr_902_; 
v_expr_902_ = lean_ctor_get(v_e_870_, 1);
lean_inc_ref(v_expr_902_);
lean_dec_ref_known(v_e_870_, 2);
v_e_870_ = v_expr_902_;
goto _start;
}
case 8:
{
lean_object* v_type_904_; lean_object* v_value_905_; lean_object* v_body_906_; lean_object* v___x_907_; 
v_type_904_ = lean_ctor_get(v_e_870_, 1);
lean_inc_ref(v_type_904_);
v_value_905_ = lean_ctor_get(v_e_870_, 2);
lean_inc_ref(v_value_905_);
v_body_906_ = lean_ctor_get(v_e_870_, 3);
lean_inc_ref(v_body_906_);
lean_dec_ref_known(v_e_870_, 4);
v___x_907_ = l_Lean_Meta_FunInd_Collector_visit(v_type_904_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; 
lean_dec_ref_known(v___x_907_, 1);
v___x_908_ = l_Lean_Meta_FunInd_Collector_visit(v_value_905_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_dec_ref_known(v___x_908_, 1);
v_e_870_ = v_body_906_;
goto _start;
}
else
{
lean_dec_ref(v_body_906_);
return v___x_908_;
}
}
else
{
lean_dec_ref(v_body_906_);
lean_dec_ref(v_value_905_);
return v___x_907_;
}
}
case 5:
{
lean_object* v_dummy_910_; lean_object* v_nargs_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_dummy_910_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_911_ = l_Lean_Expr_getAppNumArgs(v_e_870_);
lean_inc(v_nargs_911_);
v___x_912_ = lean_mk_array(v_nargs_911_, v_dummy_910_);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_sub(v_nargs_911_, v___x_913_);
lean_dec(v_nargs_911_);
lean_inc_ref(v_e_870_);
v___x_915_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_870_, v_e_870_, v___x_912_, v___x_914_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
return v___x_915_;
}
case 11:
{
lean_object* v_struct_916_; 
v_struct_916_ = lean_ctor_get(v_e_870_, 2);
lean_inc_ref(v_struct_916_);
lean_dec_ref_known(v_e_870_, 3);
v_e_870_ = v_struct_916_;
goto _start;
}
default: 
{
lean_object* v___x_918_; 
lean_dec_ref(v_e_870_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_882_);
return v___x_918_;
}
}
v___jp_885_:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Meta_FunInd_Collector_visit(v_d_886_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_dec_ref_known(v___x_895_, 1);
v_e_870_ = v_b_887_;
v_a_871_ = v___y_888_;
v_a_872_ = v___y_889_;
v_a_873_ = v___y_890_;
v_a_874_ = v___y_891_;
v_a_875_ = v___y_892_;
v_a_876_ = v___y_893_;
v_a_877_ = v___y_894_;
goto _start;
}
else
{
lean_dec_ref(v_b_887_);
return v___x_895_;
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref(v_e_870_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_921_, size_t v_i_922_, size_t v_stop_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_eq(v_i_922_, v_stop_923_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_array_uget_borrowed(v_as_921_, v_i_922_);
lean_inc(v___x_934_);
v___x_935_ = l_Lean_Meta_FunInd_Collector_visit(v___x_934_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; size_t v___x_937_; size_t v___x_938_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_922_, v___x_937_);
v_i_922_ = v___x_938_;
v_b_924_ = v_a_936_;
goto _start;
}
else
{
return v___x_935_;
}
}
else
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_924_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_941_, lean_object* v_i_942_, lean_object* v_stop_943_, lean_object* v_b_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
size_t v_i_boxed_953_; size_t v_stop_boxed_954_; lean_object* v_res_955_; 
v_i_boxed_953_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_stop_boxed_954_ = lean_unbox_usize(v_stop_943_);
lean_dec(v_stop_943_);
v_res_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_941_, v_i_boxed_953_, v_stop_boxed_954_, v_b_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v_as_941_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Meta_FunInd_Collector_visit(v_e_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_e_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_966_, v_x_967_, v_x_968_, v_x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
return v_res_978_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_979_, lean_object* v_m_980_, lean_object* v_a_981_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_980_, v_a_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_983_, lean_object* v_m_984_, lean_object* v_a_985_){
_start:
{
uint8_t v_res_986_; lean_object* v_r_987_; 
v_res_986_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_983_, v_m_984_, v_a_985_);
lean_dec_ref(v_a_985_);
lean_dec_ref(v_m_984_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_00_u03b2_988_, lean_object* v_m_989_, lean_object* v_a_990_, lean_object* v_b_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_989_, v_a_990_, v_b_991_);
return v___x_992_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_997_, lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_res_1000_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_997_, v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_a_998_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object* v_00_u03b2_1002_, lean_object* v_data_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1005_, lean_object* v_i_1006_, lean_object* v_source_1007_, lean_object* v_target_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_1006_, v_source_1007_, v_target_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1011_, v_x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = l_Lean_Expr_hasMVar(v_e_1014_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_e_1014_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_mctx_1020_; lean_object* v___x_1021_; lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; lean_object* v_cache_1025_; lean_object* v_zetaDeltaFVarIds_1026_; lean_object* v_postponed_1027_; lean_object* v_diag_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1037_; 
v___x_1019_ = lean_st_ref_get(v___y_1015_);
v_mctx_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc_ref(v_mctx_1020_);
lean_dec(v___x_1019_);
v___x_1021_ = l_Lean_instantiateMVarsCore(v_mctx_1020_, v_e_1014_);
v_fst_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_fst_1022_);
v_snd_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_snd_1023_);
lean_dec_ref(v___x_1021_);
v___x_1024_ = lean_st_ref_take(v___y_1015_);
v_cache_1025_ = lean_ctor_get(v___x_1024_, 1);
v_zetaDeltaFVarIds_1026_ = lean_ctor_get(v___x_1024_, 2);
v_postponed_1027_ = lean_ctor_get(v___x_1024_, 3);
v_diag_1028_ = lean_ctor_get(v___x_1024_, 4);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1024_, 0);
lean_dec(v_unused_1038_);
v___x_1030_ = v___x_1024_;
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_diag_1028_);
lean_inc(v_postponed_1027_);
lean_inc(v_zetaDeltaFVarIds_1026_);
lean_inc(v_cache_1025_);
lean_dec(v___x_1024_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_snd_1023_);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_snd_1023_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_cache_1025_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_zetaDeltaFVarIds_1026_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v_postponed_1027_);
lean_ctor_set(v_reuseFailAlloc_1036_, 4, v_diag_1028_);
v___x_1033_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_st_ref_set(v___y_1015_, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_fst_1022_);
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1039_, v___y_1040_);
lean_dec(v___y_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1043_, v___y_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1063_, size_t v_sz_1064_, size_t v_i_1065_, lean_object* v_b_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_usize_dec_lt(v_i_1065_, v_sz_1064_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_b_1066_);
return v___x_1076_;
}
else
{
lean_object* v_snd_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1135_; 
v_snd_1077_ = lean_ctor_get(v_b_1066_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_b_1066_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v_b_1066_, 0);
lean_dec(v_unused_1136_);
v___x_1079_ = v_b_1066_;
v_isShared_1080_ = v_isSharedCheck_1135_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_snd_1077_);
lean_dec(v_b_1066_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1135_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v_a_1083_; lean_object* v_a_1090_; 
v___x_1081_ = lean_box(0);
v_a_1090_ = lean_array_uget_borrowed(v_as_1063_, v_i_1065_);
if (lean_obj_tag(v_a_1090_) == 0)
{
v_a_1083_ = v_snd_1077_;
goto v___jp_1082_;
}
else
{
lean_object* v_val_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
lean_dec(v_snd_1077_);
v_val_1091_ = lean_ctor_get(v_a_1090_, 0);
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Lean_LocalDecl_isAuxDecl(v_val_1091_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_LocalDecl_value_x3f(v_val_1091_, v___x_1093_);
if (lean_obj_tag(v___x_1094_) == 1)
{
lean_object* v_val_1095_; lean_object* v___x_1096_; 
v_val_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_val_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1095_, v___y_1071_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1097_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref_known(v___x_1098_, 1);
v_a_1083_ = v___x_1092_;
goto v___jp_1082_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_del_object(v___x_1079_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1079_);
v_a_1107_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1096_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1096_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
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
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v___x_1094_);
v___x_1115_ = l_Lean_LocalDecl_type(v_val_1091_);
v___x_1116_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1115_, v___y_1071_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1117_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_dec_ref_known(v___x_1118_, 1);
v_a_1083_ = v___x_1092_;
goto v___jp_1082_;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_del_object(v___x_1079_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_del_object(v___x_1079_);
v_a_1127_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1116_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1116_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
v_a_1083_ = v___x_1092_;
goto v___jp_1082_;
}
}
v___jp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_a_1083_);
lean_ctor_set(v___x_1079_, 0, v___x_1081_);
v___x_1085_ = v___x_1079_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_a_1083_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
size_t v___x_1086_; size_t v___x_1087_; 
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1065_, v___x_1086_);
v_i_1065_ = v___x_1087_;
v_b_1066_ = v___x_1085_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1137_, lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
size_t v_sz_boxed_1149_; size_t v_i_boxed_1150_; lean_object* v_res_1151_; 
v_sz_boxed_1149_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1150_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1137_, v_sz_boxed_1149_, v_i_boxed_1150_, v_b_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v_as_1137_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1152_, size_t v_sz_1153_, size_t v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_lt(v_i_1154_, v_sz_1153_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_b_1155_);
return v___x_1165_;
}
else
{
lean_object* v_snd_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1224_; 
v_snd_1166_ = lean_ctor_get(v_b_1155_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_b_1155_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_b_1155_, 0);
lean_dec(v_unused_1225_);
v___x_1168_ = v_b_1155_;
v_isShared_1169_ = v_isSharedCheck_1224_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snd_1166_);
lean_dec(v_b_1155_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1224_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v_a_1172_; lean_object* v_a_1179_; 
v___x_1170_ = lean_box(0);
v_a_1179_ = lean_array_uget_borrowed(v_as_1152_, v_i_1154_);
if (lean_obj_tag(v_a_1179_) == 0)
{
v_a_1172_ = v_snd_1166_;
goto v___jp_1171_;
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
lean_dec(v_snd_1166_);
v_val_1180_ = lean_ctor_get(v_a_1179_, 0);
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lean_LocalDecl_isAuxDecl(v_val_1180_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_LocalDecl_value_x3f(v_val_1180_, v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 1)
{
lean_object* v_val_1184_; lean_object* v___x_1185_; 
v_val_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1184_, v___y_1160_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1186_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_dec_ref_known(v___x_1187_, 1);
v_a_1172_ = v___x_1181_;
goto v___jp_1171_;
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_del_object(v___x_1168_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1168_);
v_a_1196_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1185_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1185_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v___x_1183_);
v___x_1204_ = l_Lean_LocalDecl_type(v_val_1180_);
v___x_1205_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1204_, v___y_1160_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1207_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1206_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_dec_ref_known(v___x_1207_, 1);
v_a_1172_ = v___x_1181_;
goto v___jp_1171_;
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_del_object(v___x_1168_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_del_object(v___x_1168_);
v_a_1216_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1205_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1205_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
else
{
v_a_1172_ = v___x_1181_;
goto v___jp_1171_;
}
}
v___jp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_a_1172_);
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1174_ = v___x_1168_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_a_1172_);
v___x_1174_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_add(v_i_1154_, v___x_1175_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1152_, v_sz_1153_, v___x_1176_, v___x_1174_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1226_, lean_object* v_sz_1227_, lean_object* v_i_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
size_t v_sz_boxed_1238_; size_t v_i_boxed_1239_; lean_object* v_res_1240_; 
v_sz_boxed_1238_ = lean_unbox_usize(v_sz_1227_);
lean_dec(v_sz_1227_);
v_i_boxed_1239_ = lean_unbox_usize(v_i_1228_);
lean_dec(v_i_1228_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1226_, v_sz_boxed_1238_, v_i_boxed_1239_, v_b_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v_as_1226_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1241_, size_t v_sz_1242_, size_t v_i_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_lt(v_i_1243_, v_sz_1242_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_b_1244_);
return v___x_1254_;
}
else
{
lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1313_; 
v_snd_1255_ = lean_ctor_get(v_b_1244_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_b_1244_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v_b_1244_, 0);
lean_dec(v_unused_1314_);
v___x_1257_ = v_b_1244_;
v_isShared_1258_ = v_isSharedCheck_1313_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_dec(v_b_1244_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1313_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v_a_1261_; lean_object* v_a_1268_; 
v___x_1259_ = lean_box(0);
v_a_1268_ = lean_array_uget_borrowed(v_as_1241_, v_i_1243_);
if (lean_obj_tag(v_a_1268_) == 0)
{
v_a_1261_ = v_snd_1255_;
goto v___jp_1260_;
}
else
{
lean_object* v_val_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
lean_dec(v_snd_1255_);
v_val_1269_ = lean_ctor_get(v_a_1268_, 0);
v___x_1270_ = lean_box(0);
v___x_1271_ = l_Lean_LocalDecl_isAuxDecl(v_val_1269_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_LocalDecl_value_x3f(v_val_1269_, v___x_1271_);
if (lean_obj_tag(v___x_1272_) == 1)
{
lean_object* v_val_1273_; lean_object* v___x_1274_; 
v_val_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1273_, v___y_1249_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1275_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_dec_ref_known(v___x_1276_, 1);
v_a_1261_ = v___x_1270_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_del_object(v___x_1257_);
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1257_);
v_a_1285_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1274_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1274_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec(v___x_1272_);
v___x_1293_ = l_Lean_LocalDecl_type(v_val_1269_);
v___x_1294_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1293_, v___y_1249_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1295_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_dec_ref_known(v___x_1296_, 1);
v_a_1261_ = v___x_1270_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_del_object(v___x_1257_);
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
lean_del_object(v___x_1257_);
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
}
else
{
v_a_1261_ = v___x_1270_;
goto v___jp_1260_;
}
}
v___jp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_a_1261_);
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1263_ = v___x_1257_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_a_1261_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
size_t v___x_1264_; size_t v___x_1265_; 
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1243_, v___x_1264_);
v_i_1243_ = v___x_1265_;
v_b_1244_ = v___x_1263_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1315_, lean_object* v_sz_1316_, lean_object* v_i_1317_, lean_object* v_b_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
size_t v_sz_boxed_1327_; size_t v_i_boxed_1328_; lean_object* v_res_1329_; 
v_sz_boxed_1327_ = lean_unbox_usize(v_sz_1316_);
lean_dec(v_sz_1316_);
v_i_boxed_1328_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1315_, v_sz_boxed_1327_, v_i_boxed_1328_, v_b_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v_as_1315_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1330_, size_t v_sz_1331_, size_t v_i_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_lt(v_i_1332_, v_sz_1331_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_b_1333_);
return v___x_1343_;
}
else
{
lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1402_; 
v_snd_1344_ = lean_ctor_get(v_b_1333_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_b_1333_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v_b_1333_, 0);
lean_dec(v_unused_1403_);
v___x_1346_ = v_b_1333_;
v_isShared_1347_ = v_isSharedCheck_1402_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_dec(v_b_1333_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1402_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v_a_1350_; lean_object* v_a_1357_; 
v___x_1348_ = lean_box(0);
v_a_1357_ = lean_array_uget_borrowed(v_as_1330_, v_i_1332_);
if (lean_obj_tag(v_a_1357_) == 0)
{
v_a_1350_ = v_snd_1344_;
goto v___jp_1349_;
}
else
{
lean_object* v_val_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
lean_dec(v_snd_1344_);
v_val_1358_ = lean_ctor_get(v_a_1357_, 0);
v___x_1359_ = lean_box(0);
v___x_1360_ = l_Lean_LocalDecl_isAuxDecl(v_val_1358_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_LocalDecl_value_x3f(v_val_1358_, v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 1)
{
lean_object* v_val_1362_; lean_object* v___x_1363_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1362_, v___y_1338_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1364_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_dec_ref_known(v___x_1365_, 1);
v_a_1350_ = v___x_1359_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_del_object(v___x_1346_);
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1346_);
v_a_1374_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1363_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1363_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v___x_1361_);
v___x_1382_ = l_Lean_LocalDecl_type(v_val_1358_);
v___x_1383_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1382_, v___y_1338_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1384_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_dec_ref_known(v___x_1385_, 1);
v_a_1350_ = v___x_1359_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_del_object(v___x_1346_);
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_del_object(v___x_1346_);
v_a_1394_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1383_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1383_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
else
{
v_a_1350_ = v___x_1359_;
goto v___jp_1349_;
}
}
v___jp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_a_1350_);
lean_ctor_set(v___x_1346_, 0, v___x_1348_);
v___x_1352_ = v___x_1346_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_a_1350_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_add(v_i_1332_, v___x_1353_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1330_, v_sz_1331_, v___x_1354_, v___x_1352_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1404_, lean_object* v_sz_1405_, lean_object* v_i_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
size_t v_sz_boxed_1416_; size_t v_i_boxed_1417_; lean_object* v_res_1418_; 
v_sz_boxed_1416_ = lean_unbox_usize(v_sz_1405_);
lean_dec(v_sz_1405_);
v_i_boxed_1417_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1404_, v_sz_boxed_1416_, v_i_boxed_1417_, v_b_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v_as_1404_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_init_1419_, lean_object* v_n_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
if (lean_obj_tag(v_n_1420_) == 0)
{
lean_object* v_cs_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v_cs_1430_ = lean_ctor_get(v_n_1420_, 0);
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_b_1421_);
v_sz_1433_ = lean_array_size(v_cs_1430_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1419_, v_cs_1430_, v_sz_1433_, v___x_1434_, v___x_1432_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1450_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_fst_1440_; 
v_fst_1440_ = lean_ctor_get(v_a_1436_, 0);
if (lean_obj_tag(v_fst_1440_) == 0)
{
lean_object* v_snd_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v_snd_1441_ = lean_ctor_get(v_a_1436_, 1);
lean_inc(v_snd_1441_);
lean_dec(v_a_1436_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_snd_1441_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1442_);
v___x_1444_ = v___x_1438_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
else
{
lean_object* v_val_1446_; lean_object* v___x_1448_; 
lean_inc_ref(v_fst_1440_);
lean_dec(v_a_1436_);
v_val_1446_ = lean_ctor_get(v_fst_1440_, 0);
lean_inc(v_val_1446_);
lean_dec_ref_known(v_fst_1440_, 1);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v_val_1446_);
v___x_1448_ = v___x_1438_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_val_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1435_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1435_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_vs_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; size_t v_sz_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v_vs_1459_ = lean_ctor_get(v_n_1420_, 0);
v___x_1460_ = lean_box(0);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v_b_1421_);
v_sz_1462_ = lean_array_size(v_vs_1459_);
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1459_, v_sz_1462_, v___x_1463_, v___x_1461_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1479_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1479_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1479_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_fst_1469_; 
v_fst_1469_ = lean_ctor_get(v_a_1465_, 0);
if (lean_obj_tag(v_fst_1469_) == 0)
{
lean_object* v_snd_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v_snd_1470_ = lean_ctor_get(v_a_1465_, 1);
lean_inc(v_snd_1470_);
lean_dec(v_a_1465_);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_snd_1470_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1471_);
v___x_1473_ = v___x_1467_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
lean_object* v_val_1475_; lean_object* v___x_1477_; 
lean_inc_ref(v_fst_1469_);
lean_dec(v_a_1465_);
v_val_1475_ = lean_ctor_get(v_fst_1469_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v_fst_1469_, 1);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_val_1475_);
v___x_1477_ = v___x_1467_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_val_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1464_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1464_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_init_1488_, lean_object* v_as_1489_, size_t v_sz_1490_, size_t v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_usize_dec_lt(v_i_1491_, v_sz_1490_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_b_1492_);
return v___x_1502_;
}
else
{
lean_object* v_snd_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1537_; 
v_snd_1503_ = lean_ctor_get(v_b_1492_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_b_1492_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_b_1492_, 0);
lean_dec(v_unused_1538_);
v___x_1505_ = v_b_1492_;
v_isShared_1506_ = v_isSharedCheck_1537_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_snd_1503_);
lean_dec(v_b_1492_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1537_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_a_1507_; lean_object* v___x_1508_; 
v_a_1507_ = lean_array_uget_borrowed(v_as_1489_, v_i_1491_);
lean_inc(v_snd_1503_);
v___x_1508_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1488_, v_a_1507_, v_snd_1503_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1528_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1528_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1528_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
if (lean_obj_tag(v_a_1509_) == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_a_1509_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1513_);
v___x_1515_ = v___x_1505_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_snd_1503_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1515_);
v___x_1517_ = v___x_1511_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
lean_del_object(v___x_1511_);
lean_dec(v_snd_1503_);
v_a_1520_ = lean_ctor_get(v_a_1509_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v_a_1509_, 1);
v___x_1521_ = lean_box(0);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v_a_1520_);
lean_ctor_set(v___x_1505_, 0, v___x_1521_);
v___x_1523_ = v___x_1505_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_a_1520_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
size_t v___x_1524_; size_t v___x_1525_; 
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = lean_usize_add(v_i_1491_, v___x_1524_);
v_i_1491_ = v___x_1525_;
v_b_1492_ = v___x_1523_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_del_object(v___x_1505_);
lean_dec(v_snd_1503_);
v_a_1529_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1508_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1508_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1539_, lean_object* v_as_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
size_t v_sz_boxed_1552_; size_t v_i_boxed_1553_; lean_object* v_res_1554_; 
v_sz_boxed_1552_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1553_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1539_, v_as_1540_, v_sz_boxed_1552_, v_i_boxed_1553_, v_b_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v_as_1540_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_init_1555_, lean_object* v_n_1556_, lean_object* v_b_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1555_, v_n_1556_, v_b_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v_n_1556_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1567_, lean_object* v_init_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_root_1577_; lean_object* v_tail_1578_; lean_object* v___x_1579_; 
v_root_1577_ = lean_ctor_get(v_t_1567_, 0);
v_tail_1578_ = lean_ctor_get(v_t_1567_, 1);
v___x_1579_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1568_, v_root_1577_, v_init_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1616_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1616_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1616_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
if (lean_obj_tag(v_a_1580_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; 
v_a_1584_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v_a_1580_, 1);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v_a_1584_);
v___x_1586_ = v___x_1582_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; size_t v_sz_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
lean_del_object(v___x_1582_);
v_a_1588_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v_a_1580_, 1);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v_a_1588_);
v_sz_1591_ = lean_array_size(v_tail_1578_);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1578_, v_sz_1591_, v___x_1592_, v___x_1590_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1607_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fst_1598_; 
v_fst_1598_ = lean_ctor_get(v_a_1594_, 0);
if (lean_obj_tag(v_fst_1598_) == 0)
{
lean_object* v_snd_1599_; lean_object* v___x_1601_; 
v_snd_1599_ = lean_ctor_get(v_a_1594_, 1);
lean_inc(v_snd_1599_);
lean_dec(v_a_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_snd_1599_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_snd_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
else
{
lean_object* v_val_1603_; lean_object* v___x_1605_; 
lean_inc_ref(v_fst_1598_);
lean_dec(v_a_1594_);
v_val_1603_ = lean_ctor_get(v_fst_1598_, 0);
lean_inc(v_val_1603_);
lean_dec_ref_known(v_fst_1598_, 1);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_val_1603_);
v___x_1605_ = v___x_1596_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_val_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_a_1608_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1593_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1593_);
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
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1579_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1579_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1625_, lean_object* v_init_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1625_, v_init_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v_t_1625_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_lctx_1645_; lean_object* v_decls_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_lctx_1645_ = lean_ctor_get(v_a_1640_, 2);
v_decls_1646_ = lean_ctor_get(v_lctx_1645_, 1);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1646_, v___x_1647_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1649_; 
lean_dec_ref_known(v___x_1648_, 1);
v___x_1649_ = l_Lean_MVarId_getType(v_mvarId_1636_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1650_, v_a_1641_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1652_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1653_;
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_a_1654_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1651_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1651_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1649_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1649_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_dec(v_mvarId_1636_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1680_, v_x_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_a_1696_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1687_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1687_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1704_, v_x_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1712_, lean_object* v_mvarId_1713_, lean_object* v_x_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1713_, v_x_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1721_, lean_object* v_mvarId_1722_, lean_object* v_x_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1721_, v_mvarId_1722_, v_x_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_mvarId_1732_, lean_object* v_needle_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_st_mk_ref(v___x_1730_);
v___x_1740_ = lean_st_mk_ref(v___x_1731_);
v___x_1741_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1732_, v___x_1740_, v_needle_1733_, v___x_1739_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1751_; 
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1752_);
v___x_1743_ = v___x_1741_;
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v___x_1741_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v_calls_1747_; lean_object* v___x_1749_; 
v___x_1745_ = lean_st_ref_get(v___x_1740_);
lean_dec(v___x_1740_);
lean_dec(v___x_1745_);
v___x_1746_ = lean_st_ref_get(v___x_1739_);
lean_dec(v___x_1739_);
v_calls_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_ref(v_calls_1747_);
lean_dec(v___x_1746_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_calls_1747_);
v___x_1749_ = v___x_1743_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_calls_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v___x_1740_);
lean_dec(v___x_1739_);
v_a_1753_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1741_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1741_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v_mvarId_1763_, lean_object* v_needle_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1761_, v___x_1762_, v_mvarId_1763_, v_needle_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v_needle_1764_);
return v_res_1770_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_unsigned_to_nat(64u);
v___x_1772_ = l_Lean_mkPtrSet___redArg(v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1773_, lean_object* v_mvarId_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_1781_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
lean_inc(v_mvarId_1774_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1782_, 0, v___x_1781_);
lean_closure_set(v___f_1782_, 1, v___x_1780_);
lean_closure_set(v___f_1782_, 2, v_mvarId_1774_);
lean_closure_set(v___f_1782_, 3, v_needle_1773_);
v___x_1783_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1774_, v___f_1782_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_1784_, lean_object* v_mvarId_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1784_, v_mvarId_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_1792_, lean_object* v_mvarId_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1792_, v_mvarId_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_1800_, lean_object* v_mvarId_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1800_, v_mvarId_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_1808_, lean_object* v_mvarId_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1808_, v_mvarId_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_1816_, lean_object* v_mvarId_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Meta_FunInd_collect(v_needle_1816_, v_mvarId_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
return v_res_1823_;
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
