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
uint8_t lean_bool_not(uint8_t);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_106_; uint64_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1723u);
v___x_107_ = lean_uint64_of_nat(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
return v_x_108_;
}
else
{
lean_object* v_key_110_; lean_object* v_value_111_; lean_object* v_tail_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_155_; 
v_key_110_ = lean_ctor_get(v_x_109_, 0);
v_value_111_ = lean_ctor_get(v_x_109_, 1);
v_tail_112_ = lean_ctor_get(v_x_109_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_109_);
if (v_isSharedCheck_155_ == 0)
{
v___x_114_ = v_x_109_;
v_isShared_115_ = v_isSharedCheck_155_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_tail_112_);
lean_inc(v_value_111_);
lean_inc(v_key_110_);
lean_dec(v_x_109_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_155_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_118_; uint64_t v___y_120_; uint64_t v___y_121_; uint64_t v___y_141_; 
v_fst_116_ = lean_ctor_get(v_key_110_, 0);
v_snd_117_ = lean_ctor_get(v_key_110_, 1);
v___x_118_ = lean_array_get_size(v_x_108_);
if (lean_obj_tag(v_fst_116_) == 0)
{
uint64_t v___x_153_; 
v___x_153_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___y_141_ = v___x_153_;
goto v___jp_140_;
}
else
{
uint64_t v_hash_154_; 
v_hash_154_ = lean_ctor_get_uint64(v_fst_116_, sizeof(void*)*2);
v___y_141_ = v_hash_154_;
goto v___jp_140_;
}
v___jp_119_:
{
uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v_fold_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_122_ = lean_uint64_mix_hash(v___y_120_, v___y_121_);
v___x_123_ = 32ULL;
v___x_124_ = lean_uint64_shift_right(v___x_122_, v___x_123_);
v_fold_125_ = lean_uint64_xor(v___x_122_, v___x_124_);
v___x_126_ = 16ULL;
v___x_127_ = lean_uint64_shift_right(v_fold_125_, v___x_126_);
v___x_128_ = lean_uint64_xor(v_fold_125_, v___x_127_);
v___x_129_ = lean_uint64_to_usize(v___x_128_);
v___x_130_ = lean_usize_of_nat(v___x_118_);
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_sub(v___x_130_, v___x_131_);
v___x_133_ = lean_usize_land(v___x_129_, v___x_132_);
v___x_134_ = lean_array_uget_borrowed(v_x_108_, v___x_133_);
lean_inc(v___x_134_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 2, v___x_134_);
v___x_136_ = v___x_114_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_key_110_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_value_111_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v___x_134_);
v___x_136_ = v_reuseFailAlloc_139_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; 
v___x_137_ = lean_array_uset(v_x_108_, v___x_133_, v___x_136_);
v_x_108_ = v___x_137_;
v_x_109_ = v_tail_112_;
goto _start;
}
}
v___jp_140_:
{
uint64_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_142_ = 7ULL;
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_array_get_size(v_snd_117_);
v___x_145_ = lean_nat_dec_lt(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
v___y_120_ = v___y_141_;
v___y_121_ = v___x_142_;
goto v___jp_119_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_le(v___x_144_, v___x_144_);
if (v___x_146_ == 0)
{
if (v___x_145_ == 0)
{
v___y_120_ = v___y_141_;
v___y_121_ = v___x_142_;
goto v___jp_119_;
}
else
{
size_t v___x_147_; size_t v___x_148_; uint64_t v___x_149_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_144_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_117_, v___x_147_, v___x_148_, v___x_142_);
v___y_120_ = v___y_141_;
v___y_121_ = v___x_149_;
goto v___jp_119_;
}
}
else
{
size_t v___x_150_; size_t v___x_151_; uint64_t v___x_152_; 
v___x_150_ = ((size_t)0ULL);
v___x_151_ = lean_usize_of_nat(v___x_144_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_117_, v___x_150_, v___x_151_, v___x_142_);
v___y_120_ = v___y_141_;
v___y_121_ = v___x_152_;
goto v___jp_119_;
}
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
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_nbuckets_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_169_ = lean_array_get_size(v_data_168_);
v___x_170_ = lean_unsigned_to_nat(2u);
v_nbuckets_171_ = lean_nat_mul(v___x_169_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_box(0);
v___x_174_ = lean_mk_array(v_nbuckets_171_, v___x_173_);
v___x_175_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v___x_172_, v_data_168_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object* v_m_176_, lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
lean_object* v_size_179_; lean_object* v_buckets_180_; lean_object* v_fst_181_; lean_object* v_snd_182_; lean_object* v___x_183_; uint64_t v___y_185_; uint64_t v___y_186_; uint64_t v___y_225_; 
v_size_179_ = lean_ctor_get(v_m_176_, 0);
v_buckets_180_ = lean_ctor_get(v_m_176_, 1);
v_fst_181_ = lean_ctor_get(v_a_177_, 0);
v_snd_182_ = lean_ctor_get(v_a_177_, 1);
v___x_183_ = lean_array_get_size(v_buckets_180_);
if (lean_obj_tag(v_fst_181_) == 0)
{
uint64_t v___x_237_; 
v___x_237_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___y_225_ = v___x_237_;
goto v___jp_224_;
}
else
{
uint64_t v_hash_238_; 
v_hash_238_ = lean_ctor_get_uint64(v_fst_181_, sizeof(void*)*2);
v___y_225_ = v_hash_238_;
goto v___jp_224_;
}
v___jp_184_:
{
uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v_fold_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; lean_object* v_bkt_199_; uint8_t v___x_200_; 
v___x_187_ = lean_uint64_mix_hash(v___y_185_, v___y_186_);
v___x_188_ = 32ULL;
v___x_189_ = lean_uint64_shift_right(v___x_187_, v___x_188_);
v_fold_190_ = lean_uint64_xor(v___x_187_, v___x_189_);
v___x_191_ = 16ULL;
v___x_192_ = lean_uint64_shift_right(v_fold_190_, v___x_191_);
v___x_193_ = lean_uint64_xor(v_fold_190_, v___x_192_);
v___x_194_ = lean_uint64_to_usize(v___x_193_);
v___x_195_ = lean_usize_of_nat(v___x_183_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_sub(v___x_195_, v___x_196_);
v___x_198_ = lean_usize_land(v___x_194_, v___x_197_);
v_bkt_199_ = lean_array_uget_borrowed(v_buckets_180_, v___x_198_);
v___x_200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_177_, v_bkt_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_221_; 
lean_inc_ref(v_buckets_180_);
lean_inc(v_size_179_);
v_isSharedCheck_221_ = !lean_is_exclusive(v_m_176_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; lean_object* v_unused_223_; 
v_unused_222_ = lean_ctor_get(v_m_176_, 1);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_m_176_, 0);
lean_dec(v_unused_223_);
v___x_202_ = v_m_176_;
v_isShared_203_ = v_isSharedCheck_221_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_m_176_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_221_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v_size_x27_205_; lean_object* v___x_206_; lean_object* v_buckets_x27_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_204_ = lean_unsigned_to_nat(1u);
v_size_x27_205_ = lean_nat_add(v_size_179_, v___x_204_);
lean_dec(v_size_179_);
lean_inc(v_bkt_199_);
v___x_206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_206_, 0, v_a_177_);
lean_ctor_set(v___x_206_, 1, v_b_178_);
lean_ctor_set(v___x_206_, 2, v_bkt_199_);
v_buckets_x27_207_ = lean_array_uset(v_buckets_180_, v___x_198_, v___x_206_);
v___x_208_ = lean_unsigned_to_nat(4u);
v___x_209_ = lean_nat_mul(v_size_x27_205_, v___x_208_);
v___x_210_ = lean_unsigned_to_nat(3u);
v___x_211_ = lean_nat_div(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_array_get_size(v_buckets_x27_207_);
v___x_213_ = lean_nat_dec_le(v___x_211_, v___x_212_);
lean_dec(v___x_211_);
if (v___x_213_ == 0)
{
lean_object* v_val_214_; lean_object* v___x_216_; 
v_val_214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_buckets_x27_207_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_val_214_);
lean_ctor_set(v___x_202_, 0, v_size_x27_205_);
v___x_216_ = v___x_202_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_size_x27_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_val_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
else
{
lean_object* v___x_219_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_buckets_x27_207_);
lean_ctor_set(v___x_202_, 0, v_size_x27_205_);
v___x_219_ = v___x_202_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_size_x27_205_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_buckets_x27_207_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
else
{
lean_dec(v_b_178_);
lean_dec_ref(v_a_177_);
return v_m_176_;
}
}
v___jp_224_:
{
uint64_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_226_ = 7ULL;
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_array_get_size(v_snd_182_);
v___x_229_ = lean_nat_dec_lt(v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
v___y_185_ = v___y_225_;
v___y_186_ = v___x_226_;
goto v___jp_184_;
}
else
{
uint8_t v___x_230_; 
v___x_230_ = lean_nat_dec_le(v___x_228_, v___x_228_);
if (v___x_230_ == 0)
{
if (v___x_229_ == 0)
{
v___y_185_ = v___y_225_;
v___y_186_ = v___x_226_;
goto v___jp_184_;
}
else
{
size_t v___x_231_; size_t v___x_232_; uint64_t v___x_233_; 
v___x_231_ = ((size_t)0ULL);
v___x_232_ = lean_usize_of_nat(v___x_228_);
v___x_233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_182_, v___x_231_, v___x_232_, v___x_226_);
v___y_185_ = v___y_225_;
v___y_186_ = v___x_233_;
goto v___jp_184_;
}
}
else
{
size_t v___x_234_; size_t v___x_235_; uint64_t v___x_236_; 
v___x_234_ = ((size_t)0ULL);
v___x_235_ = lean_usize_of_nat(v___x_228_);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_182_, v___x_234_, v___x_235_, v___x_226_);
v___y_185_ = v___y_225_;
v___y_186_ = v___x_236_;
goto v___jp_184_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object* v_m_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_buckets_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; uint64_t v___y_246_; uint64_t v___y_247_; uint64_t v___y_263_; 
v_buckets_241_ = lean_ctor_get(v_m_239_, 1);
v_fst_242_ = lean_ctor_get(v_a_240_, 0);
v_snd_243_ = lean_ctor_get(v_a_240_, 1);
v___x_244_ = lean_array_get_size(v_buckets_241_);
if (lean_obj_tag(v_fst_242_) == 0)
{
uint64_t v___x_275_; 
v___x_275_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
v___y_263_ = v___x_275_;
goto v___jp_262_;
}
else
{
uint64_t v_hash_276_; 
v_hash_276_ = lean_ctor_get_uint64(v_fst_242_, sizeof(void*)*2);
v___y_263_ = v_hash_276_;
goto v___jp_262_;
}
v___jp_245_:
{
uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v_fold_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_248_ = lean_uint64_mix_hash(v___y_246_, v___y_247_);
v___x_249_ = 32ULL;
v___x_250_ = lean_uint64_shift_right(v___x_248_, v___x_249_);
v_fold_251_ = lean_uint64_xor(v___x_248_, v___x_250_);
v___x_252_ = 16ULL;
v___x_253_ = lean_uint64_shift_right(v_fold_251_, v___x_252_);
v___x_254_ = lean_uint64_xor(v_fold_251_, v___x_253_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
v___x_256_ = lean_usize_of_nat(v___x_244_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_sub(v___x_256_, v___x_257_);
v___x_259_ = lean_usize_land(v___x_255_, v___x_258_);
v___x_260_ = lean_array_uget_borrowed(v_buckets_241_, v___x_259_);
v___x_261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_240_, v___x_260_);
return v___x_261_;
}
v___jp_262_:
{
uint64_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_264_ = 7ULL;
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_array_get_size(v_snd_243_);
v___x_267_ = lean_nat_dec_lt(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
v___y_246_ = v___y_263_;
v___y_247_ = v___x_264_;
goto v___jp_245_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_le(v___x_266_, v___x_266_);
if (v___x_268_ == 0)
{
if (v___x_267_ == 0)
{
v___y_246_ = v___y_263_;
v___y_247_ = v___x_264_;
goto v___jp_245_;
}
else
{
size_t v___x_269_; size_t v___x_270_; uint64_t v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_266_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_243_, v___x_269_, v___x_270_, v___x_264_);
v___y_246_ = v___y_263_;
v___y_247_ = v___x_271_;
goto v___jp_245_;
}
}
else
{
size_t v___x_272_; size_t v___x_273_; uint64_t v___x_274_; 
v___x_272_ = ((size_t)0ULL);
v___x_273_ = lean_usize_of_nat(v___x_266_);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__2(v_snd_243_, v___x_272_, v___x_273_, v___x_264_);
v___y_246_ = v___y_263_;
v___y_247_ = v___x_274_;
goto v___jp_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object* v_m_277_, lean_object* v_a_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_277_, v_a_278_);
lean_dec_ref(v_a_278_);
lean_dec_ref(v_m_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object* v___x_281_, lean_object* v___x_282_, lean_object* v_calls_283_, lean_object* v_as_284_, size_t v_sz_285_, size_t v_i_286_, lean_object* v_b_287_){
_start:
{
lean_object* v_a_290_; uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_lt(v_i_286_, v_sz_285_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec_ref(v_calls_283_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v_b_287_);
return v___x_295_;
}
else
{
lean_object* v_snd_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_354_; 
v_snd_296_ = lean_ctor_get(v_b_287_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_b_287_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v_b_287_, 0);
lean_dec(v_unused_355_);
v___x_298_ = v_b_287_;
v_isShared_299_ = v_isSharedCheck_354_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snd_296_);
lean_dec(v_b_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_354_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_snd_300_; lean_object* v_fst_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_353_; 
v_snd_300_ = lean_ctor_get(v_snd_296_, 1);
v_fst_301_ = lean_ctor_get(v_snd_296_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v_snd_296_);
if (v_isSharedCheck_353_ == 0)
{
v___x_303_ = v_snd_296_;
v_isShared_304_ = v_isSharedCheck_353_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_snd_300_);
lean_inc(v_fst_301_);
lean_dec(v_snd_296_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_353_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_array_305_; lean_object* v_start_306_; lean_object* v_stop_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_array_305_ = lean_ctor_get(v_snd_300_, 0);
v_start_306_ = lean_ctor_get(v_snd_300_, 1);
v_stop_307_ = lean_ctor_get(v_snd_300_, 2);
v___x_308_ = lean_box(0);
v___x_309_ = lean_nat_dec_lt(v_start_306_, v_stop_307_);
if (v___x_309_ == 0)
{
lean_object* v___x_311_; 
lean_dec_ref(v_calls_283_);
if (v_isShared_304_ == 0)
{
v___x_311_ = v___x_303_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_fst_301_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_snd_300_);
v___x_311_ = v_reuseFailAlloc_316_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_311_);
lean_ctor_set(v___x_298_, 0, v___x_308_);
v___x_313_ = v___x_298_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_315_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
}
else
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_349_; 
lean_inc(v_stop_307_);
lean_inc(v_start_306_);
lean_inc_ref(v_array_305_);
v_isSharedCheck_349_ = !lean_is_exclusive(v_snd_300_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_350_ = lean_ctor_get(v_snd_300_, 2);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_snd_300_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_snd_300_, 0);
lean_dec(v_unused_352_);
v___x_318_ = v_snd_300_;
v_isShared_319_ = v_isSharedCheck_349_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_snd_300_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_349_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; uint8_t v___x_321_; lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_320_ = lean_nat_dec_eq(v___x_281_, v___x_282_);
v___x_321_ = lean_bool_not(v___x_320_);
v_a_322_ = lean_array_uget_borrowed(v_as_284_, v_i_286_);
v___x_323_ = lean_array_fget(v_array_305_, v_start_306_);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_start_306_, v___x_324_);
lean_dec(v_start_306_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_325_);
v___x_327_ = v___x_318_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_array_305_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_stop_307_);
v___x_327_ = v_reuseFailAlloc_348_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
uint8_t v___x_347_; 
v___x_347_ = lean_unbox(v___x_323_);
if (v___x_347_ == 2)
{
goto v___jp_340_;
}
else
{
if (v___x_321_ == 0)
{
goto v___jp_335_;
}
else
{
goto v___jp_340_;
}
}
v___jp_328_:
{
lean_object* v___x_330_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_327_);
v___x_330_ = v___x_303_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_fst_301_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_327_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_330_);
lean_ctor_set(v___x_298_, 0, v___x_308_);
v___x_332_ = v___x_298_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
v_a_290_ = v___x_332_;
goto v___jp_289_;
}
}
}
v___jp_335_:
{
uint8_t v___x_336_; 
v___x_336_ = lean_unbox(v___x_323_);
lean_dec(v___x_323_);
if (v___x_336_ == 0)
{
goto v___jp_328_;
}
else
{
if (v___x_321_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_del_object(v___x_303_);
lean_del_object(v___x_298_);
lean_inc(v_a_322_);
v___x_337_ = lean_array_push(v_fst_301_, v_a_322_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_327_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_308_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v_a_290_ = v___x_339_;
goto v___jp_289_;
}
else
{
goto v___jp_328_;
}
}
}
v___jp_340_:
{
uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = l_Lean_Expr_isFVar(v_a_322_);
v___x_342_ = lean_bool_not(v___x_341_);
if (v___x_342_ == 0)
{
goto v___jp_335_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v___x_323_);
lean_del_object(v___x_303_);
lean_del_object(v___x_298_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_calls_283_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_fst_301_);
lean_ctor_set(v___x_344_, 1, v___x_327_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
}
}
}
}
}
v___jp_289_:
{
size_t v___x_291_; size_t v___x_292_; 
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_286_, v___x_291_);
v_i_286_ = v___x_292_;
v_b_287_ = v_a_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object* v___x_356_, lean_object* v___x_357_, lean_object* v_calls_358_, lean_object* v_as_359_, lean_object* v_sz_360_, lean_object* v_i_361_, lean_object* v_b_362_, lean_object* v___y_363_){
_start:
{
size_t v_sz_boxed_364_; size_t v_i_boxed_365_; lean_object* v_res_366_; 
v_sz_boxed_364_ = lean_unbox_usize(v_sz_360_);
lean_dec(v_sz_360_);
v_i_boxed_365_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v___x_356_, v___x_357_, v_calls_358_, v_as_359_, v_sz_boxed_364_, v_i_boxed_365_, v_b_362_);
lean_dec_ref(v_as_359_);
lean_dec(v___x_357_);
lean_dec(v___x_356_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object* v_e_367_, lean_object* v_funIndInfo_368_, lean_object* v_args_369_, lean_object* v_calls_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_funName_376_; lean_object* v_params_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; uint8_t v___x_381_; 
v_funName_376_ = lean_ctor_get(v_funIndInfo_368_, 0);
lean_inc(v_funName_376_);
v_params_377_ = lean_ctor_get(v_funIndInfo_368_, 3);
lean_inc_ref(v_params_377_);
lean_dec_ref(v_funIndInfo_368_);
v___x_378_ = lean_array_get_size(v_params_377_);
v___x_379_ = lean_array_get_size(v_args_369_);
v___x_380_ = lean_nat_dec_eq(v___x_378_, v___x_379_);
v___x_381_ = lean_bool_not(v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v_keys_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; size_t v_sz_388_; size_t v___x_389_; lean_object* v___x_390_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v_keys_383_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_384_ = l_Array_toSubarray___redArg(v_params_377_, v___x_382_, v___x_378_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_keys_383_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v_sz_388_ = lean_array_size(v_args_369_);
v___x_389_ = ((size_t)0ULL);
lean_inc_ref(v_calls_370_);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v___x_378_, v___x_379_, v_calls_370_, v_args_369_, v_sz_388_, v___x_389_, v___x_387_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_431_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_431_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_431_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_431_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_fst_395_; 
v_fst_395_ = lean_ctor_get(v_a_391_, 0);
if (lean_obj_tag(v_fst_395_) == 0)
{
lean_object* v_snd_396_; lean_object* v_fst_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_425_; 
v_snd_396_ = lean_ctor_get(v_a_391_, 1);
lean_inc(v_snd_396_);
lean_dec(v_a_391_);
v_fst_397_ = lean_ctor_get(v_snd_396_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_snd_396_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_snd_396_, 1);
lean_dec(v_unused_426_);
v___x_399_ = v_snd_396_;
v_isShared_400_ = v_isSharedCheck_425_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_fst_397_);
lean_dec(v_snd_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_425_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_calls_401_; lean_object* v_seen_402_; lean_object* v___x_404_; 
v_calls_401_ = lean_ctor_get(v_calls_370_, 0);
v_seen_402_ = lean_ctor_get(v_calls_370_, 1);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v_fst_397_);
lean_ctor_set(v___x_399_, 0, v_funName_376_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_funName_376_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_fst_397_);
v___x_404_ = v_reuseFailAlloc_424_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
uint8_t v___x_405_; 
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_402_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_418_; 
lean_inc_ref(v_seen_402_);
lean_inc_ref(v_calls_401_);
v_isSharedCheck_418_ = !lean_is_exclusive(v_calls_370_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_419_ = lean_ctor_get(v_calls_370_, 1);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_calls_370_, 0);
lean_dec(v_unused_420_);
v___x_407_ = v_calls_370_;
v_isShared_408_ = v_isSharedCheck_418_;
goto v_resetjp_406_;
}
else
{
lean_dec(v_calls_370_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_418_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_409_ = lean_array_push(v_calls_401_, v_e_367_);
v___x_410_ = lean_box(0);
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_402_, v___x_404_, v___x_410_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v___x_411_);
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_413_ = v___x_407_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_413_);
v___x_415_ = v___x_393_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
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
else
{
lean_object* v___x_422_; 
lean_dec_ref(v___x_404_);
lean_dec_ref(v_e_367_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v_calls_370_);
v___x_422_ = v___x_393_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_calls_370_);
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
}
else
{
lean_object* v_val_427_; lean_object* v___x_429_; 
lean_inc_ref(v_fst_395_);
lean_dec(v_a_391_);
lean_dec(v_funName_376_);
lean_dec_ref(v_calls_370_);
lean_dec_ref(v_e_367_);
v_val_427_ = lean_ctor_get(v_fst_395_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v_fst_395_, 1);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v_val_427_);
v___x_429_ = v___x_393_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_val_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_funName_376_);
lean_dec_ref(v_calls_370_);
lean_dec_ref(v_e_367_);
v_a_432_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_390_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_390_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
lean_object* v___x_440_; 
lean_dec_ref(v_params_377_);
lean_dec(v_funName_376_);
lean_dec_ref(v_e_367_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_calls_370_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object* v_e_441_, lean_object* v_funIndInfo_442_, lean_object* v_args_443_, lean_object* v_calls_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_441_, v_funIndInfo_442_, v_args_443_, v_calls_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec_ref(v_args_443_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v_calls_453_, lean_object* v_as_454_, size_t v_sz_455_, size_t v_i_456_, lean_object* v_b_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v___x_451_, v___x_452_, v_calls_453_, v_as_454_, v_sz_455_, v_i_456_, v_b_457_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v_calls_466_, lean_object* v_as_467_, lean_object* v_sz_468_, lean_object* v_i_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
size_t v_sz_boxed_476_; size_t v_i_boxed_477_; lean_object* v_res_478_; 
v_sz_boxed_476_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_477_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v___x_464_, v___x_465_, v_calls_466_, v_as_467_, v_sz_boxed_476_, v_i_boxed_477_, v_b_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec_ref(v_as_467_);
lean_dec(v___x_465_);
lean_dec(v___x_464_);
return v_res_478_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object* v_00_u03b2_479_, lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_480_, v_a_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object* v_00_u03b2_483_, lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(v_00_u03b2_483_, v_m_484_, v_a_485_);
lean_dec_ref(v_a_485_);
lean_dec_ref(v_m_484_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object* v_00_u03b2_488_, lean_object* v_m_489_, lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_489_, v_a_490_, v_b_491_);
return v___x_492_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object* v_00_u03b2_493_, lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_494_, v_x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object* v_00_u03b2_497_, lean_object* v_a_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_497_, v_a_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec_ref(v_a_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object* v_00_u03b2_502_, lean_object* v_data_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_503_);
return v___x_504_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(lean_object* v_xs_505_, lean_object* v_ys_506_, lean_object* v_hsz_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_505_, v_ys_506_, v_x_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_511_, lean_object* v_ys_512_, lean_object* v_hsz_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(v_xs_511_, v_ys_512_, v_hsz_513_, v_x_514_, v_x_515_);
lean_dec_ref(v_ys_512_);
lean_dec_ref(v_xs_511_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_518_, lean_object* v_i_519_, lean_object* v_source_520_, lean_object* v_target_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6___redArg(v_i_519_, v_source_520_, v_target_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4_spec__6_spec__7___redArg(v_x_524_, v_x_525_);
return v___x_526_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object* v_snd_527_, lean_object* v_x_528_){
_start:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = l_Lean_NameSet_contains(v_snd_527_, v_x_528_);
v___x_530_ = lean_bool_not(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object* v_snd_531_, lean_object* v_x_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_531_, v_x_532_);
lean_dec(v_x_532_);
lean_dec(v_snd_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
if (lean_obj_tag(v_a_535_) == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v_a_536_);
return v___x_537_;
}
else
{
lean_object* v_key_538_; lean_object* v_tail_539_; lean_object* v_fst_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_562_; 
v_key_538_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_key_538_);
v_tail_539_ = lean_ctor_get(v_a_535_, 2);
lean_inc(v_tail_539_);
lean_dec_ref_known(v_a_535_, 3);
v_fst_540_ = lean_ctor_get(v_key_538_, 0);
lean_inc(v_fst_540_);
lean_dec(v_key_538_);
v_fst_541_ = lean_ctor_get(v_a_536_, 0);
v_snd_542_ = lean_ctor_get(v_a_536_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_562_ == 0)
{
v___x_544_ = v_a_536_;
v_isShared_545_ = v_isSharedCheck_562_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v_a_536_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_562_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_NameSet_contains(v_snd_542_, v_fst_540_);
if (v___x_546_ == 0)
{
uint8_t v___x_547_; 
v___x_547_ = l_Lean_NameSet_contains(v_fst_541_, v_fst_540_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = l_Lean_NameSet_insert(v_fst_541_, v_fst_540_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_548_);
v___x_550_ = v___x_544_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_snd_542_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v_a_535_ = v_tail_539_;
v_a_536_ = v___x_550_;
goto _start;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Lean_NameSet_insert(v_snd_542_, v_fst_540_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_553_);
v___x_555_ = v___x_544_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_fst_541_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v_a_535_ = v_tail_539_;
v_a_536_ = v___x_555_;
goto _start;
}
}
}
else
{
lean_object* v___x_559_; 
lean_dec(v_fst_540_);
if (v_isShared_545_ == 0)
{
v___x_559_ = v___x_544_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_fst_541_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_snd_542_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
v_a_535_ = v_tail_539_;
v_a_536_ = v___x_559_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(lean_object* v_as_563_, size_t v_sz_564_, size_t v_i_565_, lean_object* v_b_566_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = lean_usize_dec_lt(v_i_565_, v_sz_564_);
if (v___x_567_ == 0)
{
return v_b_566_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_array_uget_borrowed(v_as_563_, v_i_565_);
lean_inc(v_a_568_);
v___x_569_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_568_, v_b_566_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
return v_a_570_;
}
else
{
lean_object* v_a_571_; size_t v___x_572_; size_t v___x_573_; 
v_a_571_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_569_, 1);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_i_565_, v___x_572_);
v_i_565_ = v___x_573_;
v_b_566_ = v_a_571_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(lean_object* v_as_575_, lean_object* v_sz_576_, lean_object* v_i_577_, lean_object* v_b_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_576_);
lean_dec(v_sz_576_);
v_i_boxed_580_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_575_, v_sz_boxed_579_, v_i_boxed_580_, v_b_578_);
lean_dec_ref(v_as_575_);
return v_res_581_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0(void){
_start:
{
lean_object* v_seen_582_; lean_object* v___x_583_; 
v_seen_582_ = l_Lean_NameSet_empty;
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_seen_582_);
lean_ctor_set(v___x_583_, 1, v_seen_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object* v_calls_584_){
_start:
{
lean_object* v_seen_585_; lean_object* v___x_586_; lean_object* v_buckets_587_; size_t v_sz_588_; size_t v___x_589_; lean_object* v___x_590_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___f_593_; lean_object* v___x_594_; 
v_seen_585_ = lean_ctor_get(v_calls_584_, 1);
v___x_586_ = lean_obj_once(&l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0, &l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once, _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0);
v_buckets_587_ = lean_ctor_get(v_seen_585_, 1);
v_sz_588_ = lean_array_size(v_buckets_587_);
v___x_589_ = ((size_t)0ULL);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_587_, v_sz_588_, v___x_589_, v___x_586_);
v_fst_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v___x_590_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed), 2, 1);
lean_closure_set(v___f_593_, 0, v_snd_592_);
v___x_594_ = l_Lean_NameSet_filter(v___f_593_, v_fst_591_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object* v_calls_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_595_);
lean_dec_ref(v_calls_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object* v_e_597_, lean_object* v_funIndInfo_598_, lean_object* v_args_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_st_ref_get(v_a_600_);
v___x_607_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_597_, v_funIndInfo_598_, v_args_599_, v___x_606_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_616_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_st_ref_set(v_a_600_, v_a_608_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_607_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_607_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object* v_e_625_, lean_object* v_funIndInfo_626_, lean_object* v_args_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_625_, v_funIndInfo_626_, v_args_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_args_627_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object* v_e_635_, lean_object* v_funIndInfo_636_, lean_object* v_args_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_635_, v_funIndInfo_636_, v_args_637_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object* v_e_646_, lean_object* v_funIndInfo_647_, lean_object* v_args_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_646_, v_funIndInfo_647_, v_args_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_args_648_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object* v_e_657_, lean_object* v_funIndInfo_658_, lean_object* v_args_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_657_, v_funIndInfo_658_, v_args_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object* v_e_667_, lean_object* v_funIndInfo_668_, lean_object* v_args_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_667_, v_funIndInfo_668_, v_args_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_args_669_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object* v_e_677_, lean_object* v_funIndInfo_678_, lean_object* v_args_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_677_, v_funIndInfo_678_, v_args_679_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object* v_e_688_, lean_object* v_funIndInfo_689_, lean_object* v_args_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_688_, v_funIndInfo_689_, v_args_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec_ref(v_args_690_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
return v_x_699_;
}
else
{
lean_object* v_key_701_; lean_object* v_value_702_; lean_object* v_tail_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_729_; 
v_key_701_ = lean_ctor_get(v_x_700_, 0);
v_value_702_ = lean_ctor_get(v_x_700_, 1);
v_tail_703_ = lean_ctor_get(v_x_700_, 2);
v_isSharedCheck_729_ = !lean_is_exclusive(v_x_700_);
if (v_isSharedCheck_729_ == 0)
{
v___x_705_ = v_x_700_;
v_isShared_706_ = v_isSharedCheck_729_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_tail_703_);
lean_inc(v_value_702_);
lean_inc(v_key_701_);
lean_dec(v_x_700_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_729_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; size_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v_fold_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_707_ = lean_array_get_size(v_x_699_);
v___x_708_ = lean_ptr_addr(v_key_701_);
v___x_709_ = lean_usize_to_uint64(v___x_708_);
v___x_710_ = 11ULL;
v___x_711_ = lean_uint64_mix_hash(v___x_709_, v___x_710_);
v___x_712_ = 32ULL;
v___x_713_ = lean_uint64_shift_right(v___x_711_, v___x_712_);
v_fold_714_ = lean_uint64_xor(v___x_711_, v___x_713_);
v___x_715_ = 16ULL;
v___x_716_ = lean_uint64_shift_right(v_fold_714_, v___x_715_);
v___x_717_ = lean_uint64_xor(v_fold_714_, v___x_716_);
v___x_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = lean_usize_of_nat(v___x_707_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_sub(v___x_719_, v___x_720_);
v___x_722_ = lean_usize_land(v___x_718_, v___x_721_);
v___x_723_ = lean_array_uget_borrowed(v_x_699_, v___x_722_);
lean_inc(v___x_723_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 2, v___x_723_);
v___x_725_ = v___x_705_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_key_701_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_value_702_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v___x_723_);
v___x_725_ = v_reuseFailAlloc_728_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_array_uset(v_x_699_, v___x_722_, v___x_725_);
v_x_699_ = v___x_726_;
v_x_700_ = v_tail_703_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(lean_object* v_i_730_, lean_object* v_source_731_, lean_object* v_target_732_){
_start:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = lean_array_get_size(v_source_731_);
v___x_734_ = lean_nat_dec_lt(v_i_730_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec_ref(v_source_731_);
lean_dec(v_i_730_);
return v_target_732_;
}
else
{
lean_object* v_es_735_; lean_object* v___x_736_; lean_object* v_source_737_; lean_object* v_target_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_es_735_ = lean_array_fget(v_source_731_, v_i_730_);
v___x_736_ = lean_box(0);
v_source_737_ = lean_array_fset(v_source_731_, v_i_730_, v___x_736_);
v_target_738_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_732_, v_es_735_);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_i_730_, v___x_739_);
lean_dec(v_i_730_);
v_i_730_ = v___x_740_;
v_source_731_ = v_source_737_;
v_target_732_ = v_target_738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(lean_object* v_data_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_nbuckets_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_743_ = lean_array_get_size(v_data_742_);
v___x_744_ = lean_unsigned_to_nat(2u);
v_nbuckets_745_ = lean_nat_mul(v___x_743_, v___x_744_);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_box(0);
v___x_748_ = lean_mk_array(v_nbuckets_745_, v___x_747_);
v___x_749_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_746_, v_data_742_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
uint8_t v___x_752_; 
v___x_752_ = 0;
return v___x_752_;
}
else
{
lean_object* v_key_753_; lean_object* v_tail_754_; size_t v___x_755_; size_t v___x_756_; uint8_t v___x_757_; 
v_key_753_ = lean_ctor_get(v_x_751_, 0);
v_tail_754_ = lean_ctor_get(v_x_751_, 2);
v___x_755_ = lean_ptr_addr(v_key_753_);
v___x_756_ = lean_ptr_addr(v_a_750_);
v___x_757_ = lean_usize_dec_eq(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
v_x_751_ = v_tail_754_;
goto _start;
}
else
{
return v___x_757_;
}
}
}
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_809_, lean_object* v_a_810_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_830_, lean_object* v_a_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_830_, v_a_831_);
lean_dec_ref(v_a_831_);
lean_dec_ref(v_m_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_834_; lean_object* v_dummy_835_; 
v___x_834_ = lean_box(0);
v_dummy_835_ = l_Lean_Expr_sort___override(v___x_834_);
return v_dummy_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_e_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; 
if (lean_obj_tag(v_x_837_) == 5)
{
lean_object* v_fn_869_; lean_object* v_arg_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_fn_869_ = lean_ctor_get(v_x_837_, 0);
lean_inc_ref(v_fn_869_);
v_arg_870_ = lean_ctor_get(v_x_837_, 1);
lean_inc_ref(v_arg_870_);
lean_dec_ref_known(v_x_837_, 2);
v___x_871_ = lean_array_set(v_x_838_, v_x_839_, v_arg_870_);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_sub(v_x_839_, v___x_872_);
lean_dec(v_x_839_);
v_x_837_ = v_fn_869_;
v_x_838_ = v___x_871_;
v_x_839_ = v___x_873_;
goto _start;
}
else
{
lean_dec(v_x_839_);
if (lean_obj_tag(v_x_837_) == 4)
{
lean_object* v_declName_875_; lean_object* v_funName_876_; uint8_t v___x_877_; 
v_declName_875_ = lean_ctor_get(v_x_837_, 0);
lean_inc(v_declName_875_);
lean_dec_ref_known(v_x_837_, 2);
v_funName_876_ = lean_ctor_get(v___y_841_, 0);
v___x_877_ = lean_name_eq(v_declName_875_, v_funName_876_);
lean_dec(v_declName_875_);
if (v___x_877_ == 0)
{
lean_dec_ref(v_e_836_);
v___y_849_ = v___y_840_;
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
goto v___jp_848_;
}
else
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_Expr_hasLooseBVars(v_e_836_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
lean_inc_ref(v___y_841_);
v___x_879_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_836_, v___y_841_, v_x_838_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_dec_ref_known(v___x_879_, 1);
v___y_849_ = v___y_840_;
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
goto v___jp_848_;
}
else
{
lean_dec_ref(v_x_838_);
return v___x_879_;
}
}
else
{
lean_dec_ref(v_e_836_);
v___y_849_ = v___y_840_;
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
goto v___jp_848_;
}
}
}
else
{
lean_object* v___x_880_; 
lean_dec_ref(v_e_836_);
v___x_880_ = l_Lean_Meta_FunInd_Collector_visit(v_x_837_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_dec_ref_known(v___x_880_, 1);
v___y_849_ = v___y_840_;
v___y_850_ = v___y_841_;
v___y_851_ = v___y_842_;
v___y_852_ = v___y_843_;
v___y_853_ = v___y_844_;
v___y_854_ = v___y_845_;
v___y_855_ = v___y_846_;
goto v___jp_848_;
}
else
{
lean_dec_ref(v_x_838_);
return v___x_880_;
}
}
}
v___jp_848_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_array_get_size(v_x_838_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
lean_dec_ref(v_x_838_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
return v___x_860_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_le(v___x_857_, v___x_857_);
if (v___x_861_ == 0)
{
if (v___x_859_ == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v_x_838_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_858_);
return v___x_862_;
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_857_);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_838_, v___x_863_, v___x_864_, v___x_858_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec_ref(v_x_838_);
return v___x_865_;
}
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
v___x_866_ = ((size_t)0ULL);
v___x_867_ = lean_usize_of_nat(v___x_857_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_838_, v___x_866_, v___x_867_, v___x_858_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec_ref(v_x_838_);
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = lean_st_ref_get(v_a_882_);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_890_, v_e_881_);
lean_dec(v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v_d_897_; lean_object* v_b_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; 
v___x_892_ = lean_st_ref_take(v_a_882_);
v___x_893_ = lean_box(0);
lean_inc_ref(v_e_881_);
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_892_, v_e_881_, v___x_893_);
v___x_895_ = lean_st_ref_set(v_a_882_, v___x_894_);
switch(lean_obj_tag(v_e_881_))
{
case 4:
{
lean_object* v___x_908_; 
lean_dec_ref_known(v_e_881_, 2);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_893_);
return v___x_908_;
}
case 7:
{
lean_object* v_binderType_909_; lean_object* v_body_910_; 
v_binderType_909_ = lean_ctor_get(v_e_881_, 1);
lean_inc_ref(v_binderType_909_);
v_body_910_ = lean_ctor_get(v_e_881_, 2);
lean_inc_ref(v_body_910_);
lean_dec_ref_known(v_e_881_, 3);
v_d_897_ = v_binderType_909_;
v_b_898_ = v_body_910_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
v___y_902_ = v_a_885_;
v___y_903_ = v_a_886_;
v___y_904_ = v_a_887_;
v___y_905_ = v_a_888_;
goto v___jp_896_;
}
case 6:
{
lean_object* v_binderType_911_; lean_object* v_body_912_; 
v_binderType_911_ = lean_ctor_get(v_e_881_, 1);
lean_inc_ref(v_binderType_911_);
v_body_912_ = lean_ctor_get(v_e_881_, 2);
lean_inc_ref(v_body_912_);
lean_dec_ref_known(v_e_881_, 3);
v_d_897_ = v_binderType_911_;
v_b_898_ = v_body_912_;
v___y_899_ = v_a_882_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
v___y_902_ = v_a_885_;
v___y_903_ = v_a_886_;
v___y_904_ = v_a_887_;
v___y_905_ = v_a_888_;
goto v___jp_896_;
}
case 10:
{
lean_object* v_expr_913_; 
v_expr_913_ = lean_ctor_get(v_e_881_, 1);
lean_inc_ref(v_expr_913_);
lean_dec_ref_known(v_e_881_, 2);
v_e_881_ = v_expr_913_;
goto _start;
}
case 8:
{
lean_object* v_type_915_; lean_object* v_value_916_; lean_object* v_body_917_; lean_object* v___x_918_; 
v_type_915_ = lean_ctor_get(v_e_881_, 1);
lean_inc_ref(v_type_915_);
v_value_916_ = lean_ctor_get(v_e_881_, 2);
lean_inc_ref(v_value_916_);
v_body_917_ = lean_ctor_get(v_e_881_, 3);
lean_inc_ref(v_body_917_);
lean_dec_ref_known(v_e_881_, 4);
v___x_918_ = l_Lean_Meta_FunInd_Collector_visit(v_type_915_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v___x_919_; 
lean_dec_ref_known(v___x_918_, 1);
v___x_919_ = l_Lean_Meta_FunInd_Collector_visit(v_value_916_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_dec_ref_known(v___x_919_, 1);
v_e_881_ = v_body_917_;
goto _start;
}
else
{
lean_dec_ref(v_body_917_);
return v___x_919_;
}
}
else
{
lean_dec_ref(v_body_917_);
lean_dec_ref(v_value_916_);
return v___x_918_;
}
}
case 5:
{
lean_object* v_dummy_921_; lean_object* v_nargs_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_dummy_921_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_922_ = l_Lean_Expr_getAppNumArgs(v_e_881_);
lean_inc(v_nargs_922_);
v___x_923_ = lean_mk_array(v_nargs_922_, v_dummy_921_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_sub(v_nargs_922_, v___x_924_);
lean_dec(v_nargs_922_);
lean_inc_ref(v_e_881_);
v___x_926_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_881_, v_e_881_, v___x_923_, v___x_925_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v___x_926_;
}
case 11:
{
lean_object* v_struct_927_; 
v_struct_927_ = lean_ctor_get(v_e_881_, 2);
lean_inc_ref(v_struct_927_);
lean_dec_ref_known(v_e_881_, 3);
v_e_881_ = v_struct_927_;
goto _start;
}
default: 
{
lean_object* v___x_929_; 
lean_dec_ref(v_e_881_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_893_);
return v___x_929_;
}
}
v___jp_896_:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Meta_FunInd_Collector_visit(v_d_897_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_dec_ref_known(v___x_906_, 1);
v_e_881_ = v_b_898_;
v_a_882_ = v___y_899_;
v_a_883_ = v___y_900_;
v_a_884_ = v___y_901_;
v_a_885_ = v___y_902_;
v_a_886_ = v___y_903_;
v_a_887_ = v___y_904_;
v_a_888_ = v___y_905_;
goto _start;
}
else
{
lean_dec_ref(v_b_898_);
return v___x_906_;
}
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_e_881_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_932_, size_t v_i_933_, size_t v_stop_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
uint8_t v___x_944_; 
v___x_944_ = lean_usize_dec_eq(v_i_933_, v_stop_934_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_array_uget_borrowed(v_as_932_, v_i_933_);
lean_inc(v___x_945_);
v___x_946_ = l_Lean_Meta_FunInd_Collector_visit(v___x_945_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; size_t v___x_948_; size_t v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = ((size_t)1ULL);
v___x_949_ = lean_usize_add(v_i_933_, v___x_948_);
v_i_933_ = v___x_949_;
v_b_935_ = v_a_947_;
goto _start;
}
else
{
return v___x_946_;
}
}
else
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_b_935_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_stop_954_, lean_object* v_b_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
size_t v_i_boxed_964_; size_t v_stop_boxed_965_; lean_object* v_res_966_; 
v_i_boxed_964_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_stop_boxed_965_ = lean_unbox_usize(v_stop_954_);
lean_dec(v_stop_954_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_952_, v_i_boxed_964_, v_stop_boxed_965_, v_b_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_as_952_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_FunInd_Collector_visit(v_e_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_e_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_977_, v_x_978_, v_x_979_, v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
return v_res_989_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_990_, lean_object* v_m_991_, lean_object* v_a_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_991_, v_a_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_994_, lean_object* v_m_995_, lean_object* v_a_996_){
_start:
{
uint8_t v_res_997_; lean_object* v_r_998_; 
v_res_997_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_994_, v_m_995_, v_a_996_);
lean_dec_ref(v_a_996_);
lean_dec_ref(v_m_995_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_00_u03b2_999_, lean_object* v_m_1000_, lean_object* v_a_1001_, lean_object* v_b_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_1000_, v_a_1001_, v_b_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_1004_, lean_object* v_a_1005_, lean_object* v_x_1006_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_1005_, v_x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1008_, lean_object* v_a_1009_, lean_object* v_x_1010_){
_start:
{
uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_1008_, v_a_1009_, v_x_1010_);
lean_dec(v_x_1010_);
lean_dec_ref(v_a_1009_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object* v_00_u03b2_1013_, lean_object* v_data_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1016_, lean_object* v_i_1017_, lean_object* v_source_1018_, lean_object* v_target_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_1017_, v_source_1018_, v_target_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1022_, v_x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = l_Lean_Expr_hasMVar(v_e_1025_);
v___x_1029_ = lean_bool_not(v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v_mctx_1031_; lean_object* v___x_1032_; lean_object* v_fst_1033_; lean_object* v_snd_1034_; lean_object* v___x_1035_; lean_object* v_cache_1036_; lean_object* v_zetaDeltaFVarIds_1037_; lean_object* v_postponed_1038_; lean_object* v_diag_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1048_; 
v___x_1030_ = lean_st_ref_get(v___y_1026_);
v_mctx_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref(v_mctx_1031_);
lean_dec(v___x_1030_);
v___x_1032_ = l_Lean_instantiateMVarsCore(v_mctx_1031_, v_e_1025_);
v_fst_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_fst_1033_);
v_snd_1034_ = lean_ctor_get(v___x_1032_, 1);
lean_inc(v_snd_1034_);
lean_dec_ref(v___x_1032_);
v___x_1035_ = lean_st_ref_take(v___y_1026_);
v_cache_1036_ = lean_ctor_get(v___x_1035_, 1);
v_zetaDeltaFVarIds_1037_ = lean_ctor_get(v___x_1035_, 2);
v_postponed_1038_ = lean_ctor_get(v___x_1035_, 3);
v_diag_1039_ = lean_ctor_get(v___x_1035_, 4);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1035_, 0);
lean_dec(v_unused_1049_);
v___x_1041_ = v___x_1035_;
v_isShared_1042_ = v_isSharedCheck_1048_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_diag_1039_);
lean_inc(v_postponed_1038_);
lean_inc(v_zetaDeltaFVarIds_1037_);
lean_inc(v_cache_1036_);
lean_dec(v___x_1035_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1048_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_snd_1034_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_snd_1034_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_cache_1036_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_zetaDeltaFVarIds_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_postponed_1038_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_diag_1039_);
v___x_1044_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_st_ref_set(v___y_1026_, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_fst_1033_);
return v___x_1046_;
}
}
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_e_1025_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1051_, v___y_1052_);
lean_dec(v___y_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1055_, v___y_1060_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1075_, size_t v_sz_1076_, size_t v_i_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_lt(v_i_1077_, v_sz_1076_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_b_1078_);
return v___x_1088_;
}
else
{
lean_object* v_snd_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1147_; 
v_snd_1089_ = lean_ctor_get(v_b_1078_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_b_1078_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v_b_1078_, 0);
lean_dec(v_unused_1148_);
v___x_1091_ = v_b_1078_;
v_isShared_1092_ = v_isSharedCheck_1147_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snd_1089_);
lean_dec(v_b_1078_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1147_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v_a_1095_; lean_object* v_a_1102_; 
v___x_1093_ = lean_box(0);
v_a_1102_ = lean_array_uget_borrowed(v_as_1075_, v_i_1077_);
if (lean_obj_tag(v_a_1102_) == 0)
{
v_a_1095_ = v_snd_1089_;
goto v___jp_1094_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
lean_dec(v_snd_1089_);
v_val_1103_ = lean_ctor_get(v_a_1102_, 0);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Lean_LocalDecl_isAuxDecl(v_val_1103_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_LocalDecl_value_x3f(v_val_1103_, v___x_1105_);
if (lean_obj_tag(v___x_1106_) == 1)
{
lean_object* v_val_1107_; lean_object* v___x_1108_; 
v_val_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1107_, v___y_1083_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1109_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v_a_1095_ = v___x_1104_;
goto v___jp_1094_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_del_object(v___x_1091_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
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
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_del_object(v___x_1091_);
v_a_1119_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1108_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1108_);
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
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v___x_1106_);
v___x_1127_ = l_Lean_LocalDecl_type(v_val_1103_);
v___x_1128_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1127_, v___y_1083_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1129_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_dec_ref_known(v___x_1130_, 1);
v_a_1095_ = v___x_1104_;
goto v___jp_1094_;
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_del_object(v___x_1091_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_del_object(v___x_1091_);
v_a_1139_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1128_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1128_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
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
v_a_1095_ = v___x_1104_;
goto v___jp_1094_;
}
}
v___jp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_a_1095_);
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1097_ = v___x_1091_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_a_1095_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
size_t v___x_1098_; size_t v___x_1099_; 
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_add(v_i_1077_, v___x_1098_);
v_i_1077_ = v___x_1099_;
v_b_1078_ = v___x_1097_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1149_, lean_object* v_sz_1150_, lean_object* v_i_1151_, lean_object* v_b_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1150_);
lean_dec(v_sz_1150_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1149_, v_sz_boxed_1161_, v_i_boxed_1162_, v_b_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v_as_1149_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1164_, size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1167_);
return v___x_1177_;
}
else
{
lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1236_; 
v_snd_1178_ = lean_ctor_get(v_b_1167_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_b_1167_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v_b_1167_, 0);
lean_dec(v_unused_1237_);
v___x_1180_ = v_b_1167_;
v_isShared_1181_ = v_isSharedCheck_1236_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_dec(v_b_1167_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1236_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v_a_1184_; lean_object* v_a_1191_; 
v___x_1182_ = lean_box(0);
v_a_1191_ = lean_array_uget_borrowed(v_as_1164_, v_i_1166_);
if (lean_obj_tag(v_a_1191_) == 0)
{
v_a_1184_ = v_snd_1178_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
lean_dec(v_snd_1178_);
v_val_1192_ = lean_ctor_get(v_a_1191_, 0);
v___x_1193_ = lean_box(0);
v___x_1194_ = l_Lean_LocalDecl_isAuxDecl(v_val_1192_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_LocalDecl_value_x3f(v_val_1192_, v___x_1194_);
if (lean_obj_tag(v___x_1195_) == 1)
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
v_val_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1196_, v___y_1172_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1198_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_dec_ref_known(v___x_1199_, 1);
v_a_1184_ = v___x_1193_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_del_object(v___x_1180_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
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
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_del_object(v___x_1180_);
v_a_1208_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1197_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1197_);
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
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v___x_1195_);
v___x_1216_ = l_Lean_LocalDecl_type(v_val_1192_);
v___x_1217_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1216_, v___y_1172_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1218_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_dec_ref_known(v___x_1219_, 1);
v_a_1184_ = v___x_1193_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1180_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_del_object(v___x_1180_);
v_a_1228_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1217_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1217_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
else
{
v_a_1184_ = v___x_1193_;
goto v___jp_1183_;
}
}
v___jp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_a_1184_);
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1186_ = v___x_1180_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_a_1184_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_add(v_i_1166_, v___x_1187_);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1164_, v_sz_1165_, v___x_1188_, v___x_1186_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1238_, lean_object* v_sz_1239_, lean_object* v_i_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
size_t v_sz_boxed_1250_; size_t v_i_boxed_1251_; lean_object* v_res_1252_; 
v_sz_boxed_1250_ = lean_unbox_usize(v_sz_1239_);
lean_dec(v_sz_1239_);
v_i_boxed_1251_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_res_1252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1238_, v_sz_boxed_1250_, v_i_boxed_1251_, v_b_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v_as_1238_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1253_, size_t v_sz_1254_, size_t v_i_1255_, lean_object* v_b_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_usize_dec_lt(v_i_1255_, v_sz_1254_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v_b_1256_);
return v___x_1266_;
}
else
{
lean_object* v_snd_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1325_; 
v_snd_1267_ = lean_ctor_get(v_b_1256_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_b_1256_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v_b_1256_, 0);
lean_dec(v_unused_1326_);
v___x_1269_ = v_b_1256_;
v_isShared_1270_ = v_isSharedCheck_1325_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_snd_1267_);
lean_dec(v_b_1256_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1325_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v_a_1273_; lean_object* v_a_1280_; 
v___x_1271_ = lean_box(0);
v_a_1280_ = lean_array_uget_borrowed(v_as_1253_, v_i_1255_);
if (lean_obj_tag(v_a_1280_) == 0)
{
v_a_1273_ = v_snd_1267_;
goto v___jp_1272_;
}
else
{
lean_object* v_val_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
lean_dec(v_snd_1267_);
v_val_1281_ = lean_ctor_get(v_a_1280_, 0);
v___x_1282_ = lean_box(0);
v___x_1283_ = l_Lean_LocalDecl_isAuxDecl(v_val_1281_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_LocalDecl_value_x3f(v_val_1281_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 1)
{
lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1285_, v___y_1261_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1287_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_dec_ref_known(v___x_1288_, 1);
v_a_1273_ = v___x_1282_;
goto v___jp_1272_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_del_object(v___x_1269_);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
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
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_del_object(v___x_1269_);
v_a_1297_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1286_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1286_);
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
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v___x_1284_);
v___x_1305_ = l_Lean_LocalDecl_type(v_val_1281_);
v___x_1306_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1305_, v___y_1261_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1307_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_dec_ref_known(v___x_1308_, 1);
v_a_1273_ = v___x_1282_;
goto v___jp_1272_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_del_object(v___x_1269_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1269_);
v_a_1317_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1306_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1306_);
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
}
else
{
v_a_1273_ = v___x_1282_;
goto v___jp_1272_;
}
}
v___jp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_a_1273_);
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1275_ = v___x_1269_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_a_1273_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
size_t v___x_1276_; size_t v___x_1277_; 
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1255_, v___x_1276_);
v_i_1255_ = v___x_1277_;
v_b_1256_ = v___x_1275_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1327_, lean_object* v_sz_1328_, lean_object* v_i_1329_, lean_object* v_b_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1328_);
lean_dec(v_sz_1328_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1329_);
lean_dec(v_i_1329_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1327_, v_sz_boxed_1339_, v_i_boxed_1340_, v_b_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v_as_1327_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1342_, size_t v_sz_1343_, size_t v_i_1344_, lean_object* v_b_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_lt(v_i_1344_, v_sz_1343_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_b_1345_);
return v___x_1355_;
}
else
{
lean_object* v_snd_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1414_; 
v_snd_1356_ = lean_ctor_get(v_b_1345_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_b_1345_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_b_1345_, 0);
lean_dec(v_unused_1415_);
v___x_1358_ = v_b_1345_;
v_isShared_1359_ = v_isSharedCheck_1414_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1356_);
lean_dec(v_b_1345_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1414_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v_a_1362_; lean_object* v_a_1369_; 
v___x_1360_ = lean_box(0);
v_a_1369_ = lean_array_uget_borrowed(v_as_1342_, v_i_1344_);
if (lean_obj_tag(v_a_1369_) == 0)
{
v_a_1362_ = v_snd_1356_;
goto v___jp_1361_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
lean_dec(v_snd_1356_);
v_val_1370_ = lean_ctor_get(v_a_1369_, 0);
v___x_1371_ = lean_box(0);
v___x_1372_ = l_Lean_LocalDecl_isAuxDecl(v_val_1370_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_LocalDecl_value_x3f(v_val_1370_, v___x_1372_);
if (lean_obj_tag(v___x_1373_) == 1)
{
lean_object* v_val_1374_; lean_object* v___x_1375_; 
v_val_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1374_, v___y_1350_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1376_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_dec_ref_known(v___x_1377_, 1);
v_a_1362_ = v___x_1371_;
goto v___jp_1361_;
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_del_object(v___x_1358_);
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
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
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_del_object(v___x_1358_);
v_a_1386_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1375_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1375_);
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
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec(v___x_1373_);
v___x_1394_ = l_Lean_LocalDecl_type(v_val_1370_);
v___x_1395_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1394_, v___y_1350_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1396_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_dec_ref_known(v___x_1397_, 1);
v_a_1362_ = v___x_1371_;
goto v___jp_1361_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_del_object(v___x_1358_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_del_object(v___x_1358_);
v_a_1406_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1395_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1395_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
v_a_1362_ = v___x_1371_;
goto v___jp_1361_;
}
}
v___jp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_a_1362_);
lean_ctor_set(v___x_1358_, 0, v___x_1360_);
v___x_1364_ = v___x_1358_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_a_1362_);
v___x_1364_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_add(v_i_1344_, v___x_1365_);
v___x_1367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1342_, v_sz_1343_, v___x_1366_, v___x_1364_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1416_, lean_object* v_sz_1417_, lean_object* v_i_1418_, lean_object* v_b_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
size_t v_sz_boxed_1428_; size_t v_i_boxed_1429_; lean_object* v_res_1430_; 
v_sz_boxed_1428_ = lean_unbox_usize(v_sz_1417_);
lean_dec(v_sz_1417_);
v_i_boxed_1429_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1416_, v_sz_boxed_1428_, v_i_boxed_1429_, v_b_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v_as_1416_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_init_1431_, lean_object* v_n_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
if (lean_obj_tag(v_n_1432_) == 0)
{
lean_object* v_cs_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; size_t v_sz_1445_; size_t v___x_1446_; lean_object* v___x_1447_; 
v_cs_1442_ = lean_ctor_get(v_n_1432_, 0);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v_b_1433_);
v_sz_1445_ = lean_array_size(v_cs_1442_);
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1431_, v_cs_1442_, v_sz_1445_, v___x_1446_, v___x_1444_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1462_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_fst_1452_; 
v_fst_1452_ = lean_ctor_get(v_a_1448_, 0);
if (lean_obj_tag(v_fst_1452_) == 0)
{
lean_object* v_snd_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v_snd_1453_ = lean_ctor_get(v_a_1448_, 1);
lean_inc(v_snd_1453_);
lean_dec(v_a_1448_);
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_snd_1453_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1454_);
v___x_1456_ = v___x_1450_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_object* v_val_1458_; lean_object* v___x_1460_; 
lean_inc_ref(v_fst_1452_);
lean_dec(v_a_1448_);
v_val_1458_ = lean_ctor_get(v_fst_1452_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v_fst_1452_, 1);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v_val_1458_);
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_val_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_a_1463_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1447_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1447_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
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
lean_object* v_vs_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; size_t v_sz_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v_vs_1471_ = lean_ctor_get(v_n_1432_, 0);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v_b_1433_);
v_sz_1474_ = lean_array_size(v_vs_1471_);
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1471_, v_sz_1474_, v___x_1475_, v___x_1473_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1491_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v_fst_1481_; 
v_fst_1481_ = lean_ctor_get(v_a_1477_, 0);
if (lean_obj_tag(v_fst_1481_) == 0)
{
lean_object* v_snd_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v_snd_1482_ = lean_ctor_get(v_a_1477_, 1);
lean_inc(v_snd_1482_);
lean_dec(v_a_1477_);
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_snd_1482_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1483_);
v___x_1485_ = v___x_1479_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
else
{
lean_object* v_val_1487_; lean_object* v___x_1489_; 
lean_inc_ref(v_fst_1481_);
lean_dec(v_a_1477_);
v_val_1487_ = lean_ctor_get(v_fst_1481_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v_fst_1481_, 1);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v_val_1487_);
v___x_1489_ = v___x_1479_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_val_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1476_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1476_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_init_1500_, lean_object* v_as_1501_, size_t v_sz_1502_, size_t v_i_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_usize_dec_lt(v_i_1503_, v_sz_1502_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_b_1504_);
return v___x_1514_;
}
else
{
lean_object* v_snd_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1549_; 
v_snd_1515_ = lean_ctor_get(v_b_1504_, 1);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_b_1504_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_b_1504_, 0);
lean_dec(v_unused_1550_);
v___x_1517_ = v_b_1504_;
v_isShared_1518_ = v_isSharedCheck_1549_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_snd_1515_);
lean_dec(v_b_1504_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1549_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_a_1519_; lean_object* v___x_1520_; 
v_a_1519_ = lean_array_uget_borrowed(v_as_1501_, v_i_1503_);
lean_inc(v_snd_1515_);
v___x_1520_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1500_, v_a_1519_, v_snd_1515_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1540_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1540_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1540_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
if (lean_obj_tag(v_a_1521_) == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1521_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1525_);
v___x_1527_ = v___x_1517_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_snd_1515_);
v___x_1527_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1527_);
v___x_1529_ = v___x_1523_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
lean_del_object(v___x_1523_);
lean_dec(v_snd_1515_);
v_a_1532_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v_a_1521_, 1);
v___x_1533_ = lean_box(0);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 1, v_a_1532_);
lean_ctor_set(v___x_1517_, 0, v___x_1533_);
v___x_1535_ = v___x_1517_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_a_1532_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
size_t v___x_1536_; size_t v___x_1537_; 
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_add(v_i_1503_, v___x_1536_);
v_i_1503_ = v___x_1537_;
v_b_1504_ = v___x_1535_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_del_object(v___x_1517_);
lean_dec(v_snd_1515_);
v_a_1541_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1520_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1520_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1551_, lean_object* v_as_1552_, lean_object* v_sz_1553_, lean_object* v_i_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
size_t v_sz_boxed_1564_; size_t v_i_boxed_1565_; lean_object* v_res_1566_; 
v_sz_boxed_1564_ = lean_unbox_usize(v_sz_1553_);
lean_dec(v_sz_1553_);
v_i_boxed_1565_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_res_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1551_, v_as_1552_, v_sz_boxed_1564_, v_i_boxed_1565_, v_b_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v_as_1552_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_init_1567_, lean_object* v_n_1568_, lean_object* v_b_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1567_, v_n_1568_, v_b_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v_n_1568_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1579_, lean_object* v_init_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_root_1589_; lean_object* v_tail_1590_; lean_object* v___x_1591_; 
v_root_1589_ = lean_ctor_get(v_t_1579_, 0);
v_tail_1590_ = lean_ctor_get(v_t_1579_, 1);
v___x_1591_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1580_, v_root_1589_, v_init_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1628_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1628_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1628_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
if (lean_obj_tag(v_a_1592_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; 
v_a_1596_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v_a_1592_, 1);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v_a_1596_);
v___x_1598_ = v___x_1594_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
lean_del_object(v___x_1594_);
v_a_1600_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v_a_1592_, 1);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v_a_1600_);
v_sz_1603_ = lean_array_size(v_tail_1590_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1590_, v_sz_1603_, v___x_1604_, v___x_1602_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1619_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1619_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1619_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_fst_1610_; 
v_fst_1610_ = lean_ctor_get(v_a_1606_, 0);
if (lean_obj_tag(v_fst_1610_) == 0)
{
lean_object* v_snd_1611_; lean_object* v___x_1613_; 
v_snd_1611_ = lean_ctor_get(v_a_1606_, 1);
lean_inc(v_snd_1611_);
lean_dec(v_a_1606_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_snd_1611_);
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_snd_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
else
{
lean_object* v_val_1615_; lean_object* v___x_1617_; 
lean_inc_ref(v_fst_1610_);
lean_dec(v_a_1606_);
v_val_1615_ = lean_ctor_get(v_fst_1610_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v_fst_1610_, 1);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_val_1615_);
v___x_1617_ = v___x_1608_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_val_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1605_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1605_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1591_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1591_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1637_, lean_object* v_init_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1637_, v_init_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v_t_1637_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_lctx_1657_; lean_object* v_decls_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_lctx_1657_ = lean_ctor_get(v_a_1652_, 2);
v_decls_1658_ = lean_ctor_get(v_lctx_1657_, 1);
v___x_1659_ = lean_box(0);
v___x_1660_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1658_, v___x_1659_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref_known(v___x_1660_, 1);
v___x_1661_ = l_Lean_MVarId_getType(v_mvarId_1648_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1662_, v_a_1653_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1664_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
return v___x_1665_;
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1663_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1663_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1661_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1661_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_dec(v_mvarId_1648_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1692_, lean_object* v_x_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1692_, v_x_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1708_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1699_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1699_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1716_, v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1724_, lean_object* v_mvarId_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1725_, v_x_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_mvarId_1734_, lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1733_, v_mvarId_1734_, v_x_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1742_, lean_object* v___x_1743_, lean_object* v_mvarId_1744_, lean_object* v_needle_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_st_mk_ref(v___x_1742_);
v___x_1752_ = lean_st_mk_ref(v___x_1743_);
v___x_1753_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1744_, v___x_1752_, v_needle_1745_, v___x_1751_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1763_; 
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v___x_1753_, 0);
lean_dec(v_unused_1764_);
v___x_1755_ = v___x_1753_;
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
else
{
lean_dec(v___x_1753_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v_calls_1759_; lean_object* v___x_1761_; 
v___x_1757_ = lean_st_ref_get(v___x_1752_);
lean_dec(v___x_1752_);
lean_dec(v___x_1757_);
v___x_1758_ = lean_st_ref_get(v___x_1751_);
lean_dec(v___x_1751_);
v_calls_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc_ref(v_calls_1759_);
lean_dec(v___x_1758_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_calls_1759_);
v___x_1761_ = v___x_1755_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_calls_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v___x_1752_);
lean_dec(v___x_1751_);
v_a_1765_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1753_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1753_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1773_, lean_object* v___x_1774_, lean_object* v_mvarId_1775_, lean_object* v_needle_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1773_, v___x_1774_, v_mvarId_1775_, v_needle_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_needle_1776_);
return v_res_1782_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(64u);
v___x_1784_ = l_Lean_mkPtrSet___redArg(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1785_, lean_object* v_mvarId_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; 
v___x_1792_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_1793_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
lean_inc(v_mvarId_1786_);
v___f_1794_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1794_, 0, v___x_1793_);
lean_closure_set(v___f_1794_, 1, v___x_1792_);
lean_closure_set(v___f_1794_, 2, v_mvarId_1786_);
lean_closure_set(v___f_1794_, 3, v_needle_1785_);
v___x_1795_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1786_, v___f_1794_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_1796_, lean_object* v_mvarId_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1796_, v_mvarId_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_1804_, lean_object* v_mvarId_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1804_, v_mvarId_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_1812_, lean_object* v_mvarId_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1812_, v_mvarId_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_1820_, lean_object* v_mvarId_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1820_, v_mvarId_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_1828_, lean_object* v_mvarId_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Meta_FunInd_collect(v_needle_1828_, v_mvarId_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1835_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_FunIndCollect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
