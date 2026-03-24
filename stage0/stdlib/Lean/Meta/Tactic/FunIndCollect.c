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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object* v_calls_281_, lean_object* v_as_282_, size_t v_sz_283_, size_t v_i_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_a_288_; uint8_t v___x_292_; 
v___x_292_ = lean_usize_dec_lt(v_i_284_, v_sz_283_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec_ref(v_calls_281_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v_b_285_);
return v___x_293_;
}
else
{
lean_object* v_snd_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_351_; 
v_snd_294_ = lean_ctor_get(v_b_285_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_b_285_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v_b_285_, 0);
lean_dec(v_unused_352_);
v___x_296_ = v_b_285_;
v_isShared_297_ = v_isSharedCheck_351_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_snd_294_);
lean_dec(v_b_285_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_351_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_snd_298_; lean_object* v_fst_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_350_; 
v_snd_298_ = lean_ctor_get(v_snd_294_, 1);
v_fst_299_ = lean_ctor_get(v_snd_294_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_snd_294_);
if (v_isSharedCheck_350_ == 0)
{
v___x_301_ = v_snd_294_;
v_isShared_302_ = v_isSharedCheck_350_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_snd_298_);
lean_inc(v_fst_299_);
lean_dec(v_snd_294_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_350_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_array_303_; lean_object* v_start_304_; lean_object* v_stop_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_array_303_ = lean_ctor_get(v_snd_298_, 0);
v_start_304_ = lean_ctor_get(v_snd_298_, 1);
v_stop_305_ = lean_ctor_get(v_snd_298_, 2);
v___x_306_ = lean_box(0);
v___x_307_ = lean_nat_dec_lt(v_start_304_, v_stop_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; 
lean_dec_ref(v_calls_281_);
if (v_isShared_302_ == 0)
{
v___x_309_ = v___x_301_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_fst_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_snd_298_);
v___x_309_ = v_reuseFailAlloc_314_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_309_);
lean_ctor_set(v___x_296_, 0, v___x_306_);
v___x_311_ = v___x_296_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_313_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
}
else
{
lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_346_; 
lean_inc(v_stop_305_);
lean_inc(v_start_304_);
lean_inc_ref(v_array_303_);
v_isSharedCheck_346_ = !lean_is_exclusive(v_snd_298_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_347_ = lean_ctor_get(v_snd_298_, 2);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_snd_298_, 1);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_snd_298_, 0);
lean_dec(v_unused_349_);
v___x_316_ = v_snd_298_;
v_isShared_317_ = v_isSharedCheck_346_;
goto v_resetjp_315_;
}
else
{
lean_dec(v_snd_298_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_346_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v_a_318_ = lean_array_uget_borrowed(v_as_282_, v_i_284_);
v___x_319_ = lean_array_fget(v_array_303_, v_start_304_);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_start_304_, v___x_320_);
lean_dec(v_start_304_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___x_321_);
v___x_323_ = v___x_316_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_array_303_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_stop_305_);
v___x_323_ = v_reuseFailAlloc_345_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
uint8_t v___x_339_; 
v___x_339_ = lean_unbox(v___x_319_);
if (v___x_339_ == 2)
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_Expr_isFVar(v_a_318_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v___x_319_);
lean_del_object(v___x_301_);
lean_del_object(v___x_296_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v_calls_281_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_fst_299_);
lean_ctor_set(v___x_342_, 1, v___x_323_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
else
{
goto v___jp_324_;
}
}
else
{
goto v___jp_324_;
}
v___jp_324_:
{
uint8_t v___x_325_; 
v___x_325_ = lean_unbox(v___x_319_);
lean_dec(v___x_319_);
if (v___x_325_ == 0)
{
lean_object* v___x_327_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_323_);
v___x_327_ = v___x_301_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_fst_299_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_323_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_327_);
lean_ctor_set(v___x_296_, 0, v___x_306_);
v___x_329_ = v___x_296_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v_a_288_ = v___x_329_;
goto v___jp_287_;
}
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_334_; 
lean_inc(v_a_318_);
v___x_332_ = lean_array_push(v_fst_299_, v_a_318_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_323_);
lean_ctor_set(v___x_301_, 0, v___x_332_);
v___x_334_ = v___x_301_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_323_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_334_);
lean_ctor_set(v___x_296_, 0, v___x_306_);
v___x_336_ = v___x_296_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v_a_288_ = v___x_336_;
goto v___jp_287_;
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
v___jp_287_:
{
size_t v___x_289_; size_t v___x_290_; 
v___x_289_ = ((size_t)1ULL);
v___x_290_ = lean_usize_add(v_i_284_, v___x_289_);
v_i_284_ = v___x_290_;
v_b_285_ = v_a_288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object* v_calls_353_, lean_object* v_as_354_, lean_object* v_sz_355_, lean_object* v_i_356_, lean_object* v_b_357_, lean_object* v___y_358_){
_start:
{
size_t v_sz_boxed_359_; size_t v_i_boxed_360_; lean_object* v_res_361_; 
v_sz_boxed_359_ = lean_unbox_usize(v_sz_355_);
lean_dec(v_sz_355_);
v_i_boxed_360_ = lean_unbox_usize(v_i_356_);
lean_dec(v_i_356_);
v_res_361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_353_, v_as_354_, v_sz_boxed_359_, v_i_boxed_360_, v_b_357_);
lean_dec_ref(v_as_354_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object* v_e_362_, lean_object* v_funIndInfo_363_, lean_object* v_args_364_, lean_object* v_calls_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_funName_371_; lean_object* v_params_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_funName_371_ = lean_ctor_get(v_funIndInfo_363_, 0);
lean_inc(v_funName_371_);
v_params_372_ = lean_ctor_get(v_funIndInfo_363_, 3);
lean_inc_ref(v_params_372_);
lean_dec_ref(v_funIndInfo_363_);
v___x_373_ = lean_array_get_size(v_params_372_);
v___x_374_ = lean_array_get_size(v_args_364_);
v___x_375_ = lean_nat_dec_eq(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec_ref(v_params_372_);
lean_dec(v_funName_371_);
lean_dec_ref(v_e_362_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_calls_365_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; lean_object* v_keys_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; size_t v_sz_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_377_ = lean_unsigned_to_nat(0u);
v_keys_378_ = ((lean_object*)(l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__0));
v___x_379_ = l_Array_toSubarray___redArg(v_params_372_, v___x_377_, v___x_373_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_keys_378_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v_sz_383_ = lean_array_size(v_args_364_);
v___x_384_ = ((size_t)0ULL);
lean_inc_ref(v_calls_365_);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_365_, v_args_364_, v_sz_383_, v___x_384_, v___x_382_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_426_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_426_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_426_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_426_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_fst_390_; 
v_fst_390_ = lean_ctor_get(v_a_386_, 0);
if (lean_obj_tag(v_fst_390_) == 0)
{
lean_object* v_snd_391_; lean_object* v_fst_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_420_; 
v_snd_391_ = lean_ctor_get(v_a_386_, 1);
lean_inc(v_snd_391_);
lean_dec(v_a_386_);
v_fst_392_ = lean_ctor_get(v_snd_391_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_snd_391_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_snd_391_, 1);
lean_dec(v_unused_421_);
v___x_394_ = v_snd_391_;
v_isShared_395_ = v_isSharedCheck_420_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_fst_392_);
lean_dec(v_snd_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_420_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_calls_396_; lean_object* v_seen_397_; lean_object* v___x_399_; 
v_calls_396_ = lean_ctor_get(v_calls_365_, 0);
v_seen_397_ = lean_ctor_get(v_calls_365_, 1);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v_fst_392_);
lean_ctor_set(v___x_394_, 0, v_funName_371_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_funName_371_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_fst_392_);
v___x_399_ = v_reuseFailAlloc_419_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
uint8_t v___x_400_; 
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_397_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_413_; 
lean_inc_ref(v_seen_397_);
lean_inc_ref(v_calls_396_);
v_isSharedCheck_413_ = !lean_is_exclusive(v_calls_365_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_414_ = lean_ctor_get(v_calls_365_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_calls_365_, 0);
lean_dec(v_unused_415_);
v___x_402_ = v_calls_365_;
v_isShared_403_ = v_isSharedCheck_413_;
goto v_resetjp_401_;
}
else
{
lean_dec(v_calls_365_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_413_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_404_ = lean_array_push(v_calls_396_, v_e_362_);
v___x_405_ = lean_box(0);
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_397_, v___x_399_, v___x_405_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___x_406_);
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_412_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_408_);
v___x_410_ = v___x_388_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
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
lean_object* v___x_417_; 
lean_dec_ref(v___x_399_);
lean_dec_ref(v_e_362_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_calls_365_);
v___x_417_ = v___x_388_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_calls_365_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
else
{
lean_object* v_val_422_; lean_object* v___x_424_; 
lean_inc_ref(v_fst_390_);
lean_dec(v_a_386_);
lean_dec(v_funName_371_);
lean_dec_ref(v_calls_365_);
lean_dec_ref(v_e_362_);
v_val_422_ = lean_ctor_get(v_fst_390_, 0);
lean_inc(v_val_422_);
lean_dec_ref(v_fst_390_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_val_422_);
v___x_424_ = v___x_388_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_val_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_funName_371_);
lean_dec_ref(v_calls_365_);
lean_dec_ref(v_e_362_);
v_a_427_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_385_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_385_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object* v_e_435_, lean_object* v_funIndInfo_436_, lean_object* v_args_437_, lean_object* v_calls_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_435_, v_funIndInfo_436_, v_args_437_, v_calls_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec_ref(v_args_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object* v_calls_445_, lean_object* v_as_446_, size_t v_sz_447_, size_t v_i_448_, lean_object* v_b_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_445_, v_as_446_, v_sz_447_, v_i_448_, v_b_449_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object* v_calls_456_, lean_object* v_as_457_, lean_object* v_sz_458_, lean_object* v_i_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
size_t v_sz_boxed_466_; size_t v_i_boxed_467_; lean_object* v_res_468_; 
v_sz_boxed_466_ = lean_unbox_usize(v_sz_458_);
lean_dec(v_sz_458_);
v_i_boxed_467_ = lean_unbox_usize(v_i_459_);
lean_dec(v_i_459_);
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_456_, v_as_457_, v_sz_boxed_466_, v_i_boxed_467_, v_b_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec_ref(v_as_457_);
return v_res_468_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object* v_00_u03b2_469_, lean_object* v_m_470_, lean_object* v_a_471_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_470_, v_a_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object* v_00_u03b2_473_, lean_object* v_m_474_, lean_object* v_a_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(v_00_u03b2_473_, v_m_474_, v_a_475_);
lean_dec_ref(v_a_475_);
lean_dec_ref(v_m_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object* v_00_u03b2_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_479_, v_a_480_, v_b_481_);
return v___x_482_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object* v_00_u03b2_483_, lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_a_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object* v_00_u03b2_487_, lean_object* v_a_488_, lean_object* v_x_489_){
_start:
{
uint8_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_487_, v_a_488_, v_x_489_);
lean_dec(v_x_489_);
lean_dec_ref(v_a_488_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object* v_00_u03b2_492_, lean_object* v_data_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___redArg(v_data_493_);
return v___x_494_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2(lean_object* v_xs_495_, lean_object* v_ys_496_, lean_object* v_hsz_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1_spec__2___redArg(v_xs_495_, v_ys_496_, v_x_498_);
return v___x_500_;
}
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
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object* v_snd_517_, lean_object* v_x_518_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object* v_snd_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_522_, v_x_523_);
lean_dec(v_x_523_);
lean_dec(v_snd_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
if (lean_obj_tag(v_a_526_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v_a_527_);
return v___x_528_;
}
else
{
lean_object* v_key_529_; lean_object* v_tail_530_; lean_object* v_fst_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_553_; 
v_key_529_ = lean_ctor_get(v_a_526_, 0);
lean_inc(v_key_529_);
v_tail_530_ = lean_ctor_get(v_a_526_, 2);
lean_inc(v_tail_530_);
lean_dec_ref(v_a_526_);
v_fst_531_ = lean_ctor_get(v_key_529_, 0);
lean_inc(v_fst_531_);
lean_dec(v_key_529_);
v_fst_532_ = lean_ctor_get(v_a_527_, 0);
v_snd_533_ = lean_ctor_get(v_a_527_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_527_);
if (v_isSharedCheck_553_ == 0)
{
v___x_535_ = v_a_527_;
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_snd_533_);
lean_inc(v_fst_532_);
lean_dec(v_a_527_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint8_t v___x_537_; 
v___x_537_ = l_Lean_NameSet_contains(v_snd_533_, v_fst_531_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_NameSet_contains(v_fst_532_, v_fst_531_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_NameSet_insert(v_fst_532_, v_fst_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_539_);
v___x_541_ = v___x_535_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_snd_533_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
v_a_526_ = v_tail_530_;
v_a_527_ = v___x_541_;
goto _start;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = l_Lean_NameSet_insert(v_snd_533_, v_fst_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_544_);
v___x_546_ = v___x_535_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_fst_532_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v_a_526_ = v_tail_530_;
v_a_527_ = v___x_546_;
goto _start;
}
}
}
else
{
lean_object* v___x_550_; 
lean_dec(v_fst_531_);
if (v_isShared_536_ == 0)
{
v___x_550_ = v___x_535_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_fst_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_snd_533_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v_a_526_ = v_tail_530_;
v_a_527_ = v___x_550_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(lean_object* v_as_554_, size_t v_sz_555_, size_t v_i_556_, lean_object* v_b_557_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_lt(v_i_556_, v_sz_555_);
if (v___x_558_ == 0)
{
return v_b_557_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_array_uget_borrowed(v_as_554_, v_i_556_);
lean_inc(v_a_559_);
v___x_560_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_a_559_, v_b_557_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref(v___x_560_);
return v_a_561_;
}
else
{
lean_object* v_a_562_; size_t v___x_563_; size_t v___x_564_; 
v_a_562_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_562_);
lean_dec_ref(v___x_560_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_556_, v___x_563_);
v_i_556_ = v___x_564_;
v_b_557_ = v_a_562_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1___boxed(lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_){
_start:
{
size_t v_sz_boxed_570_; size_t v_i_boxed_571_; lean_object* v_res_572_; 
v_sz_boxed_570_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_571_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_as_566_, v_sz_boxed_570_, v_i_boxed_571_, v_b_569_);
lean_dec_ref(v_as_566_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0(void){
_start:
{
lean_object* v_seen_573_; lean_object* v___x_574_; 
v_seen_573_ = l_Lean_NameSet_empty;
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_seen_573_);
lean_ctor_set(v___x_574_, 1, v_seen_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object* v_calls_575_){
_start:
{
lean_object* v_seen_576_; lean_object* v___x_577_; lean_object* v_buckets_578_; size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v_seen_576_ = lean_ctor_get(v_calls_575_, 1);
v___x_577_ = lean_obj_once(&l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0, &l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once, _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0);
v_buckets_578_ = lean_ctor_get(v_seen_576_, 1);
v_sz_579_ = lean_array_size(v_buckets_578_);
v___x_580_ = ((size_t)0ULL);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__1(v_buckets_578_, v_sz_579_, v___x_580_, v___x_577_);
v_fst_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_fst_582_);
v_snd_583_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_snd_583_);
lean_dec_ref(v___x_581_);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed), 2, 1);
lean_closure_set(v___f_584_, 0, v_snd_583_);
v___x_585_ = l_Lean_NameSet_filter(v___f_584_, v_fst_582_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object* v_calls_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_586_);
lean_dec_ref(v_calls_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object* v_e_588_, lean_object* v_funIndInfo_589_, lean_object* v_args_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_st_ref_get(v_a_591_);
v___x_598_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_588_, v_funIndInfo_589_, v_args_590_, v___x_597_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_st_ref_set(v_a_591_, v_a_599_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_598_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_598_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object* v_e_616_, lean_object* v_funIndInfo_617_, lean_object* v_args_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_616_, v_funIndInfo_617_, v_args_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_args_618_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object* v_e_626_, lean_object* v_funIndInfo_627_, lean_object* v_args_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_626_, v_funIndInfo_627_, v_args_628_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object* v_e_637_, lean_object* v_funIndInfo_638_, lean_object* v_args_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_637_, v_funIndInfo_638_, v_args_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec_ref(v_args_639_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object* v_e_648_, lean_object* v_funIndInfo_649_, lean_object* v_args_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_648_, v_funIndInfo_649_, v_args_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object* v_e_658_, lean_object* v_funIndInfo_659_, lean_object* v_args_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_658_, v_funIndInfo_659_, v_args_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_args_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object* v_e_668_, lean_object* v_funIndInfo_669_, lean_object* v_args_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_668_, v_funIndInfo_669_, v_args_670_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object* v_e_679_, lean_object* v_funIndInfo_680_, lean_object* v_args_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_679_, v_funIndInfo_680_, v_args_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec_ref(v_args_681_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
return v_x_690_;
}
else
{
lean_object* v_key_692_; lean_object* v_value_693_; lean_object* v_tail_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_720_; 
v_key_692_ = lean_ctor_get(v_x_691_, 0);
v_value_693_ = lean_ctor_get(v_x_691_, 1);
v_tail_694_ = lean_ctor_get(v_x_691_, 2);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_720_ == 0)
{
v___x_696_ = v_x_691_;
v_isShared_697_ = v_isSharedCheck_720_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_tail_694_);
lean_inc(v_value_693_);
lean_inc(v_key_692_);
lean_dec(v_x_691_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_720_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; size_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v_fold_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_698_ = lean_array_get_size(v_x_690_);
v___x_699_ = lean_ptr_addr(v_key_692_);
v___x_700_ = lean_usize_to_uint64(v___x_699_);
v___x_701_ = 11ULL;
v___x_702_ = lean_uint64_mix_hash(v___x_700_, v___x_701_);
v___x_703_ = 32ULL;
v___x_704_ = lean_uint64_shift_right(v___x_702_, v___x_703_);
v_fold_705_ = lean_uint64_xor(v___x_702_, v___x_704_);
v___x_706_ = 16ULL;
v___x_707_ = lean_uint64_shift_right(v_fold_705_, v___x_706_);
v___x_708_ = lean_uint64_xor(v_fold_705_, v___x_707_);
v___x_709_ = lean_uint64_to_usize(v___x_708_);
v___x_710_ = lean_usize_of_nat(v___x_698_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_sub(v___x_710_, v___x_711_);
v___x_713_ = lean_usize_land(v___x_709_, v___x_712_);
v___x_714_ = lean_array_uget_borrowed(v_x_690_, v___x_713_);
lean_inc(v___x_714_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 2, v___x_714_);
v___x_716_ = v___x_696_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_key_692_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_value_693_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v___x_714_);
v___x_716_ = v_reuseFailAlloc_719_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; 
v___x_717_ = lean_array_uset(v_x_690_, v___x_713_, v___x_716_);
v_x_690_ = v___x_717_;
v_x_691_ = v_tail_694_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(lean_object* v_i_721_, lean_object* v_source_722_, lean_object* v_target_723_){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_array_get_size(v_source_722_);
v___x_725_ = lean_nat_dec_lt(v_i_721_, v___x_724_);
if (v___x_725_ == 0)
{
lean_dec_ref(v_source_722_);
lean_dec(v_i_721_);
return v_target_723_;
}
else
{
lean_object* v_es_726_; lean_object* v___x_727_; lean_object* v_source_728_; lean_object* v_target_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_es_726_ = lean_array_fget(v_source_722_, v_i_721_);
v___x_727_ = lean_box(0);
v_source_728_ = lean_array_fset(v_source_722_, v_i_721_, v___x_727_);
v_target_729_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_723_, v_es_726_);
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_i_721_, v___x_730_);
lean_dec(v_i_721_);
v_i_721_ = v___x_731_;
v_source_722_ = v_source_728_;
v_target_723_ = v_target_729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(lean_object* v_data_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_nbuckets_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_734_ = lean_array_get_size(v_data_733_);
v___x_735_ = lean_unsigned_to_nat(2u);
v_nbuckets_736_ = lean_nat_mul(v___x_734_, v___x_735_);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_box(0);
v___x_739_ = lean_mk_array(v_nbuckets_736_, v___x_738_);
v___x_740_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_737_, v_data_733_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_a_741_, lean_object* v_x_742_){
_start:
{
if (lean_obj_tag(v_x_742_) == 0)
{
uint8_t v___x_743_; 
v___x_743_ = 0;
return v___x_743_;
}
else
{
lean_object* v_key_744_; lean_object* v_tail_745_; size_t v___x_746_; size_t v___x_747_; uint8_t v___x_748_; 
v_key_744_ = lean_ctor_get(v_x_742_, 0);
v_tail_745_ = lean_ctor_get(v_x_742_, 2);
v___x_746_ = lean_ptr_addr(v_key_744_);
v___x_747_ = lean_ptr_addr(v_a_741_);
v___x_748_ = lean_usize_dec_eq(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
v_x_742_ = v_tail_745_;
goto _start;
}
else
{
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_750_, v_x_751_);
lean_dec(v_x_751_);
lean_dec_ref(v_a_750_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(lean_object* v_m_754_, lean_object* v_a_755_, lean_object* v_b_756_){
_start:
{
lean_object* v_size_757_; lean_object* v_buckets_758_; lean_object* v___x_759_; size_t v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; uint64_t v___x_763_; uint64_t v___x_764_; uint64_t v___x_765_; uint64_t v_fold_766_; uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; lean_object* v_bkt_775_; uint8_t v___x_776_; 
v_size_757_ = lean_ctor_get(v_m_754_, 0);
v_buckets_758_ = lean_ctor_get(v_m_754_, 1);
v___x_759_ = lean_array_get_size(v_buckets_758_);
v___x_760_ = lean_ptr_addr(v_a_755_);
v___x_761_ = lean_usize_to_uint64(v___x_760_);
v___x_762_ = 11ULL;
v___x_763_ = lean_uint64_mix_hash(v___x_761_, v___x_762_);
v___x_764_ = 32ULL;
v___x_765_ = lean_uint64_shift_right(v___x_763_, v___x_764_);
v_fold_766_ = lean_uint64_xor(v___x_763_, v___x_765_);
v___x_767_ = 16ULL;
v___x_768_ = lean_uint64_shift_right(v_fold_766_, v___x_767_);
v___x_769_ = lean_uint64_xor(v_fold_766_, v___x_768_);
v___x_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = lean_usize_of_nat(v___x_759_);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_sub(v___x_771_, v___x_772_);
v___x_774_ = lean_usize_land(v___x_770_, v___x_773_);
v_bkt_775_ = lean_array_uget_borrowed(v_buckets_758_, v___x_774_);
v___x_776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_755_, v_bkt_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_797_; 
lean_inc_ref(v_buckets_758_);
lean_inc(v_size_757_);
v_isSharedCheck_797_ = !lean_is_exclusive(v_m_754_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_798_ = lean_ctor_get(v_m_754_, 1);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_m_754_, 0);
lean_dec(v_unused_799_);
v___x_778_ = v_m_754_;
v_isShared_779_ = v_isSharedCheck_797_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_m_754_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_797_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v_size_x27_781_; lean_object* v___x_782_; lean_object* v_buckets_x27_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v_size_x27_781_ = lean_nat_add(v_size_757_, v___x_780_);
lean_dec(v_size_757_);
lean_inc(v_bkt_775_);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v_a_755_);
lean_ctor_set(v___x_782_, 1, v_b_756_);
lean_ctor_set(v___x_782_, 2, v_bkt_775_);
v_buckets_x27_783_ = lean_array_uset(v_buckets_758_, v___x_774_, v___x_782_);
v___x_784_ = lean_unsigned_to_nat(4u);
v___x_785_ = lean_nat_mul(v_size_x27_781_, v___x_784_);
v___x_786_ = lean_unsigned_to_nat(3u);
v___x_787_ = lean_nat_div(v___x_785_, v___x_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_array_get_size(v_buckets_x27_783_);
v___x_789_ = lean_nat_dec_le(v___x_787_, v___x_788_);
lean_dec(v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v_val_790_; lean_object* v___x_792_; 
v_val_790_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_783_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_val_790_);
lean_ctor_set(v___x_778_, 0, v_size_x27_781_);
v___x_792_ = v___x_778_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_size_x27_781_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_val_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v___x_795_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_buckets_x27_783_);
lean_ctor_set(v___x_778_, 0, v_size_x27_781_);
v___x_795_ = v___x_778_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_size_x27_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_buckets_x27_783_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_dec(v_b_756_);
lean_dec_ref(v_a_755_);
return v_m_754_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_buckets_802_; lean_object* v___x_803_; size_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v_fold_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_buckets_802_ = lean_ctor_get(v_m_800_, 1);
v___x_803_ = lean_array_get_size(v_buckets_802_);
v___x_804_ = lean_ptr_addr(v_a_801_);
v___x_805_ = lean_usize_to_uint64(v___x_804_);
v___x_806_ = 11ULL;
v___x_807_ = lean_uint64_mix_hash(v___x_805_, v___x_806_);
v___x_808_ = 32ULL;
v___x_809_ = lean_uint64_shift_right(v___x_807_, v___x_808_);
v_fold_810_ = lean_uint64_xor(v___x_807_, v___x_809_);
v___x_811_ = 16ULL;
v___x_812_ = lean_uint64_shift_right(v_fold_810_, v___x_811_);
v___x_813_ = lean_uint64_xor(v_fold_810_, v___x_812_);
v___x_814_ = lean_uint64_to_usize(v___x_813_);
v___x_815_ = lean_usize_of_nat(v___x_803_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_sub(v___x_815_, v___x_816_);
v___x_818_ = lean_usize_land(v___x_814_, v___x_817_);
v___x_819_ = lean_array_uget_borrowed(v_buckets_802_, v___x_818_);
v___x_820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_801_, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_821_, v_a_822_);
lean_dec_ref(v_a_822_);
lean_dec_ref(v_m_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_825_; lean_object* v_dummy_826_; 
v___x_825_ = lean_box(0);
v_dummy_826_ = l_Lean_Expr_sort___override(v___x_825_);
return v_dummy_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_e_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; 
if (lean_obj_tag(v_x_828_) == 5)
{
lean_object* v_fn_860_; lean_object* v_arg_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_fn_860_ = lean_ctor_get(v_x_828_, 0);
lean_inc_ref(v_fn_860_);
v_arg_861_ = lean_ctor_get(v_x_828_, 1);
lean_inc_ref(v_arg_861_);
lean_dec_ref(v_x_828_);
v___x_862_ = lean_array_set(v_x_829_, v_x_830_, v_arg_861_);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_sub(v_x_830_, v___x_863_);
lean_dec(v_x_830_);
v_x_828_ = v_fn_860_;
v_x_829_ = v___x_862_;
v_x_830_ = v___x_864_;
goto _start;
}
else
{
lean_dec(v_x_830_);
if (lean_obj_tag(v_x_828_) == 4)
{
lean_object* v_declName_866_; lean_object* v_funName_867_; uint8_t v___x_868_; 
v_declName_866_ = lean_ctor_get(v_x_828_, 0);
lean_inc(v_declName_866_);
lean_dec_ref(v_x_828_);
v_funName_867_ = lean_ctor_get(v___y_832_, 0);
v___x_868_ = lean_name_eq(v_declName_866_, v_funName_867_);
lean_dec(v_declName_866_);
if (v___x_868_ == 0)
{
lean_dec_ref(v_e_827_);
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
v___y_845_ = v___y_836_;
v___y_846_ = v___y_837_;
goto v___jp_839_;
}
else
{
uint8_t v___x_869_; 
v___x_869_ = l_Lean_Expr_hasLooseBVars(v_e_827_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_inc_ref(v___y_832_);
v___x_870_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_827_, v___y_832_, v_x_829_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_dec_ref(v___x_870_);
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
v___y_845_ = v___y_836_;
v___y_846_ = v___y_837_;
goto v___jp_839_;
}
else
{
lean_dec_ref(v_x_829_);
return v___x_870_;
}
}
else
{
lean_dec_ref(v_e_827_);
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
v___y_845_ = v___y_836_;
v___y_846_ = v___y_837_;
goto v___jp_839_;
}
}
}
else
{
lean_object* v___x_871_; 
lean_dec_ref(v_e_827_);
v___x_871_ = l_Lean_Meta_FunInd_Collector_visit(v_x_828_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_dec_ref(v___x_871_);
v___y_840_ = v___y_831_;
v___y_841_ = v___y_832_;
v___y_842_ = v___y_833_;
v___y_843_ = v___y_834_;
v___y_844_ = v___y_835_;
v___y_845_ = v___y_836_;
v___y_846_ = v___y_837_;
goto v___jp_839_;
}
else
{
lean_dec_ref(v_x_829_);
return v___x_871_;
}
}
}
v___jp_839_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_array_get_size(v_x_829_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_nat_dec_lt(v___x_847_, v___x_848_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v_x_829_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = lean_nat_dec_le(v___x_848_, v___x_848_);
if (v___x_852_ == 0)
{
if (v___x_850_ == 0)
{
lean_object* v___x_853_; 
lean_dec_ref(v_x_829_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_849_);
return v___x_853_;
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((size_t)0ULL);
v___x_855_ = lean_usize_of_nat(v___x_848_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_829_, v___x_854_, v___x_855_, v___x_849_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec_ref(v_x_829_);
return v___x_856_;
}
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_848_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_829_, v___x_857_, v___x_858_, v___x_849_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec_ref(v_x_829_);
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_st_ref_get(v_a_873_);
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_881_, v_e_872_);
lean_dec(v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_d_888_; lean_object* v_b_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; 
v___x_883_ = lean_st_ref_take(v_a_873_);
v___x_884_ = lean_box(0);
lean_inc_ref(v_e_872_);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v___x_883_, v_e_872_, v___x_884_);
v___x_886_ = lean_st_ref_set(v_a_873_, v___x_885_);
switch(lean_obj_tag(v_e_872_))
{
case 4:
{
lean_object* v___x_899_; 
lean_dec_ref(v_e_872_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_884_);
return v___x_899_;
}
case 7:
{
lean_object* v_binderType_900_; lean_object* v_body_901_; 
v_binderType_900_ = lean_ctor_get(v_e_872_, 1);
lean_inc_ref(v_binderType_900_);
v_body_901_ = lean_ctor_get(v_e_872_, 2);
lean_inc_ref(v_body_901_);
lean_dec_ref(v_e_872_);
v_d_888_ = v_binderType_900_;
v_b_889_ = v_body_901_;
v___y_890_ = v_a_873_;
v___y_891_ = v_a_874_;
v___y_892_ = v_a_875_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
goto v___jp_887_;
}
case 6:
{
lean_object* v_binderType_902_; lean_object* v_body_903_; 
v_binderType_902_ = lean_ctor_get(v_e_872_, 1);
lean_inc_ref(v_binderType_902_);
v_body_903_ = lean_ctor_get(v_e_872_, 2);
lean_inc_ref(v_body_903_);
lean_dec_ref(v_e_872_);
v_d_888_ = v_binderType_902_;
v_b_889_ = v_body_903_;
v___y_890_ = v_a_873_;
v___y_891_ = v_a_874_;
v___y_892_ = v_a_875_;
v___y_893_ = v_a_876_;
v___y_894_ = v_a_877_;
v___y_895_ = v_a_878_;
v___y_896_ = v_a_879_;
goto v___jp_887_;
}
case 10:
{
lean_object* v_expr_904_; 
v_expr_904_ = lean_ctor_get(v_e_872_, 1);
lean_inc_ref(v_expr_904_);
lean_dec_ref(v_e_872_);
v_e_872_ = v_expr_904_;
goto _start;
}
case 8:
{
lean_object* v_type_906_; lean_object* v_value_907_; lean_object* v_body_908_; lean_object* v___x_909_; 
v_type_906_ = lean_ctor_get(v_e_872_, 1);
lean_inc_ref(v_type_906_);
v_value_907_ = lean_ctor_get(v_e_872_, 2);
lean_inc_ref(v_value_907_);
v_body_908_ = lean_ctor_get(v_e_872_, 3);
lean_inc_ref(v_body_908_);
lean_dec_ref(v_e_872_);
v___x_909_ = l_Lean_Meta_FunInd_Collector_visit(v_type_906_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v___x_910_; 
lean_dec_ref(v___x_909_);
v___x_910_ = l_Lean_Meta_FunInd_Collector_visit(v_value_907_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_dec_ref(v___x_910_);
v_e_872_ = v_body_908_;
goto _start;
}
else
{
lean_dec_ref(v_body_908_);
return v___x_910_;
}
}
else
{
lean_dec_ref(v_body_908_);
lean_dec_ref(v_value_907_);
return v___x_909_;
}
}
case 5:
{
lean_object* v_dummy_912_; lean_object* v_nargs_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_dummy_912_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_913_ = l_Lean_Expr_getAppNumArgs(v_e_872_);
lean_inc(v_nargs_913_);
v___x_914_ = lean_mk_array(v_nargs_913_, v_dummy_912_);
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_sub(v_nargs_913_, v___x_915_);
lean_dec(v_nargs_913_);
lean_inc_ref(v_e_872_);
v___x_917_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_872_, v_e_872_, v___x_914_, v___x_916_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
return v___x_917_;
}
case 11:
{
lean_object* v_struct_918_; 
v_struct_918_ = lean_ctor_get(v_e_872_, 2);
lean_inc_ref(v_struct_918_);
lean_dec_ref(v_e_872_);
v_e_872_ = v_struct_918_;
goto _start;
}
default: 
{
lean_object* v___x_920_; 
lean_dec_ref(v_e_872_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_884_);
return v___x_920_;
}
}
v___jp_887_:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_FunInd_Collector_visit(v_d_888_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref(v___x_897_);
v_e_872_ = v_b_889_;
v_a_873_ = v___y_890_;
v_a_874_ = v___y_891_;
v_a_875_ = v___y_892_;
v_a_876_ = v___y_893_;
v_a_877_ = v___y_894_;
v_a_878_ = v___y_895_;
v_a_879_ = v___y_896_;
goto _start;
}
else
{
lean_dec_ref(v_b_889_);
return v___x_897_;
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref(v_e_872_);
v___x_921_ = lean_box(0);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_923_, size_t v_i_924_, size_t v_stop_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_eq(v_i_924_, v_stop_925_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_array_uget_borrowed(v_as_923_, v_i_924_);
lean_inc(v___x_936_);
v___x_937_ = l_Lean_Meta_FunInd_Collector_visit(v___x_936_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; size_t v___x_939_; size_t v___x_940_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref(v___x_937_);
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_924_, v___x_939_);
v_i_924_ = v___x_940_;
v_b_926_ = v_a_938_;
goto _start;
}
else
{
return v___x_937_;
}
}
else
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_b_926_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_943_, lean_object* v_i_944_, lean_object* v_stop_945_, lean_object* v_b_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
size_t v_i_boxed_955_; size_t v_stop_boxed_956_; lean_object* v_res_957_; 
v_i_boxed_955_ = lean_unbox_usize(v_i_944_);
lean_dec(v_i_944_);
v_stop_boxed_956_ = lean_unbox_usize(v_stop_945_);
lean_dec(v_stop_945_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_943_, v_i_boxed_955_, v_stop_boxed_956_, v_b_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v_as_943_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Meta_FunInd_Collector_visit(v_e_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_e_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_e_968_, v_x_969_, v_x_970_, v_x_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_981_, lean_object* v_m_982_, lean_object* v_a_983_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_982_, v_a_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_985_, lean_object* v_m_986_, lean_object* v_a_987_){
_start:
{
uint8_t v_res_988_; lean_object* v_r_989_; 
v_res_988_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_985_, v_m_986_, v_a_987_);
lean_dec_ref(v_a_987_);
lean_dec_ref(v_m_986_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_00_u03b2_990_, lean_object* v_m_991_, lean_object* v_a_992_, lean_object* v_b_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2___redArg(v_m_991_, v_a_992_, v_b_993_);
return v___x_994_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_995_, lean_object* v_a_996_, lean_object* v_x_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_a_996_, v_x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_999_, lean_object* v_a_1000_, lean_object* v_x_1001_){
_start:
{
uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_res_1002_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_999_, v_a_1000_, v_x_1001_);
lean_dec(v_x_1001_);
lean_dec_ref(v_a_1000_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3(lean_object* v_00_u03b2_1004_, lean_object* v_data_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3___redArg(v_data_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1007_, lean_object* v_i_1008_, lean_object* v_source_1009_, lean_object* v_target_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_1008_, v_source_1009_, v_target_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FunInd_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = l_Lean_Expr_hasMVar(v_e_1016_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_e_1016_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v_mctx_1022_; lean_object* v___x_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1026_; lean_object* v_cache_1027_; lean_object* v_zetaDeltaFVarIds_1028_; lean_object* v_postponed_1029_; lean_object* v_diag_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1039_; 
v___x_1021_ = lean_st_ref_get(v___y_1017_);
v_mctx_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_mctx_1022_);
lean_dec(v___x_1021_);
v___x_1023_ = l_Lean_instantiateMVarsCore(v_mctx_1022_, v_e_1016_);
v_fst_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v___x_1023_, 1);
lean_inc(v_snd_1025_);
lean_dec_ref(v___x_1023_);
v___x_1026_ = lean_st_ref_take(v___y_1017_);
v_cache_1027_ = lean_ctor_get(v___x_1026_, 1);
v_zetaDeltaFVarIds_1028_ = lean_ctor_get(v___x_1026_, 2);
v_postponed_1029_ = lean_ctor_get(v___x_1026_, 3);
v_diag_1030_ = lean_ctor_get(v___x_1026_, 4);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v___x_1026_, 0);
lean_dec(v_unused_1040_);
v___x_1032_ = v___x_1026_;
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_diag_1030_);
lean_inc(v_postponed_1029_);
lean_inc(v_zetaDeltaFVarIds_1028_);
lean_inc(v_cache_1027_);
lean_dec(v___x_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v_snd_1025_);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_snd_1025_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_cache_1027_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_zetaDeltaFVarIds_1028_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_postponed_1029_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v_diag_1030_);
v___x_1035_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_st_ref_set(v___y_1017_, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_fst_1024_);
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1041_, v___y_1042_);
lean_dec(v___y_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1045_, v___y_1050_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1065_, size_t v_sz_1066_, size_t v_i_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_usize_dec_lt(v_i_1067_, v_sz_1066_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_b_1068_);
return v___x_1078_;
}
else
{
lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1137_; 
v_snd_1079_ = lean_ctor_get(v_b_1068_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_b_1068_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v_b_1068_, 0);
lean_dec(v_unused_1138_);
v___x_1081_ = v_b_1068_;
v_isShared_1082_ = v_isSharedCheck_1137_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snd_1079_);
lean_dec(v_b_1068_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1137_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v_a_1085_; lean_object* v_a_1092_; 
v___x_1083_ = lean_box(0);
v_a_1092_ = lean_array_uget_borrowed(v_as_1065_, v_i_1067_);
if (lean_obj_tag(v_a_1092_) == 0)
{
v_a_1085_ = v_snd_1079_;
goto v___jp_1084_;
}
else
{
lean_object* v_val_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
lean_dec(v_snd_1079_);
v_val_1093_ = lean_ctor_get(v_a_1092_, 0);
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Lean_LocalDecl_isAuxDecl(v_val_1093_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_LocalDecl_value_x3f(v_val_1093_, v___x_1095_);
if (lean_obj_tag(v___x_1096_) == 1)
{
lean_object* v_val_1097_; lean_object* v___x_1098_; 
v_val_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_val_1097_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1097_, v___y_1073_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1099_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_dec_ref(v___x_1100_);
v_a_1085_ = v___x_1094_;
goto v___jp_1084_;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_del_object(v___x_1081_);
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_del_object(v___x_1081_);
v_a_1109_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1098_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1098_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
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
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v___x_1096_);
v___x_1117_ = l_Lean_LocalDecl_type(v_val_1093_);
v___x_1118_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1117_, v___y_1073_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1119_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_dec_ref(v___x_1120_);
v_a_1085_ = v___x_1094_;
goto v___jp_1084_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_del_object(v___x_1081_);
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_del_object(v___x_1081_);
v_a_1129_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1118_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1118_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
else
{
v_a_1085_ = v___x_1094_;
goto v___jp_1084_;
}
}
v___jp_1084_:
{
lean_object* v___x_1087_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 1, v_a_1085_);
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1087_ = v___x_1081_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_a_1085_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
size_t v___x_1088_; size_t v___x_1089_; 
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1067_, v___x_1088_);
v_i_1067_ = v___x_1089_;
v_b_1068_ = v___x_1087_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1139_, lean_object* v_sz_1140_, lean_object* v_i_1141_, lean_object* v_b_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
size_t v_sz_boxed_1151_; size_t v_i_boxed_1152_; lean_object* v_res_1153_; 
v_sz_boxed_1151_ = lean_unbox_usize(v_sz_1140_);
lean_dec(v_sz_1140_);
v_i_boxed_1152_ = lean_unbox_usize(v_i_1141_);
lean_dec(v_i_1141_);
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1139_, v_sz_boxed_1151_, v_i_boxed_1152_, v_b_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v_as_1139_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1154_, size_t v_sz_1155_, size_t v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_usize_dec_lt(v_i_1156_, v_sz_1155_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_b_1157_);
return v___x_1167_;
}
else
{
lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1226_; 
v_snd_1168_ = lean_ctor_get(v_b_1157_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_b_1157_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v_b_1157_, 0);
lean_dec(v_unused_1227_);
v___x_1170_ = v_b_1157_;
v_isShared_1171_ = v_isSharedCheck_1226_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_dec(v_b_1157_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1226_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v_a_1174_; lean_object* v_a_1181_; 
v___x_1172_ = lean_box(0);
v_a_1181_ = lean_array_uget_borrowed(v_as_1154_, v_i_1156_);
if (lean_obj_tag(v_a_1181_) == 0)
{
v_a_1174_ = v_snd_1168_;
goto v___jp_1173_;
}
else
{
lean_object* v_val_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
lean_dec(v_snd_1168_);
v_val_1182_ = lean_ctor_get(v_a_1181_, 0);
v___x_1183_ = lean_box(0);
v___x_1184_ = l_Lean_LocalDecl_isAuxDecl(v_val_1182_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_LocalDecl_value_x3f(v_val_1182_, v___x_1184_);
if (lean_obj_tag(v___x_1185_) == 1)
{
lean_object* v_val_1186_; lean_object* v___x_1187_; 
v_val_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1186_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1186_, v___y_1162_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1188_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_dec_ref(v___x_1189_);
v_a_1174_ = v___x_1183_;
goto v___jp_1173_;
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_del_object(v___x_1170_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_del_object(v___x_1170_);
v_a_1198_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1187_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1187_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec(v___x_1185_);
v___x_1206_ = l_Lean_LocalDecl_type(v_val_1182_);
v___x_1207_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1206_, v___y_1162_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1208_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_dec_ref(v___x_1209_);
v_a_1174_ = v___x_1183_;
goto v___jp_1173_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1170_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_del_object(v___x_1170_);
v_a_1218_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1207_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1207_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
else
{
v_a_1174_ = v___x_1183_;
goto v___jp_1173_;
}
}
v___jp_1173_:
{
lean_object* v___x_1176_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_a_1174_);
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1176_ = v___x_1170_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_a_1174_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_add(v_i_1156_, v___x_1177_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1154_, v_sz_1155_, v___x_1178_, v___x_1176_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1228_, lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
size_t v_sz_boxed_1240_; size_t v_i_boxed_1241_; lean_object* v_res_1242_; 
v_sz_boxed_1240_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1241_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1228_, v_sz_boxed_1240_, v_i_boxed_1241_, v_b_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v_as_1228_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1243_, size_t v_sz_1244_, size_t v_i_1245_, lean_object* v_b_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_usize_dec_lt(v_i_1245_, v_sz_1244_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_b_1246_);
return v___x_1256_;
}
else
{
lean_object* v_snd_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1315_; 
v_snd_1257_ = lean_ctor_get(v_b_1246_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_b_1246_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v_b_1246_, 0);
lean_dec(v_unused_1316_);
v___x_1259_ = v_b_1246_;
v_isShared_1260_ = v_isSharedCheck_1315_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_snd_1257_);
lean_dec(v_b_1246_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1315_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v_a_1263_; lean_object* v_a_1270_; 
v___x_1261_ = lean_box(0);
v_a_1270_ = lean_array_uget_borrowed(v_as_1243_, v_i_1245_);
if (lean_obj_tag(v_a_1270_) == 0)
{
v_a_1263_ = v_snd_1257_;
goto v___jp_1262_;
}
else
{
lean_object* v_val_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
lean_dec(v_snd_1257_);
v_val_1271_ = lean_ctor_get(v_a_1270_, 0);
v___x_1272_ = lean_box(0);
v___x_1273_ = l_Lean_LocalDecl_isAuxDecl(v_val_1271_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_LocalDecl_value_x3f(v_val_1271_, v___x_1273_);
if (lean_obj_tag(v___x_1274_) == 1)
{
lean_object* v_val_1275_; lean_object* v___x_1276_; 
v_val_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1275_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1275_, v___y_1251_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1277_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_dec_ref(v___x_1278_);
v_a_1263_ = v___x_1272_;
goto v___jp_1262_;
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1259_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_del_object(v___x_1259_);
v_a_1287_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1276_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1276_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec(v___x_1274_);
v___x_1295_ = l_Lean_LocalDecl_type(v_val_1271_);
v___x_1296_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1295_, v___y_1251_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1297_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_dec_ref(v___x_1298_);
v_a_1263_ = v___x_1272_;
goto v___jp_1262_;
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_del_object(v___x_1259_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_del_object(v___x_1259_);
v_a_1307_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1296_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1296_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
else
{
v_a_1263_ = v___x_1272_;
goto v___jp_1262_;
}
}
v___jp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_a_1263_);
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1265_ = v___x_1259_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1263_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
size_t v___x_1266_; size_t v___x_1267_; 
v___x_1266_ = ((size_t)1ULL);
v___x_1267_ = lean_usize_add(v_i_1245_, v___x_1266_);
v_i_1245_ = v___x_1267_;
v_b_1246_ = v___x_1265_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1317_, lean_object* v_sz_1318_, lean_object* v_i_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
size_t v_sz_boxed_1329_; size_t v_i_boxed_1330_; lean_object* v_res_1331_; 
v_sz_boxed_1329_ = lean_unbox_usize(v_sz_1318_);
lean_dec(v_sz_1318_);
v_i_boxed_1330_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1317_, v_sz_boxed_1329_, v_i_boxed_1330_, v_b_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v_as_1317_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1332_, size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_b_1335_);
return v___x_1345_;
}
else
{
lean_object* v_snd_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1404_; 
v_snd_1346_ = lean_ctor_get(v_b_1335_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_b_1335_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v_b_1335_, 0);
lean_dec(v_unused_1405_);
v___x_1348_ = v_b_1335_;
v_isShared_1349_ = v_isSharedCheck_1404_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1346_);
lean_dec(v_b_1335_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1404_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v_a_1352_; lean_object* v_a_1359_; 
v___x_1350_ = lean_box(0);
v_a_1359_ = lean_array_uget_borrowed(v_as_1332_, v_i_1334_);
if (lean_obj_tag(v_a_1359_) == 0)
{
v_a_1352_ = v_snd_1346_;
goto v___jp_1351_;
}
else
{
lean_object* v_val_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
lean_dec(v_snd_1346_);
v_val_1360_ = lean_ctor_get(v_a_1359_, 0);
v___x_1361_ = lean_box(0);
v___x_1362_ = l_Lean_LocalDecl_isAuxDecl(v_val_1360_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_LocalDecl_value_x3f(v_val_1360_, v___x_1362_);
if (lean_obj_tag(v___x_1363_) == 1)
{
lean_object* v_val_1364_; lean_object* v___x_1365_; 
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1364_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1364_, v___y_1340_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1366_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_dec_ref(v___x_1367_);
v_a_1352_ = v___x_1361_;
goto v___jp_1351_;
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1348_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_del_object(v___x_1348_);
v_a_1376_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1365_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1365_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec(v___x_1363_);
v___x_1384_ = l_Lean_LocalDecl_type(v_val_1360_);
v___x_1385_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1384_, v___y_1340_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1386_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_dec_ref(v___x_1387_);
v_a_1352_ = v___x_1361_;
goto v___jp_1351_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_del_object(v___x_1348_);
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1348_);
v_a_1396_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1385_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1385_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
else
{
v_a_1352_ = v___x_1361_;
goto v___jp_1351_;
}
}
v___jp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v_a_1352_);
lean_ctor_set(v___x_1348_, 0, v___x_1350_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_a_1352_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_add(v_i_1334_, v___x_1355_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1332_, v_sz_1333_, v___x_1356_, v___x_1354_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1406_, lean_object* v_sz_1407_, lean_object* v_i_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1407_);
lean_dec(v_sz_1407_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1408_);
lean_dec(v_i_1408_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1406_, v_sz_boxed_1418_, v_i_boxed_1419_, v_b_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v_as_1406_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_inh_1421_, lean_object* v_n_1422_, lean_object* v_b_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
if (lean_obj_tag(v_n_1422_) == 0)
{
lean_object* v_cs_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1466_; 
v_cs_1432_ = lean_ctor_get(v_n_1422_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_n_1422_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1434_ = v_n_1422_;
v_isShared_1435_ = v_isSharedCheck_1466_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_cs_1432_);
lean_dec(v_n_1422_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1466_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; size_t v_sz_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v_b_1423_);
v_sz_1438_ = lean_array_size(v_cs_1432_);
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_inh_1421_, v_cs_1432_, v_sz_1438_, v___x_1439_, v___x_1437_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec_ref(v_cs_1432_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1457_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1457_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1457_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_fst_1445_; 
v_fst_1445_ = lean_ctor_get(v_a_1441_, 0);
if (lean_obj_tag(v_fst_1445_) == 0)
{
lean_object* v_snd_1446_; lean_object* v___x_1448_; 
v_snd_1446_ = lean_ctor_get(v_a_1441_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_a_1441_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 1);
lean_ctor_set(v___x_1434_, 0, v_snd_1446_);
v___x_1448_ = v___x_1434_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_snd_1446_);
v___x_1448_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1448_);
v___x_1450_ = v___x_1443_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_object* v_val_1453_; lean_object* v___x_1455_; 
lean_inc_ref(v_fst_1445_);
lean_dec(v_a_1441_);
lean_del_object(v___x_1434_);
v_val_1453_ = lean_ctor_get(v_fst_1445_, 0);
lean_inc(v_val_1453_);
lean_dec_ref(v_fst_1445_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v_val_1453_);
v___x_1455_ = v___x_1443_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_val_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_del_object(v___x_1434_);
v_a_1458_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1440_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1440_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_vs_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1501_; 
v_vs_1467_ = lean_ctor_get(v_n_1422_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_n_1422_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1469_ = v_n_1422_;
v_isShared_1470_ = v_isSharedCheck_1501_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_vs_1467_);
lean_dec(v_n_1422_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1501_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v_b_1423_);
v_sz_1473_ = lean_array_size(v_vs_1467_);
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1467_, v_sz_1473_, v___x_1474_, v___x_1472_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec_ref(v_vs_1467_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1492_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1492_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1492_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_fst_1480_; 
v_fst_1480_ = lean_ctor_get(v_a_1476_, 0);
if (lean_obj_tag(v_fst_1480_) == 0)
{
lean_object* v_snd_1481_; lean_object* v___x_1483_; 
v_snd_1481_ = lean_ctor_get(v_a_1476_, 1);
lean_inc(v_snd_1481_);
lean_dec(v_a_1476_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v_snd_1481_);
v___x_1483_ = v___x_1469_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_snd_1481_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1483_);
v___x_1485_ = v___x_1478_;
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
}
else
{
lean_object* v_val_1488_; lean_object* v___x_1490_; 
lean_inc_ref(v_fst_1480_);
lean_dec(v_a_1476_);
lean_del_object(v___x_1469_);
v_val_1488_ = lean_ctor_get(v_fst_1480_, 0);
lean_inc(v_val_1488_);
lean_dec_ref(v_fst_1480_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v_val_1488_);
v___x_1490_ = v___x_1478_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_val_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_del_object(v___x_1469_);
v_a_1493_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1475_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1475_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_inh_1502_, lean_object* v_as_1503_, size_t v_sz_1504_, size_t v_i_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_lt(v_i_1505_, v_sz_1504_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_b_1506_);
return v___x_1516_;
}
else
{
lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1551_; 
v_snd_1517_ = lean_ctor_get(v_b_1506_, 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_b_1506_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_b_1506_, 0);
lean_dec(v_unused_1552_);
v___x_1519_ = v_b_1506_;
v_isShared_1520_ = v_isSharedCheck_1551_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_dec(v_b_1506_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1551_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_a_1521_; lean_object* v___x_1522_; 
v_a_1521_ = lean_array_uget_borrowed(v_as_1503_, v_i_1505_);
lean_inc(v_snd_1517_);
lean_inc(v_a_1521_);
v___x_1522_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_inh_1502_, v_a_1521_, v_snd_1517_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1542_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1542_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1542_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
if (lean_obj_tag(v_a_1523_) == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_a_1523_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1527_);
v___x_1529_ = v___x_1519_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_snd_1517_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1529_);
v___x_1531_ = v___x_1525_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
lean_del_object(v___x_1525_);
lean_dec(v_snd_1517_);
v_a_1534_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v_a_1523_);
v___x_1535_ = lean_box(0);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 1, v_a_1534_);
lean_ctor_set(v___x_1519_, 0, v___x_1535_);
v___x_1537_ = v___x_1519_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_a_1534_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
size_t v___x_1538_; size_t v___x_1539_; 
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1505_, v___x_1538_);
v_i_1505_ = v___x_1539_;
v_b_1506_ = v___x_1537_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1519_);
lean_dec(v_snd_1517_);
v_a_1543_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1522_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1522_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_inh_1553_, lean_object* v_as_1554_, lean_object* v_sz_1555_, lean_object* v_i_1556_, lean_object* v_b_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
size_t v_sz_boxed_1566_; size_t v_i_boxed_1567_; lean_object* v_res_1568_; 
v_sz_boxed_1566_ = lean_unbox_usize(v_sz_1555_);
lean_dec(v_sz_1555_);
v_i_boxed_1567_ = lean_unbox_usize(v_i_1556_);
lean_dec(v_i_1556_);
v_res_1568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_inh_1553_, v_as_1554_, v_sz_boxed_1566_, v_i_boxed_1567_, v_b_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v_as_1554_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_inh_1569_, lean_object* v_n_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_inh_1569_, v_n_1570_, v_b_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1581_, lean_object* v_init_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_root_1591_; lean_object* v_tail_1592_; lean_object* v___x_1593_; 
v_root_1591_ = lean_ctor_get(v_t_1581_, 0);
lean_inc_ref(v_root_1591_);
v_tail_1592_ = lean_ctor_get(v_t_1581_, 1);
lean_inc_ref(v_tail_1592_);
lean_dec_ref(v_t_1581_);
v___x_1593_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1582_, v_root_1591_, v_init_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1630_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1630_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1630_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
if (lean_obj_tag(v_a_1594_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; 
lean_dec_ref(v_tail_1592_);
v_a_1598_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v_a_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_a_1598_);
v___x_1600_ = v___x_1596_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; size_t v_sz_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1596_);
v_a_1602_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v_a_1594_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1602_);
v_sz_1605_ = lean_array_size(v_tail_1592_);
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1592_, v_sz_1605_, v___x_1606_, v___x_1604_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec_ref(v_tail_1592_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1621_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_fst_1612_; 
v_fst_1612_ = lean_ctor_get(v_a_1608_, 0);
if (lean_obj_tag(v_fst_1612_) == 0)
{
lean_object* v_snd_1613_; lean_object* v___x_1615_; 
v_snd_1613_ = lean_ctor_get(v_a_1608_, 1);
lean_inc(v_snd_1613_);
lean_dec(v_a_1608_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_snd_1613_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_snd_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
lean_object* v_val_1617_; lean_object* v___x_1619_; 
lean_inc_ref(v_fst_1612_);
lean_dec(v_a_1608_);
v_val_1617_ = lean_ctor_get(v_fst_1612_, 0);
lean_inc(v_val_1617_);
lean_dec_ref(v_fst_1612_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_val_1617_);
v___x_1619_ = v___x_1610_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_val_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1607_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1607_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_tail_1592_);
v_a_1631_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1593_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1593_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1639_, lean_object* v_init_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1639_, v_init_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_lctx_1659_; lean_object* v_decls_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_lctx_1659_ = lean_ctor_get(v_a_1654_, 2);
v_decls_1660_ = lean_ctor_get(v_lctx_1659_, 1);
v___x_1661_ = lean_box(0);
lean_inc_ref(v_decls_1660_);
v___x_1662_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1660_, v___x_1661_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref(v___x_1662_);
v___x_1663_ = l_Lean_MVarId_getType(v_mvarId_1650_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1664_, v_a_1655_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref(v___x_1665_);
v___x_1667_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1666_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec_ref(v_a_1654_);
return v___x_1667_;
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref(v_a_1654_);
v_a_1668_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1665_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1665_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_a_1654_);
v_a_1676_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1663_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1663_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_dec_ref(v_a_1654_);
lean_dec(v_mvarId_1650_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1694_, lean_object* v_x_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1694_, v_x_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v_a_1710_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1701_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1701_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1718_, lean_object* v_x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1718_, v_x_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1726_, lean_object* v_mvarId_1727_, lean_object* v_x_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1727_, v_x_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_mvarId_1736_, lean_object* v_x_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1735_, v_mvarId_1736_, v_x_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1744_, lean_object* v___x_1745_, lean_object* v_mvarId_1746_, lean_object* v_needle_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_st_mk_ref(v___x_1744_);
v___x_1754_ = lean_st_mk_ref(v___x_1745_);
v___x_1755_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1746_, v___x_1754_, v_needle_1747_, v___x_1753_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1765_; 
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1755_, 0);
lean_dec(v_unused_1766_);
v___x_1757_ = v___x_1755_;
v_isShared_1758_ = v_isSharedCheck_1765_;
goto v_resetjp_1756_;
}
else
{
lean_dec(v___x_1755_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1765_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_calls_1761_; lean_object* v___x_1763_; 
v___x_1759_ = lean_st_ref_get(v___x_1754_);
lean_dec(v___x_1754_);
lean_dec(v___x_1759_);
v___x_1760_ = lean_st_ref_get(v___x_1753_);
lean_dec(v___x_1753_);
v_calls_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_ref(v_calls_1761_);
lean_dec(v___x_1760_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_calls_1761_);
v___x_1763_ = v___x_1757_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_calls_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v___x_1754_);
lean_dec(v___x_1753_);
v_a_1767_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1755_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1755_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v_mvarId_1777_, lean_object* v_needle_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1775_, v___x_1776_, v_mvarId_1777_, v_needle_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v_needle_1778_);
return v_res_1784_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(64u);
v___x_1786_ = l_Lean_mkPtrSet___redArg(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1787_, lean_object* v_mvarId_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; 
v___x_1794_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_1795_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
lean_inc(v_mvarId_1788_);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1796_, 0, v___x_1795_);
lean_closure_set(v___f_1796_, 1, v___x_1794_);
lean_closure_set(v___f_1796_, 2, v_mvarId_1788_);
lean_closure_set(v___f_1796_, 3, v_needle_1787_);
v___x_1797_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1788_, v___f_1796_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_1798_, lean_object* v_mvarId_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1798_, v_mvarId_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_1806_, lean_object* v_mvarId_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1806_, v_mvarId_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_1814_, lean_object* v_mvarId_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_1814_, v_mvarId_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_1822_, lean_object* v_mvarId_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Meta_FunInd_Collector_main(v_needle_1822_, v_mvarId_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_1830_, lean_object* v_mvarId_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Meta_FunInd_collect(v_needle_1830_, v_mvarId_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1837_;
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
