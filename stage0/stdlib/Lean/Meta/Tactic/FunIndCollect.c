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
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls;
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_FunInd_Collector_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_FunInd_Collector_visit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_cellCount_30_; lean_object* v___x_31_; 
v_cellCount_30_ = lean_unsigned_to_nat(16u);
v___x_31_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2(void){
_start:
{
lean_object* v_cellCount_32_; lean_object* v___x_33_; 
v_cellCount_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__2);
v___x_35_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__1);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
lean_ctor_set(v___x_37_, 2, v___x_34_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__3);
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
v___x_41_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4);
return v___x_41_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_isEmpty(lean_object* v_sc_42_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_isEmpty___boxed(lean_object* v_sc_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Lean_Meta_FunInd_SeenCalls_isEmpty(v_sc_47_);
lean_dec_ref(v_sc_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___redArg(lean_object* v_xs_50_, lean_object* v_ys_51_, lean_object* v_x_52_){
_start:
{
lean_object* v_zero_53_; uint8_t v_isZero_54_; 
v_zero_53_ = lean_unsigned_to_nat(0u);
v_isZero_54_ = lean_nat_dec_eq(v_x_52_, v_zero_53_);
if (v_isZero_54_ == 1)
{
lean_dec(v_x_52_);
return v_isZero_54_;
}
else
{
lean_object* v_one_55_; lean_object* v_n_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_one_55_ = lean_unsigned_to_nat(1u);
v_n_56_ = lean_nat_sub(v_x_52_, v_one_55_);
lean_dec(v_x_52_);
v___x_57_ = lean_array_fget_borrowed(v_xs_50_, v_n_56_);
v___x_58_ = lean_array_fget_borrowed(v_ys_51_, v_n_56_);
v___x_59_ = lean_expr_eqv(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_dec(v_n_56_);
return v___x_59_;
}
else
{
v_x_52_ = v_n_56_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_xs_61_, lean_object* v_ys_62_, lean_object* v_x_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___redArg(v_xs_61_, v_ys_62_, v_x_63_);
lean_dec_ref(v_ys_62_);
lean_dec_ref(v_xs_61_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___redArg(lean_object* v_m_66_, lean_object* v_query_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_zero_71_; uint8_t v_isZero_72_; 
v_zero_71_ = lean_unsigned_to_nat(0u);
v_isZero_72_ = lean_nat_dec_eq(v_x_69_, v_zero_71_);
if (v_isZero_72_ == 1)
{
lean_dec(v_x_70_);
lean_dec(v_x_69_);
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(2);
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
v_val_74_ = lean_ctor_get(v_x_68_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v_x_68_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v_x_68_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_val_74_);
lean_dec(v_x_68_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_val_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v_keyArray_82_; lean_object* v_valueArray_83_; lean_object* v___x_84_; uint8_t v_isSome_85_; 
v_keyArray_82_ = lean_ctor_get(v_m_66_, 1);
v_valueArray_83_ = lean_ctor_get(v_m_66_, 2);
v___x_84_ = lean_array_fget_borrowed(v_keyArray_82_, v_x_70_);
v_isSome_85_ = lean_noption_is_some(v___x_84_);
if (v_isSome_85_ == 0)
{
lean_dec(v_x_69_);
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_86_; 
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v_x_70_);
return v___x_86_;
}
else
{
lean_object* v_val_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_dec(v_x_70_);
v_val_87_ = lean_ctor_get(v_x_68_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_x_68_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v_x_68_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_val_87_);
lean_dec(v_x_68_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_val_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
else
{
lean_object* v_one_95_; lean_object* v_n_96_; lean_object* v___y_98_; 
v_one_95_ = lean_unsigned_to_nat(1u);
v_n_96_ = lean_nat_sub(v_x_69_, v_one_95_);
lean_dec(v_x_69_);
if (v_isSome_85_ == 0)
{
goto v___jp_104_;
}
else
{
lean_object* v___x_112_; uint8_t v_isSome_113_; 
v___x_112_ = lean_array_fget_borrowed(v_valueArray_83_, v_x_70_);
v_isSome_113_ = lean_noption_is_some(v___x_112_);
if (v_isSome_113_ == 0)
{
goto v___jp_104_;
}
else
{
lean_object* v_val_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v_val_119_; uint8_t v___y_121_; uint8_t v___x_123_; 
lean_inc(v___x_84_);
v_val_114_ = lean_noption_get(v___x_84_);
v_fst_115_ = lean_ctor_get(v_val_114_, 0);
lean_inc(v_fst_115_);
v_snd_116_ = lean_ctor_get(v_val_114_, 1);
lean_inc(v_snd_116_);
v_fst_117_ = lean_ctor_get(v_query_67_, 0);
v_snd_118_ = lean_ctor_get(v_query_67_, 1);
lean_inc(v___x_112_);
v_val_119_ = lean_noption_get(v___x_112_);
v___x_123_ = lean_name_eq(v_fst_115_, v_fst_117_);
lean_dec(v_fst_115_);
if (v___x_123_ == 0)
{
lean_dec(v_snd_116_);
v___y_121_ = v___x_123_;
goto v___jp_120_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_array_get_size(v_snd_116_);
v___x_125_ = lean_array_get_size(v_snd_118_);
v___x_126_ = lean_nat_dec_eq(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_dec(v_val_119_);
lean_dec(v_snd_116_);
lean_dec(v_val_114_);
goto v___jp_106_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___redArg(v_snd_116_, v_snd_118_, v___x_124_);
lean_dec(v_snd_116_);
v___y_121_ = v___x_127_;
goto v___jp_120_;
}
}
v___jp_120_:
{
if (v___y_121_ == 0)
{
lean_dec(v_val_119_);
lean_dec(v_val_114_);
goto v___jp_106_;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_n_96_);
lean_dec(v_x_68_);
v___x_122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_122_, 0, v_x_70_);
lean_ctor_set(v___x_122_, 1, v_val_114_);
lean_ctor_set(v___x_122_, 2, v_val_119_);
return v___x_122_;
}
}
}
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_array_get_size(v_keyArray_82_);
v___x_100_ = lean_nat_add(v_x_70_, v_one_95_);
lean_dec(v_x_70_);
v___x_101_ = lean_nat_dec_lt(v___x_100_, v___x_99_);
if (v___x_101_ == 0)
{
lean_dec(v___x_100_);
v_x_68_ = v___y_98_;
v_x_69_ = v_n_96_;
v_x_70_ = v_zero_71_;
goto _start;
}
else
{
v_x_68_ = v___y_98_;
v_x_69_ = v_n_96_;
v_x_70_ = v___x_100_;
goto _start;
}
}
v___jp_104_:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_105_; 
lean_inc(v_x_70_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v_x_70_);
v___y_98_ = v___x_105_;
goto v___jp_97_;
}
else
{
v___y_98_ = v_x_68_;
goto v___jp_97_;
}
}
v___jp_106_:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = lean_array_get_size(v_keyArray_82_);
v___x_108_ = lean_nat_add(v_x_70_, v_one_95_);
lean_dec(v_x_70_);
v___x_109_ = lean_nat_dec_lt(v___x_108_, v___x_107_);
if (v___x_109_ == 0)
{
lean_dec(v___x_108_);
v_x_69_ = v_n_96_;
v_x_70_ = v_zero_71_;
goto _start;
}
else
{
v_x_69_ = v_n_96_;
v_x_70_ = v___x_108_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___redArg___boxed(lean_object* v_m_128_, lean_object* v_query_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___redArg(v_m_128_, v_query_129_, v_x_130_, v_x_131_, v_x_132_);
lean_dec_ref(v_query_129_);
lean_dec_ref(v_m_128_);
return v_res_133_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(lean_object* v_as_134_, size_t v_i_135_, size_t v_stop_136_, uint64_t v_b_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_usize_dec_eq(v_i_135_, v_stop_136_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; 
v___x_139_ = lean_array_uget_borrowed(v_as_134_, v_i_135_);
v___x_140_ = l_Lean_Expr_hash(v___x_139_);
v___x_141_ = lean_uint64_mix_hash(v_b_137_, v___x_140_);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_add(v_i_135_, v___x_142_);
v_i_135_ = v___x_143_;
v_b_137_ = v___x_141_;
goto _start;
}
else
{
return v_b_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4___boxed(lean_object* v_as_145_, lean_object* v_i_146_, lean_object* v_stop_147_, lean_object* v_b_148_){
_start:
{
size_t v_i_boxed_149_; size_t v_stop_boxed_150_; uint64_t v_b_boxed_151_; uint64_t v_res_152_; lean_object* v_r_153_; 
v_i_boxed_149_ = lean_unbox_usize(v_i_146_);
lean_dec(v_i_146_);
v_stop_boxed_150_ = lean_unbox_usize(v_stop_147_);
lean_dec(v_stop_147_);
v_b_boxed_151_ = lean_unbox_uint64(v_b_148_);
lean_dec_ref(v_b_148_);
v_res_152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(v_as_145_, v_i_boxed_149_, v_stop_boxed_150_, v_b_boxed_151_);
lean_dec_ref(v_as_145_);
v_r_153_ = lean_box_uint64(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(lean_object* v_m_154_, lean_object* v_query_155_){
_start:
{
lean_object* v_keyArray_156_; lean_object* v_fst_157_; lean_object* v_snd_158_; lean_object* v___x_159_; uint64_t v___y_161_; uint64_t v___y_162_; uint64_t v___y_179_; 
v_keyArray_156_ = lean_ctor_get(v_m_154_, 1);
v_fst_157_ = lean_ctor_get(v_query_155_, 0);
v_snd_158_ = lean_ctor_get(v_query_155_, 1);
v___x_159_ = lean_array_get_size(v_keyArray_156_);
if (lean_obj_tag(v_fst_157_) == 0)
{
uint64_t v___x_191_; 
v___x_191_ = 1723ULL;
v___y_179_ = v___x_191_;
goto v___jp_178_;
}
else
{
uint64_t v_hash_192_; 
v_hash_192_ = lean_ctor_get_uint64(v_fst_157_, sizeof(void*)*2);
v___y_179_ = v_hash_192_;
goto v___jp_178_;
}
v___jp_160_:
{
uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v_fold_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_163_ = lean_uint64_mix_hash(v___y_161_, v___y_162_);
v___x_164_ = 32ULL;
v___x_165_ = lean_uint64_shift_right(v___x_163_, v___x_164_);
v_fold_166_ = lean_uint64_xor(v___x_163_, v___x_165_);
v___x_167_ = 16ULL;
v___x_168_ = lean_uint64_shift_right(v_fold_166_, v___x_167_);
v___x_169_ = lean_uint64_xor(v_fold_166_, v___x_168_);
v___x_170_ = lean_uint64_to_usize(v___x_169_);
v___x_171_ = lean_usize_of_nat(v___x_159_);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_sub(v___x_171_, v___x_172_);
v___x_174_ = lean_usize_land(v___x_170_, v___x_173_);
v___x_175_ = lean_usize_to_nat(v___x_174_);
v___x_176_ = lean_box(0);
v___x_177_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___redArg(v_m_154_, v_query_155_, v___x_176_, v___x_159_, v___x_175_);
return v___x_177_;
}
v___jp_178_:
{
uint64_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_180_ = 7ULL;
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_array_get_size(v_snd_158_);
v___x_183_ = lean_nat_dec_lt(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
v___y_161_ = v___y_179_;
v___y_162_ = v___x_180_;
goto v___jp_160_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = lean_nat_dec_le(v___x_182_, v___x_182_);
if (v___x_184_ == 0)
{
if (v___x_183_ == 0)
{
v___y_161_ = v___y_179_;
v___y_162_ = v___x_180_;
goto v___jp_160_;
}
else
{
size_t v___x_185_; size_t v___x_186_; uint64_t v___x_187_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_182_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(v_snd_158_, v___x_185_, v___x_186_, v___x_180_);
v___y_161_ = v___y_179_;
v___y_162_ = v___x_187_;
goto v___jp_160_;
}
}
else
{
size_t v___x_188_; size_t v___x_189_; uint64_t v___x_190_; 
v___x_188_ = ((size_t)0ULL);
v___x_189_ = lean_usize_of_nat(v___x_182_);
v___x_190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__4(v_snd_158_, v___x_188_, v___x_189_, v___x_180_);
v___y_161_ = v___y_179_;
v___y_162_ = v___x_190_;
goto v___jp_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg___boxed(lean_object* v_m_193_, lean_object* v_query_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_193_, v_query_194_);
lean_dec_ref(v_query_194_);
lean_dec_ref(v_m_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(lean_object* v_m_196_, lean_object* v_query_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_196_, v_query_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_index_199_; lean_object* v_key_200_; lean_object* v_value_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_index_199_ = lean_ctor_get(v___x_198_, 0);
v_key_200_ = lean_ctor_get(v___x_198_, 1);
v_value_201_ = lean_ctor_get(v___x_198_, 2);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_198_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_value_201_);
lean_inc(v_key_200_);
lean_inc(v_index_199_);
lean_dec(v___x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_index_199_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_key_200_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_value_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v___x_209_; 
lean_dec(v___x_198_);
v___x_209_ = lean_box(1);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg___boxed(lean_object* v_m_210_, lean_object* v_query_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_m_210_, v_query_211_);
lean_dec_ref(v_query_211_);
lean_dec_ref(v_m_210_);
return v_res_212_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(lean_object* v_m_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_m_213_, v_a_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
uint8_t v___x_216_; 
lean_dec_ref_known(v___x_215_, 3);
v___x_216_ = 1;
return v___x_216_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = 0;
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg___boxed(lean_object* v_m_218_, lean_object* v_a_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_218_, v_a_219_);
lean_dec_ref(v_a_219_);
lean_dec_ref(v_m_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(lean_object* v_calls_222_, lean_object* v_as_223_, size_t v_sz_224_, size_t v_i_225_, lean_object* v_b_226_){
_start:
{
lean_object* v_a_229_; uint8_t v___x_233_; 
v___x_233_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_dec_ref(v_calls_222_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_b_226_);
return v___x_234_;
}
else
{
lean_object* v_snd_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_292_; 
v_snd_235_ = lean_ctor_get(v_b_226_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_b_226_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_b_226_, 0);
lean_dec(v_unused_293_);
v___x_237_ = v_b_226_;
v_isShared_238_ = v_isSharedCheck_292_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_snd_235_);
lean_dec(v_b_226_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_292_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_snd_239_; lean_object* v_fst_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_291_; 
v_snd_239_ = lean_ctor_get(v_snd_235_, 1);
v_fst_240_ = lean_ctor_get(v_snd_235_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_snd_235_);
if (v_isSharedCheck_291_ == 0)
{
v___x_242_ = v_snd_235_;
v_isShared_243_ = v_isSharedCheck_291_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_snd_239_);
lean_inc(v_fst_240_);
lean_dec(v_snd_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_291_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_array_244_; lean_object* v_start_245_; lean_object* v_stop_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_array_244_ = lean_ctor_get(v_snd_239_, 0);
v_start_245_ = lean_ctor_get(v_snd_239_, 1);
v_stop_246_ = lean_ctor_get(v_snd_239_, 2);
v___x_247_ = lean_box(0);
v___x_248_ = lean_nat_dec_lt(v_start_245_, v_stop_246_);
if (v___x_248_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_calls_222_);
if (v_isShared_243_ == 0)
{
v___x_250_ = v___x_242_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_snd_239_);
v___x_250_ = v_reuseFailAlloc_255_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_250_);
lean_ctor_set(v___x_237_, 0, v___x_247_);
v___x_252_ = v___x_237_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
else
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_287_; 
lean_inc(v_stop_246_);
lean_inc(v_start_245_);
lean_inc_ref(v_array_244_);
v_isSharedCheck_287_ = !lean_is_exclusive(v_snd_239_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; 
v_unused_288_ = lean_ctor_get(v_snd_239_, 2);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_snd_239_, 1);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_snd_239_, 0);
lean_dec(v_unused_290_);
v___x_257_ = v_snd_239_;
v_isShared_258_ = v_isSharedCheck_287_;
goto v_resetjp_256_;
}
else
{
lean_dec(v_snd_239_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_287_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_a_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v_a_259_ = lean_array_uget_borrowed(v_as_223_, v_i_225_);
v___x_260_ = lean_array_fget(v_array_244_, v_start_245_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_start_245_, v___x_261_);
lean_dec(v_start_245_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_262_);
v___x_264_ = v___x_257_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_array_244_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_stop_246_);
v___x_264_ = v_reuseFailAlloc_286_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
uint8_t v___x_280_; 
v___x_280_ = lean_unbox(v___x_260_);
if (v___x_280_ == 2)
{
uint8_t v___x_281_; 
v___x_281_ = l_Lean_Expr_isFVar(v_a_259_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec(v___x_260_);
lean_del_object(v___x_242_);
lean_del_object(v___x_237_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_calls_222_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_fst_240_);
lean_ctor_set(v___x_283_, 1, v___x_264_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
else
{
goto v___jp_265_;
}
}
else
{
goto v___jp_265_;
}
v___jp_265_:
{
uint8_t v___x_266_; 
v___x_266_ = lean_unbox(v___x_260_);
lean_dec(v___x_260_);
if (v___x_266_ == 0)
{
lean_object* v___x_268_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_264_);
v___x_268_ = v___x_242_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_264_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_268_);
lean_ctor_set(v___x_237_, 0, v___x_247_);
v___x_270_ = v___x_237_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
v_a_229_ = v___x_270_;
goto v___jp_228_;
}
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_inc(v_a_259_);
v___x_273_ = lean_array_push(v_fst_240_, v_a_259_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_264_);
lean_ctor_set(v___x_242_, 0, v___x_273_);
v___x_275_ = v___x_242_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_264_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_275_);
lean_ctor_set(v___x_237_, 0, v___x_247_);
v___x_277_ = v___x_237_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
v_a_229_ = v___x_277_;
goto v___jp_228_;
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
v___jp_228_:
{
size_t v___x_230_; size_t v___x_231_; 
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_225_, v___x_230_);
v_i_225_ = v___x_231_;
v_b_226_ = v_a_229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg___boxed(lean_object* v_calls_294_, lean_object* v_as_295_, lean_object* v_sz_296_, lean_object* v_i_297_, lean_object* v_b_298_, lean_object* v___y_299_){
_start:
{
size_t v_sz_boxed_300_; size_t v_i_boxed_301_; lean_object* v_res_302_; 
v_sz_boxed_300_ = lean_unbox_usize(v_sz_296_);
lean_dec(v_sz_296_);
v_i_boxed_301_ = lean_unbox_usize(v_i_297_);
lean_dec(v_i_297_);
v_res_302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_294_, v_as_295_, v_sz_boxed_300_, v_i_boxed_301_, v_b_298_);
lean_dec_ref(v_as_295_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___redArg(lean_object* v_b_303_, lean_object* v_acc_304_, lean_object* v_i_305_){
_start:
{
lean_object* v___y_307_; lean_object* v_keyArray_315_; lean_object* v_valueArray_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_keyArray_315_ = lean_ctor_get(v_b_303_, 1);
v_valueArray_316_ = lean_ctor_get(v_b_303_, 2);
v___x_317_ = lean_array_get_size(v_keyArray_315_);
v___x_318_ = lean_nat_dec_lt(v_i_305_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_i_305_);
return v_acc_304_;
}
else
{
lean_object* v___x_319_; uint8_t v_isSome_320_; 
v___x_319_ = lean_array_fget_borrowed(v_keyArray_315_, v_i_305_);
v_isSome_320_ = lean_noption_is_some(v___x_319_);
if (v_isSome_320_ == 0)
{
goto v___jp_311_;
}
else
{
lean_object* v___x_321_; uint8_t v_isSome_322_; 
v___x_321_ = lean_array_fget_borrowed(v_valueArray_316_, v_i_305_);
v_isSome_322_ = lean_noption_is_some(v___x_321_);
if (v_isSome_322_ == 0)
{
goto v___jp_311_;
}
else
{
lean_object* v_val_323_; lean_object* v_val_324_; lean_object* v_i_326_; lean_object* v___x_331_; 
lean_inc(v___x_319_);
v_val_323_ = lean_noption_get(v___x_319_);
lean_inc(v___x_321_);
v_val_324_ = lean_noption_get(v___x_321_);
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_acc_304_, v_val_323_);
switch(lean_obj_tag(v___x_331_))
{
case 0:
{
lean_object* v_index_332_; lean_object* v_size_333_; lean_object* v___x_334_; 
v_index_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_index_332_);
lean_dec_ref_known(v___x_331_, 3);
v_size_333_ = lean_ctor_get(v_acc_304_, 0);
lean_inc(v_size_333_);
v___x_334_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_304_, v_size_333_, v_index_332_, v_val_323_, v_val_324_);
lean_dec(v_index_332_);
v___y_307_ = v___x_334_;
goto v___jp_306_;
}
case 1:
{
lean_object* v_index_335_; 
v_index_335_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_index_335_);
lean_dec_ref_known(v___x_331_, 1);
v_i_326_ = v_index_335_;
goto v___jp_325_;
}
default: 
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_304_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_index_338_; 
v_index_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_index_338_);
lean_dec_ref_known(v___x_337_, 1);
v_i_326_ = v_index_338_;
goto v___jp_325_;
}
else
{
lean_dec(v_val_324_);
lean_dec(v_val_323_);
v___y_307_ = v_acc_304_;
goto v___jp_306_;
}
}
}
v___jp_325_:
{
lean_object* v_size_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_size_327_ = lean_ctor_get(v_acc_304_, 0);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_size_327_, v___x_328_);
v___x_330_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_304_, v___x_329_, v_i_326_, v_val_323_, v_val_324_);
lean_dec(v_i_326_);
v___y_307_ = v___x_330_;
goto v___jp_306_;
}
}
}
}
v___jp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_i_305_, v___x_308_);
lean_dec(v_i_305_);
v_acc_304_ = v___y_307_;
v_i_305_ = v___x_309_;
goto _start;
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_i_305_, v___x_312_);
lean_dec(v_i_305_);
v_i_305_ = v___x_313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_b_339_, lean_object* v_acc_340_, lean_object* v_i_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___redArg(v_b_339_, v_acc_340_, v_i_341_);
lean_dec_ref(v_b_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___redArg(lean_object* v_init_343_, lean_object* v_b_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___redArg(v_b_344_, v_init_343_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___redArg___boxed(lean_object* v_init_347_, lean_object* v_b_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___redArg(v_init_347_, v_b_348_);
lean_dec_ref(v_b_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg(lean_object* v_m_350_){
_start:
{
lean_object* v_keyArray_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_cellCount_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_target_358_; lean_object* v___x_359_; 
v_keyArray_351_ = lean_ctor_get(v_m_350_, 1);
v___x_352_ = lean_array_get_size(v_keyArray_351_);
v___x_353_ = lean_unsigned_to_nat(2u);
v_cellCount_354_ = lean_nat_mul(v___x_352_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_354_);
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_354_);
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_354_);
v_target_358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_358_, 0, v___x_355_);
lean_ctor_set(v_target_358_, 1, v___x_356_);
lean_ctor_set(v_target_358_, 2, v___x_357_);
v___x_359_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___redArg(v_target_358_, v_m_350_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg___boxed(lean_object* v_m_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg(v_m_360_);
lean_dec_ref(v_m_360_);
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
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_486_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_486_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_486_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_486_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_fst_390_; 
v_fst_390_ = lean_ctor_get(v_a_386_, 0);
if (lean_obj_tag(v_fst_390_) == 0)
{
lean_object* v_snd_391_; lean_object* v_fst_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_480_; 
v_snd_391_ = lean_ctor_get(v_a_386_, 1);
lean_inc(v_snd_391_);
lean_dec(v_a_386_);
v_fst_392_ = lean_ctor_get(v_snd_391_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_snd_391_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_snd_391_, 1);
lean_dec(v_unused_481_);
v___x_394_ = v_snd_391_;
v_isShared_395_ = v_isSharedCheck_480_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_fst_392_);
lean_dec(v_snd_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_480_;
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
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_funName_371_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_fst_392_);
v___x_399_ = v_reuseFailAlloc_479_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
uint8_t v___x_400_; 
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_seen_397_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_473_; 
lean_inc_ref(v_seen_397_);
lean_inc_ref(v_calls_396_);
v_isSharedCheck_473_ = !lean_is_exclusive(v_calls_365_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; 
v_unused_474_ = lean_ctor_get(v_calls_365_, 1);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_calls_365_, 0);
lean_dec(v_unused_475_);
v___x_402_ = v_calls_365_;
v_isShared_403_ = v_isSharedCheck_473_;
goto v_resetjp_401_;
}
else
{
lean_dec(v_calls_365_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_473_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___y_406_; lean_object* v___x_413_; lean_object* v___y_415_; lean_object* v_i_416_; lean_object* v___y_422_; lean_object* v___y_431_; lean_object* v_i_432_; lean_object* v___x_446_; 
v___x_404_ = lean_array_push(v_calls_396_, v_e_362_);
v___x_413_ = lean_box(0);
v___x_446_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_seen_397_, v___x_399_);
switch(lean_obj_tag(v___x_446_))
{
case 0:
{
lean_dec_ref_known(v___x_446_, 3);
lean_dec_ref(v___x_399_);
v___y_406_ = v_seen_397_;
goto v___jp_405_;
}
case 1:
{
lean_object* v_index_447_; lean_object* v_size_448_; lean_object* v_keyArray_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_index_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_index_447_);
lean_dec_ref_known(v___x_446_, 1);
v_size_448_ = lean_ctor_get(v_seen_397_, 0);
v_keyArray_449_ = lean_ctor_get(v_seen_397_, 1);
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_add(v_size_448_, v___x_450_);
v___x_452_ = lean_array_get_size(v_keyArray_449_);
v___x_453_ = lean_nat_dec_lt(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec(v___x_451_);
lean_dec(v_index_447_);
goto v___jp_437_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_454_ = lean_unsigned_to_nat(4u);
v___x_455_ = lean_nat_mul(v___x_451_, v___x_454_);
v___x_456_ = lean_unsigned_to_nat(3u);
v___x_457_ = lean_nat_mul(v___x_452_, v___x_456_);
v___x_458_ = lean_nat_dec_le(v___x_455_, v___x_457_);
lean_dec(v___x_457_);
lean_dec(v___x_455_);
if (v___x_458_ == 0)
{
lean_dec(v___x_451_);
lean_dec(v_index_447_);
goto v___jp_437_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DHashMap_Raw_setEntry___redArg(v_seen_397_, v___x_451_, v_index_447_, v___x_399_, v___x_413_);
lean_dec(v_index_447_);
v___y_406_ = v___x_459_;
goto v___jp_405_;
}
}
}
default: 
{
lean_object* v_size_460_; lean_object* v_keyArray_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_size_460_ = lean_ctor_get(v_seen_397_, 0);
v_keyArray_461_ = lean_ctor_get(v_seen_397_, 1);
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = lean_nat_add(v_size_460_, v___x_462_);
v___x_464_ = lean_array_get_size(v_keyArray_461_);
v___x_465_ = lean_nat_dec_lt(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec(v___x_463_);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg(v_seen_397_);
lean_dec_ref(v_seen_397_);
v___y_422_ = v___x_466_;
goto v___jp_421_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_467_ = lean_unsigned_to_nat(4u);
v___x_468_ = lean_nat_mul(v___x_463_, v___x_467_);
lean_dec(v___x_463_);
v___x_469_ = lean_unsigned_to_nat(3u);
v___x_470_ = lean_nat_mul(v___x_464_, v___x_469_);
v___x_471_ = lean_nat_dec_le(v___x_468_, v___x_470_);
lean_dec(v___x_470_);
lean_dec(v___x_468_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg(v_seen_397_);
lean_dec_ref(v_seen_397_);
v___y_422_ = v___x_472_;
goto v___jp_421_;
}
else
{
v___y_422_ = v_seen_397_;
goto v___jp_421_;
}
}
}
}
v___jp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___y_406_);
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___y_406_);
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
v___jp_414_:
{
lean_object* v_size_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_size_417_ = lean_ctor_get(v___y_415_, 0);
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_size_417_, v___x_418_);
v___x_420_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_415_, v___x_419_, v_i_416_, v___x_399_, v___x_413_);
lean_dec(v_i_416_);
v___y_406_ = v___x_420_;
goto v___jp_405_;
}
v___jp_421_:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v___y_422_, v___x_399_);
switch(lean_obj_tag(v___x_423_))
{
case 0:
{
lean_object* v_index_424_; lean_object* v_size_425_; lean_object* v___x_426_; 
v_index_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_index_424_);
lean_dec_ref_known(v___x_423_, 3);
v_size_425_ = lean_ctor_get(v___y_422_, 0);
lean_inc(v_size_425_);
v___x_426_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_422_, v_size_425_, v_index_424_, v___x_399_, v___x_413_);
lean_dec(v_index_424_);
v___y_406_ = v___x_426_;
goto v___jp_405_;
}
case 1:
{
lean_object* v_index_427_; 
v_index_427_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_index_427_);
lean_dec_ref_known(v___x_423_, 1);
v___y_415_ = v___y_422_;
v_i_416_ = v_index_427_;
goto v___jp_414_;
}
default: 
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_422_, v___x_377_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_index_429_; 
v_index_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_index_429_);
lean_dec_ref_known(v___x_428_, 1);
v___y_415_ = v___y_422_;
v_i_416_ = v_index_429_;
goto v___jp_414_;
}
else
{
lean_dec_ref(v___x_399_);
v___y_406_ = v___y_422_;
goto v___jp_405_;
}
}
}
}
v___jp_430_:
{
lean_object* v_size_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_size_433_ = lean_ctor_get(v___y_431_, 0);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_size_433_, v___x_434_);
v___x_436_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_431_, v___x_435_, v_i_432_, v___x_399_, v___x_413_);
lean_dec(v_i_432_);
v___y_406_ = v___x_436_;
goto v___jp_405_;
}
v___jp_437_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg(v_seen_397_);
lean_dec_ref(v_seen_397_);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v___x_438_, v___x_399_);
switch(lean_obj_tag(v___x_439_))
{
case 0:
{
lean_object* v_index_440_; lean_object* v_size_441_; lean_object* v___x_442_; 
v_index_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_index_440_);
lean_dec_ref_known(v___x_439_, 3);
v_size_441_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_size_441_);
v___x_442_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_438_, v_size_441_, v_index_440_, v___x_399_, v___x_413_);
lean_dec(v_index_440_);
v___y_406_ = v___x_442_;
goto v___jp_405_;
}
case 1:
{
lean_object* v_index_443_; 
v_index_443_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_439_, 1);
v___y_431_ = v___x_438_;
v_i_432_ = v_index_443_;
goto v___jp_430_;
}
default: 
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_438_, v___x_377_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_index_445_; 
v_index_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_index_445_);
lean_dec_ref_known(v___x_444_, 1);
v___y_431_ = v___x_438_;
v_i_432_ = v_index_445_;
goto v___jp_430_;
}
else
{
lean_dec_ref(v___x_399_);
v___y_406_ = v___x_438_;
goto v___jp_405_;
}
}
}
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec_ref(v___x_399_);
lean_dec_ref(v_e_362_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_calls_365_);
v___x_477_ = v___x_388_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_calls_365_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
else
{
lean_object* v_val_482_; lean_object* v___x_484_; 
lean_inc_ref(v_fst_390_);
lean_dec(v_a_386_);
lean_dec(v_funName_371_);
lean_dec_ref(v_calls_365_);
lean_dec_ref(v_e_362_);
v_val_482_ = lean_ctor_get(v_fst_390_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v_fst_390_, 1);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_val_482_);
v___x_484_ = v___x_388_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_val_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_funName_371_);
lean_dec_ref(v_calls_365_);
lean_dec_ref(v_e_362_);
v_a_487_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_385_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_385_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_push___boxed(lean_object* v_e_495_, lean_object* v_funIndInfo_496_, lean_object* v_args_497_, lean_object* v_calls_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_495_, v_funIndInfo_496_, v_args_497_, v_calls_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec_ref(v_args_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(lean_object* v_calls_505_, lean_object* v_as_506_, size_t v_sz_507_, size_t v_i_508_, lean_object* v_b_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___redArg(v_calls_505_, v_as_506_, v_sz_507_, v_i_508_, v_b_509_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0___boxed(lean_object* v_calls_516_, lean_object* v_as_517_, lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_b_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
size_t v_sz_boxed_526_; size_t v_i_boxed_527_; lean_object* v_res_528_; 
v_sz_boxed_526_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_527_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_FunInd_SeenCalls_push_spec__0(v_calls_516_, v_as_517_, v_sz_boxed_526_, v_i_boxed_527_, v_b_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_as_517_);
return v_res_528_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(lean_object* v_00_u03b2_529_, lean_object* v_m_530_, lean_object* v_a_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___redArg(v_m_530_, v_a_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1___boxed(lean_object* v_00_u03b2_533_, lean_object* v_m_534_, lean_object* v_a_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1(v_00_u03b2_533_, v_m_534_, v_a_535_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_m_534_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(lean_object* v_00_u03b2_538_, lean_object* v_m_539_, lean_object* v_query_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___redArg(v_m_539_, v_query_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2___boxed(lean_object* v_00_u03b2_542_, lean_object* v_m_543_, lean_object* v_query_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2(v_00_u03b2_542_, v_m_543_, v_query_544_);
lean_dec_ref(v_query_544_);
lean_dec_ref(v_m_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3(lean_object* v_00_u03b2_546_, lean_object* v_m_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___redArg(v_m_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3___boxed(lean_object* v_00_u03b2_549_, lean_object* v_m_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3(v_00_u03b2_549_, v_m_550_);
lean_dec_ref(v_m_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(lean_object* v_00_u03b2_552_, lean_object* v_m_553_, lean_object* v_query_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___redArg(v_m_553_, v_query_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1___boxed(lean_object* v_00_u03b2_556_, lean_object* v_m_557_, lean_object* v_query_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_SeenCalls_push_spec__1_spec__1(v_00_u03b2_556_, v_m_557_, v_query_558_);
lean_dec_ref(v_query_558_);
lean_dec_ref(v_m_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3(lean_object* v_00_u03b2_560_, lean_object* v_m_561_, lean_object* v_query_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___redArg(v_m_561_, v_query_562_, v_x_563_, v_x_564_, v_x_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3___boxed(lean_object* v_00_u03b2_568_, lean_object* v_m_569_, lean_object* v_query_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3(v_00_u03b2_568_, v_m_569_, v_query_570_, v_x_571_, v_x_572_, v_x_573_, v_x_574_);
lean_dec_ref(v_query_570_);
lean_dec_ref(v_m_569_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6(lean_object* v_00_u03b2_576_, lean_object* v_init_577_, lean_object* v_b_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___redArg(v_init_577_, v_b_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6___boxed(lean_object* v_00_u03b2_580_, lean_object* v_init_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6(v_00_u03b2_580_, v_init_581_, v_b_582_);
lean_dec_ref(v_b_582_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4(lean_object* v_xs_584_, lean_object* v_ys_585_, lean_object* v_hsz_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___redArg(v_xs_584_, v_ys_585_, v_x_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4___boxed(lean_object* v_xs_590_, lean_object* v_ys_591_, lean_object* v_hsz_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_SeenCalls_push_spec__2_spec__3_spec__4(v_xs_590_, v_ys_591_, v_hsz_592_, v_x_593_, v_x_594_);
lean_dec_ref(v_ys_591_);
lean_dec_ref(v_xs_590_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_597_, lean_object* v_b_598_, lean_object* v_acc_599_, lean_object* v_i_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___redArg(v_b_598_, v_acc_599_, v_i_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_602_, lean_object* v_b_603_, lean_object* v_acc_604_, lean_object* v_i_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_SeenCalls_push_spec__3_spec__6_spec__8(v_00_u03b2_602_, v_b_603_, v_acc_604_, v_i_605_);
lean_dec_ref(v_b_603_);
return v_res_606_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(lean_object* v_snd_607_, lean_object* v_x_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_NameSet_contains(v_snd_607_, v_x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; 
v___x_610_ = 1;
return v___x_610_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = 0;
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed(lean_object* v_snd_612_, lean_object* v_x_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0(v_snd_612_, v_x_613_);
lean_dec(v_x_613_);
lean_dec(v_snd_612_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0_spec__0(lean_object* v_b_616_, lean_object* v_acc_617_, lean_object* v_i_618_){
_start:
{
lean_object* v_a_624_; lean_object* v_keyArray_628_; lean_object* v_valueArray_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_keyArray_628_ = lean_ctor_get(v_b_616_, 1);
v_valueArray_629_ = lean_ctor_get(v_b_616_, 2);
v___x_630_ = lean_array_get_size(v_keyArray_628_);
v___x_631_ = lean_nat_dec_lt(v_i_618_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_i_618_);
return v_acc_617_;
}
else
{
lean_object* v___x_632_; uint8_t v_isSome_633_; 
v___x_632_ = lean_array_fget_borrowed(v_keyArray_628_, v_i_618_);
v_isSome_633_ = lean_noption_is_some(v___x_632_);
if (v_isSome_633_ == 0)
{
goto v___jp_619_;
}
else
{
lean_object* v___x_634_; uint8_t v_isSome_635_; 
v___x_634_ = lean_array_fget_borrowed(v_valueArray_629_, v_i_618_);
v_isSome_635_ = lean_noption_is_some(v___x_634_);
if (v_isSome_635_ == 0)
{
goto v___jp_619_;
}
else
{
lean_object* v_val_636_; lean_object* v_fst_637_; lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_656_; 
lean_inc(v___x_632_);
v_val_636_ = lean_noption_get(v___x_632_);
v_fst_637_ = lean_ctor_get(v_val_636_, 0);
lean_inc(v_fst_637_);
lean_dec(v_val_636_);
v_fst_638_ = lean_ctor_get(v_acc_617_, 0);
v_snd_639_ = lean_ctor_get(v_acc_617_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_acc_617_);
if (v_isSharedCheck_656_ == 0)
{
v___x_641_ = v_acc_617_;
v_isShared_642_ = v_isSharedCheck_656_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_dec(v_acc_617_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_656_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
uint8_t v___x_643_; 
v___x_643_ = l_Lean_NameSet_contains(v_snd_639_, v_fst_637_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = l_Lean_NameSet_contains(v_fst_638_, v_fst_637_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_NameSet_insert(v_fst_638_, v_fst_637_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_645_);
v___x_647_ = v___x_641_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_snd_639_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v_a_624_ = v___x_647_;
goto v___jp_623_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = l_Lean_NameSet_insert(v_snd_639_, v_fst_637_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_649_);
v___x_651_ = v___x_641_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_a_624_ = v___x_651_;
goto v___jp_623_;
}
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v_fst_637_);
if (v_isShared_642_ == 0)
{
v___x_654_ = v___x_641_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_snd_639_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
v_a_624_ = v___x_654_;
goto v___jp_623_;
}
}
}
}
}
}
v___jp_619_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_i_618_, v___x_620_);
lean_dec(v_i_618_);
v_i_618_ = v___x_621_;
goto _start;
}
v___jp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_i_618_, v___x_625_);
lean_dec(v_i_618_);
v_acc_617_ = v_a_624_;
v_i_618_ = v___x_626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0_spec__0___boxed(lean_object* v_b_657_, lean_object* v_acc_658_, lean_object* v_i_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0_spec__0(v_b_657_, v_acc_658_, v_i_659_);
lean_dec_ref(v_b_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(lean_object* v_init_661_, lean_object* v_b_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0_spec__0(v_b_662_, v_init_661_, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0___boxed(lean_object* v_init_665_, lean_object* v_b_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v_init_665_, v_b_666_);
lean_dec_ref(v_b_666_);
return v_res_667_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0(void){
_start:
{
lean_object* v_seen_668_; lean_object* v___x_669_; 
v_seen_668_ = l_Lean_NameSet_empty;
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_seen_668_);
lean_ctor_set(v___x_669_, 1, v_seen_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object* v_calls_670_){
_start:
{
lean_object* v_seen_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___f_676_; lean_object* v___x_677_; 
v_seen_671_ = lean_ctor_get(v_calls_670_, 1);
v___x_672_ = lean_obj_once(&l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0, &l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0_once, _init_l_Lean_Meta_FunInd_SeenCalls_uniques___closed__0);
v___x_673_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Meta_FunInd_SeenCalls_uniques_spec__0(v___x_672_, v_seen_671_);
v_fst_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_fst_674_);
v_snd_675_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_snd_675_);
lean_dec_ref(v___x_673_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_SeenCalls_uniques___lam__0___boxed), 2, 1);
lean_closure_set(v___f_676_, 0, v_snd_675_);
v___x_677_ = l_Lean_NameSet_filter(v___f_676_, v_fst_674_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques___boxed(lean_object* v_calls_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Meta_FunInd_SeenCalls_uniques(v_calls_678_);
lean_dec_ref(v_calls_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(lean_object* v_e_680_, lean_object* v_funIndInfo_681_, lean_object* v_args_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_st_ref_get(v_a_683_);
v___x_690_ = l_Lean_Meta_FunInd_SeenCalls_push(v_e_680_, v_funIndInfo_681_, v_args_682_, v___x_689_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_700_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_700_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = lean_st_ref_swap(v_a_683_, v_a_691_);
lean_dec(v___x_695_);
v___x_696_ = lean_box(0);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_696_);
v___x_698_ = v___x_693_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_690_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_690_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___redArg___boxed(lean_object* v_e_709_, lean_object* v_funIndInfo_710_, lean_object* v_args_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_709_, v_funIndInfo_710_, v_args_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_args_711_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd(lean_object* v_e_719_, lean_object* v_funIndInfo_720_, lean_object* v_args_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_719_, v_funIndInfo_720_, v_args_721_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_saveFunInd___boxed(lean_object* v_e_730_, lean_object* v_funIndInfo_731_, lean_object* v_args_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_FunInd_Collector_saveFunInd(v_e_730_, v_funIndInfo_731_, v_args_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_args_732_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg(lean_object* v_e_741_, lean_object* v_funIndInfo_742_, lean_object* v_args_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_741_, v_funIndInfo_742_, v_args_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___redArg___boxed(lean_object* v_e_751_, lean_object* v_funIndInfo_752_, lean_object* v_args_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_FunInd_Collector_visitApp___redArg(v_e_751_, v_funIndInfo_752_, v_args_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_args_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp(lean_object* v_e_761_, lean_object* v_funIndInfo_762_, lean_object* v_args_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_761_, v_funIndInfo_762_, v_args_763_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visitApp___boxed(lean_object* v_e_772_, lean_object* v_funIndInfo_773_, lean_object* v_args_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_FunInd_Collector_visitApp(v_e_772_, v_funIndInfo_773_, v_args_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec_ref(v_args_774_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___redArg(lean_object* v_m_783_, lean_object* v_query_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_zero_788_; uint8_t v_isZero_789_; 
v_zero_788_ = lean_unsigned_to_nat(0u);
v_isZero_789_ = lean_nat_dec_eq(v_x_786_, v_zero_788_);
if (v_isZero_789_ == 1)
{
lean_dec(v_x_787_);
lean_dec(v_x_786_);
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_box(2);
return v___x_790_;
}
else
{
lean_object* v_val_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_val_791_ = lean_ctor_get(v_x_785_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v_x_785_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_val_791_);
lean_dec(v_x_785_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_val_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_keyArray_799_; lean_object* v_valueArray_800_; lean_object* v___x_801_; uint8_t v_isSome_802_; 
v_keyArray_799_ = lean_ctor_get(v_m_783_, 1);
v_valueArray_800_ = lean_ctor_get(v_m_783_, 2);
v___x_801_ = lean_array_fget_borrowed(v_keyArray_799_, v_x_787_);
v_isSome_802_ = lean_noption_is_some(v___x_801_);
if (v_isSome_802_ == 0)
{
lean_dec(v_x_786_);
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_x_787_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_x_787_);
v_val_804_ = lean_ctor_get(v_x_785_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v_x_785_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_val_804_);
lean_dec(v_x_785_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_val_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_one_812_; lean_object* v_n_813_; lean_object* v___y_815_; 
v_one_812_ = lean_unsigned_to_nat(1u);
v_n_813_ = lean_nat_sub(v_x_786_, v_one_812_);
lean_dec(v_x_786_);
if (v_isSome_802_ == 0)
{
goto v___jp_821_;
}
else
{
lean_object* v___x_823_; uint8_t v_isSome_824_; 
v___x_823_ = lean_array_fget_borrowed(v_valueArray_800_, v_x_787_);
v_isSome_824_ = lean_noption_is_some(v___x_823_);
if (v_isSome_824_ == 0)
{
goto v___jp_821_;
}
else
{
lean_object* v_val_825_; size_t v___x_826_; size_t v___x_827_; uint8_t v___x_828_; 
lean_inc(v___x_801_);
v_val_825_ = lean_noption_get(v___x_801_);
v___x_826_ = lean_ptr_addr(v_val_825_);
v___x_827_ = lean_ptr_addr(v_query_784_);
v___x_828_ = lean_usize_dec_eq(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
lean_dec(v_val_825_);
v___x_829_ = lean_array_get_size(v_keyArray_799_);
v___x_830_ = lean_nat_add(v_x_787_, v_one_812_);
lean_dec(v_x_787_);
v___x_831_ = lean_nat_dec_lt(v___x_830_, v___x_829_);
if (v___x_831_ == 0)
{
lean_dec(v___x_830_);
v_x_786_ = v_n_813_;
v_x_787_ = v_zero_788_;
goto _start;
}
else
{
v_x_786_ = v_n_813_;
v_x_787_ = v___x_830_;
goto _start;
}
}
else
{
lean_object* v_val_834_; lean_object* v___x_835_; 
lean_dec(v_n_813_);
lean_dec(v_x_785_);
lean_inc(v___x_823_);
v_val_834_ = lean_noption_get(v___x_823_);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v_x_787_);
lean_ctor_set(v___x_835_, 1, v_val_825_);
lean_ctor_set(v___x_835_, 2, v_val_834_);
return v___x_835_;
}
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_816_ = lean_array_get_size(v_keyArray_799_);
v___x_817_ = lean_nat_add(v_x_787_, v_one_812_);
lean_dec(v_x_787_);
v___x_818_ = lean_nat_dec_lt(v___x_817_, v___x_816_);
if (v___x_818_ == 0)
{
lean_dec(v___x_817_);
v_x_785_ = v___y_815_;
v_x_786_ = v_n_813_;
v_x_787_ = v_zero_788_;
goto _start;
}
else
{
v_x_785_ = v___y_815_;
v_x_786_ = v_n_813_;
v_x_787_ = v___x_817_;
goto _start;
}
}
v___jp_821_:
{
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v___x_822_; 
lean_inc(v_x_787_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_x_787_);
v___y_815_ = v___x_822_;
goto v___jp_814_;
}
else
{
v___y_815_ = v_x_785_;
goto v___jp_814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___redArg___boxed(lean_object* v_m_836_, lean_object* v_query_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___redArg(v_m_836_, v_query_837_, v_x_838_, v_x_839_, v_x_840_);
lean_dec_ref(v_query_837_);
lean_dec_ref(v_m_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(lean_object* v_m_842_, lean_object* v_query_843_){
_start:
{
lean_object* v_keyArray_844_; lean_object* v___x_845_; size_t v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v_fold_852_; uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_keyArray_844_ = lean_ctor_get(v_m_842_, 1);
v___x_845_ = lean_array_get_size(v_keyArray_844_);
v___x_846_ = lean_ptr_addr(v_query_843_);
v___x_847_ = lean_usize_to_uint64(v___x_846_);
v___x_848_ = 11ULL;
v___x_849_ = lean_uint64_mix_hash(v___x_847_, v___x_848_);
v___x_850_ = 32ULL;
v___x_851_ = lean_uint64_shift_right(v___x_849_, v___x_850_);
v_fold_852_ = lean_uint64_xor(v___x_849_, v___x_851_);
v___x_853_ = 16ULL;
v___x_854_ = lean_uint64_shift_right(v_fold_852_, v___x_853_);
v___x_855_ = lean_uint64_xor(v_fold_852_, v___x_854_);
v___x_856_ = lean_uint64_to_usize(v___x_855_);
v___x_857_ = lean_usize_of_nat(v___x_845_);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_sub(v___x_857_, v___x_858_);
v___x_860_ = lean_usize_land(v___x_856_, v___x_859_);
v___x_861_ = lean_usize_to_nat(v___x_860_);
v___x_862_ = lean_box(0);
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___redArg(v_m_842_, v_query_843_, v___x_862_, v___x_845_, v___x_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg___boxed(lean_object* v_m_864_, lean_object* v_query_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(v_m_864_, v_query_865_);
lean_dec_ref(v_query_865_);
lean_dec_ref(v_m_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(lean_object* v_m_867_, lean_object* v_query_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(v_m_867_, v_query_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_index_870_; lean_object* v_key_871_; lean_object* v_value_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_index_870_ = lean_ctor_get(v___x_869_, 0);
v_key_871_ = lean_ctor_get(v___x_869_, 1);
v_value_872_ = lean_ctor_get(v___x_869_, 2);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_869_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_value_872_);
lean_inc(v_key_871_);
lean_inc(v_index_870_);
lean_dec(v___x_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_index_870_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_key_871_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_value_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v___x_880_; 
lean_dec(v___x_869_);
v___x_880_ = lean_box(1);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg___boxed(lean_object* v_m_881_, lean_object* v_query_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_m_881_, v_query_882_);
lean_dec_ref(v_query_882_);
lean_dec_ref(v_m_881_);
return v_res_883_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(lean_object* v_m_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_m_884_, v_a_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
uint8_t v___x_887_; 
lean_dec_ref_known(v___x_886_, 3);
v___x_887_ = 1;
return v___x_887_;
}
else
{
uint8_t v___x_888_; 
v___x_888_ = 0;
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg___boxed(lean_object* v_m_889_, lean_object* v_a_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_889_, v_a_890_);
lean_dec_ref(v_a_890_);
lean_dec_ref(v_m_889_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___redArg(lean_object* v_b_893_, lean_object* v_acc_894_, lean_object* v_i_895_){
_start:
{
lean_object* v___y_897_; lean_object* v_keyArray_905_; lean_object* v_valueArray_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_keyArray_905_ = lean_ctor_get(v_b_893_, 1);
v_valueArray_906_ = lean_ctor_get(v_b_893_, 2);
v___x_907_ = lean_array_get_size(v_keyArray_905_);
v___x_908_ = lean_nat_dec_lt(v_i_895_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v_i_895_);
return v_acc_894_;
}
else
{
lean_object* v___x_909_; uint8_t v_isSome_910_; 
v___x_909_ = lean_array_fget_borrowed(v_keyArray_905_, v_i_895_);
v_isSome_910_ = lean_noption_is_some(v___x_909_);
if (v_isSome_910_ == 0)
{
goto v___jp_901_;
}
else
{
lean_object* v___x_911_; uint8_t v_isSome_912_; 
v___x_911_ = lean_array_fget_borrowed(v_valueArray_906_, v_i_895_);
v_isSome_912_ = lean_noption_is_some(v___x_911_);
if (v_isSome_912_ == 0)
{
goto v___jp_901_;
}
else
{
lean_object* v_val_913_; lean_object* v_val_914_; lean_object* v_i_916_; lean_object* v___x_921_; 
lean_inc(v___x_909_);
v_val_913_ = lean_noption_get(v___x_909_);
lean_inc(v___x_911_);
v_val_914_ = lean_noption_get(v___x_911_);
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(v_acc_894_, v_val_913_);
switch(lean_obj_tag(v___x_921_))
{
case 0:
{
lean_object* v_index_922_; lean_object* v_size_923_; lean_object* v___x_924_; 
v_index_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_index_922_);
lean_dec_ref_known(v___x_921_, 3);
v_size_923_ = lean_ctor_get(v_acc_894_, 0);
lean_inc(v_size_923_);
v___x_924_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_894_, v_size_923_, v_index_922_, v_val_913_, v_val_914_);
lean_dec(v_index_922_);
v___y_897_ = v___x_924_;
goto v___jp_896_;
}
case 1:
{
lean_object* v_index_925_; 
v_index_925_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_index_925_);
lean_dec_ref_known(v___x_921_, 1);
v_i_916_ = v_index_925_;
goto v___jp_915_;
}
default: 
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_894_, v___x_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_index_928_; 
v_index_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_index_928_);
lean_dec_ref_known(v___x_927_, 1);
v_i_916_ = v_index_928_;
goto v___jp_915_;
}
else
{
lean_dec(v_val_914_);
lean_dec(v_val_913_);
v___y_897_ = v_acc_894_;
goto v___jp_896_;
}
}
}
v___jp_915_:
{
lean_object* v_size_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_size_917_ = lean_ctor_get(v_acc_894_, 0);
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = lean_nat_add(v_size_917_, v___x_918_);
v___x_920_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_894_, v___x_919_, v_i_916_, v_val_913_, v_val_914_);
lean_dec(v_i_916_);
v___y_897_ = v___x_920_;
goto v___jp_896_;
}
}
}
}
v___jp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_i_895_, v___x_898_);
lean_dec(v_i_895_);
v_acc_894_ = v___y_897_;
v_i_895_ = v___x_899_;
goto _start;
}
v___jp_901_:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_add(v_i_895_, v___x_902_);
lean_dec(v_i_895_);
v_i_895_ = v___x_903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_b_929_, lean_object* v_acc_930_, lean_object* v_i_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___redArg(v_b_929_, v_acc_930_, v_i_931_);
lean_dec_ref(v_b_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___redArg(lean_object* v_init_933_, lean_object* v_b_934_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___redArg(v_b_934_, v_init_933_, v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___redArg___boxed(lean_object* v_init_937_, lean_object* v_b_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___redArg(v_init_937_, v_b_938_);
lean_dec_ref(v_b_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg(lean_object* v_m_940_){
_start:
{
lean_object* v_keyArray_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_cellCount_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_target_948_; lean_object* v___x_949_; 
v_keyArray_941_ = lean_ctor_get(v_m_940_, 1);
v___x_942_ = lean_array_get_size(v_keyArray_941_);
v___x_943_ = lean_unsigned_to_nat(2u);
v_cellCount_944_ = lean_nat_mul(v___x_942_, v___x_943_);
v___x_945_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_944_);
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_944_);
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_944_);
v_target_948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_948_, 0, v___x_945_);
lean_ctor_set(v_target_948_, 1, v___x_946_);
lean_ctor_set(v_target_948_, 2, v___x_947_);
v___x_949_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___redArg(v_target_948_, v_m_940_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg___boxed(lean_object* v_m_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg(v_m_950_);
lean_dec_ref(v_m_950_);
return v_res_951_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_visit___closed__0(void){
_start:
{
lean_object* v___x_952_; lean_object* v_dummy_953_; 
v___x_952_ = lean_box(0);
v_dummy_953_ = l_Lean_Expr_sort___override(v___x_952_);
return v_dummy_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__2(lean_object* v_e_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; 
if (lean_obj_tag(v_x_955_) == 5)
{
lean_object* v_fn_987_; lean_object* v_arg_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_fn_987_ = lean_ctor_get(v_x_955_, 0);
lean_inc_ref(v_fn_987_);
v_arg_988_ = lean_ctor_get(v_x_955_, 1);
lean_inc_ref(v_arg_988_);
lean_dec_ref_known(v_x_955_, 2);
v___x_989_ = lean_array_set(v_x_956_, v_x_957_, v_arg_988_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_sub(v_x_957_, v___x_990_);
lean_dec(v_x_957_);
v_x_955_ = v_fn_987_;
v_x_956_ = v___x_989_;
v_x_957_ = v___x_991_;
goto _start;
}
else
{
lean_dec(v_x_957_);
if (lean_obj_tag(v_x_955_) == 4)
{
lean_object* v_declName_993_; lean_object* v_funName_994_; uint8_t v___x_995_; 
v_declName_993_ = lean_ctor_get(v_x_955_, 0);
lean_inc(v_declName_993_);
lean_dec_ref_known(v_x_955_, 2);
v_funName_994_ = lean_ctor_get(v___y_959_, 0);
v___x_995_ = lean_name_eq(v_declName_993_, v_funName_994_);
lean_dec(v_declName_993_);
if (v___x_995_ == 0)
{
lean_dec_ref(v_e_954_);
v___y_967_ = v___y_958_;
v___y_968_ = v___y_959_;
v___y_969_ = v___y_960_;
v___y_970_ = v___y_961_;
v___y_971_ = v___y_962_;
v___y_972_ = v___y_963_;
v___y_973_ = v___y_964_;
goto v___jp_966_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = l_Lean_Expr_hasLooseBVars(v_e_954_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
lean_inc_ref(v___y_959_);
v___x_997_ = l_Lean_Meta_FunInd_Collector_saveFunInd___redArg(v_e_954_, v___y_959_, v_x_956_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_dec_ref_known(v___x_997_, 1);
v___y_967_ = v___y_958_;
v___y_968_ = v___y_959_;
v___y_969_ = v___y_960_;
v___y_970_ = v___y_961_;
v___y_971_ = v___y_962_;
v___y_972_ = v___y_963_;
v___y_973_ = v___y_964_;
goto v___jp_966_;
}
else
{
lean_dec_ref(v_x_956_);
return v___x_997_;
}
}
else
{
lean_dec_ref(v_e_954_);
v___y_967_ = v___y_958_;
v___y_968_ = v___y_959_;
v___y_969_ = v___y_960_;
v___y_970_ = v___y_961_;
v___y_971_ = v___y_962_;
v___y_972_ = v___y_963_;
v___y_973_ = v___y_964_;
goto v___jp_966_;
}
}
}
else
{
lean_object* v___x_998_; 
lean_dec_ref(v_e_954_);
v___x_998_ = l_Lean_Meta_FunInd_Collector_visit(v_x_955_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_dec_ref_known(v___x_998_, 1);
v___y_967_ = v___y_958_;
v___y_968_ = v___y_959_;
v___y_969_ = v___y_960_;
v___y_970_ = v___y_961_;
v___y_971_ = v___y_962_;
v___y_972_ = v___y_963_;
v___y_973_ = v___y_964_;
goto v___jp_966_;
}
else
{
lean_dec_ref(v_x_956_);
return v___x_998_;
}
}
}
v___jp_966_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_array_get_size(v_x_956_);
v___x_976_ = lean_box(0);
v___x_977_ = lean_nat_dec_lt(v___x_974_, v___x_975_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_dec_ref(v_x_956_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
return v___x_978_;
}
else
{
uint8_t v___x_979_; 
v___x_979_ = lean_nat_dec_le(v___x_975_, v___x_975_);
if (v___x_979_ == 0)
{
if (v___x_977_ == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v_x_956_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_976_);
return v___x_980_;
}
else
{
size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((size_t)0ULL);
v___x_982_ = lean_usize_of_nat(v___x_975_);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_956_, v___x_981_, v___x_982_, v___x_976_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec_ref(v_x_956_);
return v___x_983_;
}
}
else
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_975_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_x_956_, v___x_984_, v___x_985_, v___x_976_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec_ref(v_x_956_);
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit(lean_object* v_e_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_d_1009_; lean_object* v_b_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_st_ref_get(v_a_1000_);
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v___x_1020_, v_e_999_);
lean_dec(v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___y_1024_; lean_object* v___x_1050_; lean_object* v___y_1052_; lean_object* v_i_1053_; lean_object* v___y_1059_; lean_object* v___y_1069_; lean_object* v_i_1070_; lean_object* v___x_1085_; 
v___x_1022_ = lean_st_ref_take(v_a_1000_);
v___x_1050_ = lean_box(0);
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(v___x_1022_, v_e_999_);
switch(lean_obj_tag(v___x_1085_))
{
case 0:
{
lean_dec_ref_known(v___x_1085_, 3);
v___y_1024_ = v___x_1022_;
goto v___jp_1023_;
}
case 1:
{
lean_object* v_index_1086_; lean_object* v_size_1087_; lean_object* v_keyArray_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_index_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_index_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v_size_1087_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_size_1087_);
v_keyArray_1088_ = lean_ctor_get(v___x_1022_, 1);
lean_inc_ref(v_keyArray_1088_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_add(v_size_1087_, v___x_1089_);
lean_dec(v_size_1087_);
v___x_1091_ = lean_array_get_size(v_keyArray_1088_);
lean_dec_ref(v_keyArray_1088_);
v___x_1092_ = lean_nat_dec_lt(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_dec(v___x_1090_);
lean_dec(v_index_1086_);
goto v___jp_1075_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1093_ = lean_unsigned_to_nat(4u);
v___x_1094_ = lean_nat_mul(v___x_1090_, v___x_1093_);
v___x_1095_ = lean_unsigned_to_nat(3u);
v___x_1096_ = lean_nat_mul(v___x_1091_, v___x_1095_);
v___x_1097_ = lean_nat_dec_le(v___x_1094_, v___x_1096_);
lean_dec(v___x_1096_);
lean_dec(v___x_1094_);
if (v___x_1097_ == 0)
{
lean_dec(v___x_1090_);
lean_dec(v_index_1086_);
goto v___jp_1075_;
}
else
{
lean_object* v___x_1098_; 
lean_inc_ref(v_e_999_);
v___x_1098_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1022_, v___x_1090_, v_index_1086_, v_e_999_, v___x_1050_);
lean_dec(v_index_1086_);
v___y_1024_ = v___x_1098_;
goto v___jp_1023_;
}
}
}
default: 
{
lean_object* v_size_1099_; lean_object* v_keyArray_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_size_1099_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_size_1099_);
v_keyArray_1100_ = lean_ctor_get(v___x_1022_, 1);
lean_inc_ref(v_keyArray_1100_);
v___x_1101_ = lean_unsigned_to_nat(1u);
v___x_1102_ = lean_nat_add(v_size_1099_, v___x_1101_);
lean_dec(v_size_1099_);
v___x_1103_ = lean_array_get_size(v_keyArray_1100_);
lean_dec_ref(v_keyArray_1100_);
v___x_1104_ = lean_nat_dec_lt(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec(v___x_1102_);
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg(v___x_1022_);
lean_dec(v___x_1022_);
v___y_1059_ = v___x_1105_;
goto v___jp_1058_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1106_ = lean_unsigned_to_nat(4u);
v___x_1107_ = lean_nat_mul(v___x_1102_, v___x_1106_);
lean_dec(v___x_1102_);
v___x_1108_ = lean_unsigned_to_nat(3u);
v___x_1109_ = lean_nat_mul(v___x_1103_, v___x_1108_);
v___x_1110_ = lean_nat_dec_le(v___x_1107_, v___x_1109_);
lean_dec(v___x_1109_);
lean_dec(v___x_1107_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg(v___x_1022_);
lean_dec(v___x_1022_);
v___y_1059_ = v___x_1111_;
goto v___jp_1058_;
}
else
{
v___y_1059_ = v___x_1022_;
goto v___jp_1058_;
}
}
}
}
v___jp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_st_ref_put(v_a_1000_, v___y_1024_);
switch(lean_obj_tag(v_e_999_))
{
case 4:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec_ref_known(v_e_999_, 2);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
case 7:
{
lean_object* v_binderType_1028_; lean_object* v_body_1029_; 
v_binderType_1028_ = lean_ctor_get(v_e_999_, 1);
lean_inc_ref(v_binderType_1028_);
v_body_1029_ = lean_ctor_get(v_e_999_, 2);
lean_inc_ref(v_body_1029_);
lean_dec_ref_known(v_e_999_, 3);
v_d_1009_ = v_binderType_1028_;
v_b_1010_ = v_body_1029_;
v___y_1011_ = v_a_1000_;
v___y_1012_ = v_a_1001_;
v___y_1013_ = v_a_1002_;
v___y_1014_ = v_a_1003_;
v___y_1015_ = v_a_1004_;
v___y_1016_ = v_a_1005_;
v___y_1017_ = v_a_1006_;
goto v___jp_1008_;
}
case 6:
{
lean_object* v_binderType_1030_; lean_object* v_body_1031_; 
v_binderType_1030_ = lean_ctor_get(v_e_999_, 1);
lean_inc_ref(v_binderType_1030_);
v_body_1031_ = lean_ctor_get(v_e_999_, 2);
lean_inc_ref(v_body_1031_);
lean_dec_ref_known(v_e_999_, 3);
v_d_1009_ = v_binderType_1030_;
v_b_1010_ = v_body_1031_;
v___y_1011_ = v_a_1000_;
v___y_1012_ = v_a_1001_;
v___y_1013_ = v_a_1002_;
v___y_1014_ = v_a_1003_;
v___y_1015_ = v_a_1004_;
v___y_1016_ = v_a_1005_;
v___y_1017_ = v_a_1006_;
goto v___jp_1008_;
}
case 10:
{
lean_object* v_expr_1032_; 
v_expr_1032_ = lean_ctor_get(v_e_999_, 1);
lean_inc_ref(v_expr_1032_);
lean_dec_ref_known(v_e_999_, 2);
v_e_999_ = v_expr_1032_;
goto _start;
}
case 8:
{
lean_object* v_type_1034_; lean_object* v_value_1035_; lean_object* v_body_1036_; lean_object* v___x_1037_; 
v_type_1034_ = lean_ctor_get(v_e_999_, 1);
lean_inc_ref(v_type_1034_);
v_value_1035_ = lean_ctor_get(v_e_999_, 2);
lean_inc_ref(v_value_1035_);
v_body_1036_ = lean_ctor_get(v_e_999_, 3);
lean_inc_ref(v_body_1036_);
lean_dec_ref_known(v_e_999_, 4);
v___x_1037_ = l_Lean_Meta_FunInd_Collector_visit(v_type_1034_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref_known(v___x_1037_, 1);
v___x_1038_ = l_Lean_Meta_FunInd_Collector_visit(v_value_1035_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref_known(v___x_1038_, 1);
v_e_999_ = v_body_1036_;
goto _start;
}
else
{
lean_dec_ref(v_body_1036_);
return v___x_1038_;
}
}
else
{
lean_dec_ref(v_body_1036_);
lean_dec_ref(v_value_1035_);
return v___x_1037_;
}
}
case 5:
{
lean_object* v_dummy_1040_; lean_object* v_nargs_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_dummy_1040_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_visit___closed__0, &l_Lean_Meta_FunInd_Collector_visit___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_visit___closed__0);
v_nargs_1041_ = l_Lean_Expr_getAppNumArgs(v_e_999_);
lean_inc(v_nargs_1041_);
v___x_1042_ = lean_mk_array(v_nargs_1041_, v_dummy_1040_);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_sub(v_nargs_1041_, v___x_1043_);
lean_dec(v_nargs_1041_);
lean_inc_ref(v_e_999_);
v___x_1045_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__2(v_e_999_, v_e_999_, v___x_1042_, v___x_1044_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1045_;
}
case 11:
{
lean_object* v_struct_1046_; 
v_struct_1046_ = lean_ctor_get(v_e_999_, 2);
lean_inc_ref(v_struct_1046_);
lean_dec_ref_known(v_e_999_, 3);
v_e_999_ = v_struct_1046_;
goto _start;
}
default: 
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v_e_999_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
}
v___jp_1051_:
{
lean_object* v_size_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_size_1054_ = lean_ctor_get(v___y_1052_, 0);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_size_1054_, v___x_1055_);
lean_inc_ref(v_e_999_);
v___x_1057_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1052_, v___x_1056_, v_i_1053_, v_e_999_, v___x_1050_);
lean_dec(v_i_1053_);
v___y_1024_ = v___x_1057_;
goto v___jp_1023_;
}
v___jp_1058_:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(v___y_1059_, v_e_999_);
switch(lean_obj_tag(v___x_1060_))
{
case 0:
{
lean_object* v_index_1061_; lean_object* v_size_1062_; lean_object* v___x_1063_; 
v_index_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_index_1061_);
lean_dec_ref_known(v___x_1060_, 3);
v_size_1062_ = lean_ctor_get(v___y_1059_, 0);
lean_inc(v_size_1062_);
lean_inc_ref(v_e_999_);
v___x_1063_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1059_, v_size_1062_, v_index_1061_, v_e_999_, v___x_1050_);
lean_dec(v_index_1061_);
v___y_1024_ = v___x_1063_;
goto v___jp_1023_;
}
case 1:
{
lean_object* v_index_1064_; 
v_index_1064_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_index_1064_);
lean_dec_ref_known(v___x_1060_, 1);
v___y_1052_ = v___y_1059_;
v_i_1053_ = v_index_1064_;
goto v___jp_1051_;
}
default: 
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1059_, v___x_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_index_1067_; 
v_index_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_index_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___y_1052_ = v___y_1059_;
v_i_1053_ = v_index_1067_;
goto v___jp_1051_;
}
else
{
v___y_1024_ = v___y_1059_;
goto v___jp_1023_;
}
}
}
}
v___jp_1068_:
{
lean_object* v_size_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_size_1071_ = lean_ctor_get(v___y_1069_, 0);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_add(v_size_1071_, v___x_1072_);
lean_inc_ref(v_e_999_);
v___x_1074_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1069_, v___x_1073_, v_i_1070_, v_e_999_, v___x_1050_);
lean_dec(v_i_1070_);
v___y_1024_ = v___x_1074_;
goto v___jp_1023_;
}
v___jp_1075_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg(v___x_1022_);
lean_dec(v___x_1022_);
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(v___x_1076_, v_e_999_);
switch(lean_obj_tag(v___x_1077_))
{
case 0:
{
lean_object* v_index_1078_; lean_object* v_size_1079_; lean_object* v___x_1080_; 
v_index_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_index_1078_);
lean_dec_ref_known(v___x_1077_, 3);
v_size_1079_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_size_1079_);
lean_inc_ref(v_e_999_);
v___x_1080_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1076_, v_size_1079_, v_index_1078_, v_e_999_, v___x_1050_);
lean_dec(v_index_1078_);
v___y_1024_ = v___x_1080_;
goto v___jp_1023_;
}
case 1:
{
lean_object* v_index_1081_; 
v_index_1081_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_index_1081_);
lean_dec_ref_known(v___x_1077_, 1);
v___y_1069_ = v___x_1076_;
v_i_1070_ = v_index_1081_;
goto v___jp_1068_;
}
default: 
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1076_, v___x_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_index_1084_; 
v_index_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_index_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___y_1069_ = v___x_1076_;
v_i_1070_ = v_index_1084_;
goto v___jp_1068_;
}
else
{
v___y_1024_ = v___x_1076_;
goto v___jp_1023_;
}
}
}
}
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec_ref(v_e_999_);
v___x_1112_ = lean_box(0);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
v___jp_1008_:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Meta_FunInd_Collector_visit(v_d_1009_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_dec_ref_known(v___x_1018_, 1);
v_e_999_ = v_b_1010_;
v_a_1000_ = v___y_1011_;
v_a_1001_ = v___y_1012_;
v_a_1002_ = v___y_1013_;
v_a_1003_ = v___y_1014_;
v_a_1004_ = v___y_1015_;
v_a_1005_ = v___y_1016_;
v_a_1006_ = v___y_1017_;
goto _start;
}
else
{
lean_dec_ref(v_b_1010_);
return v___x_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(lean_object* v_as_1114_, size_t v_i_1115_, size_t v_stop_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_usize_dec_eq(v_i_1115_, v_stop_1116_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_array_uget_borrowed(v_as_1114_, v_i_1115_);
lean_inc(v___x_1127_);
v___x_1128_ = l_Lean_Meta_FunInd_Collector_visit(v___x_1127_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; size_t v___x_1130_; size_t v___x_1131_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_add(v_i_1115_, v___x_1130_);
v_i_1115_ = v___x_1131_;
v_b_1117_ = v_a_1129_;
goto _start;
}
else
{
return v___x_1128_;
}
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_b_1117_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0___boxed(lean_object* v_as_1134_, lean_object* v_i_1135_, lean_object* v_stop_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
size_t v_i_boxed_1146_; size_t v_stop_boxed_1147_; lean_object* v_res_1148_; 
v_i_boxed_1146_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_stop_boxed_1147_ = lean_unbox_usize(v_stop_1136_);
lean_dec(v_stop_1136_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_FunInd_Collector_visit_spec__0(v_as_1134_, v_i_boxed_1146_, v_stop_boxed_1147_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v_as_1134_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__2___boxed(lean_object* v_e_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_FunInd_Collector_visit_spec__2(v_e_1149_, v_x_1150_, v_x_1151_, v_x_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_visit___boxed(lean_object* v_e_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_FunInd_Collector_visit(v_e_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
return v_res_1171_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(lean_object* v_00_u03b2_1172_, lean_object* v_m_1173_, lean_object* v_a_1174_){
_start:
{
uint8_t v___x_1175_; 
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___redArg(v_m_1173_, v_a_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1___boxed(lean_object* v_00_u03b2_1176_, lean_object* v_m_1177_, lean_object* v_a_1178_){
_start:
{
uint8_t v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1(v_00_u03b2_1176_, v_m_1177_, v_a_1178_);
lean_dec_ref(v_a_1178_);
lean_dec_ref(v_m_1177_);
v_r_1180_ = lean_box(v_res_1179_);
return v_r_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3(lean_object* v_00_u03b2_1181_, lean_object* v_m_1182_, lean_object* v_query_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___redArg(v_m_1182_, v_query_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3___boxed(lean_object* v_00_u03b2_1185_, lean_object* v_m_1186_, lean_object* v_query_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3(v_00_u03b2_1185_, v_m_1186_, v_query_1187_);
lean_dec_ref(v_query_1187_);
lean_dec_ref(v_m_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4(lean_object* v_00_u03b2_1189_, lean_object* v_m_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___redArg(v_m_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4___boxed(lean_object* v_00_u03b2_1192_, lean_object* v_m_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4(v_00_u03b2_1192_, v_m_1193_);
lean_dec_ref(v_m_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(lean_object* v_00_u03b2_1195_, lean_object* v_m_1196_, lean_object* v_query_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___redArg(v_m_1196_, v_query_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1199_, lean_object* v_m_1200_, lean_object* v_query_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FunInd_Collector_visit_spec__1_spec__1(v_00_u03b2_1199_, v_m_1200_, v_query_1201_);
lean_dec_ref(v_query_1201_);
lean_dec_ref(v_m_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4(lean_object* v_00_u03b2_1203_, lean_object* v_m_1204_, lean_object* v_query_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___redArg(v_m_1204_, v_query_1205_, v_x_1206_, v_x_1207_, v_x_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1211_, lean_object* v_m_1212_, lean_object* v_query_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_FunInd_Collector_visit_spec__3_spec__4(v_00_u03b2_1211_, v_m_1212_, v_query_1213_, v_x_1214_, v_x_1215_, v_x_1216_, v_x_1217_);
lean_dec_ref(v_query_1213_);
lean_dec_ref(v_m_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6(lean_object* v_00_u03b2_1219_, lean_object* v_init_1220_, lean_object* v_b_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___redArg(v_init_1220_, v_b_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1223_, lean_object* v_init_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6(v_00_u03b2_1223_, v_init_1224_, v_b_1225_);
lean_dec_ref(v_b_1225_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_1227_, lean_object* v_b_1228_, lean_object* v_acc_1229_, lean_object* v_i_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___redArg(v_b_1228_, v_acc_1229_, v_i_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1232_, lean_object* v_b_1233_, lean_object* v_acc_1234_, lean_object* v_i_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_FunInd_Collector_visit_spec__4_spec__6_spec__7(v_00_u03b2_1232_, v_b_1233_, v_acc_1234_, v_i_1235_);
lean_dec_ref(v_b_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(lean_object* v_e_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = l_Lean_Expr_hasMVar(v_e_1237_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_e_1237_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; lean_object* v_mctx_1243_; lean_object* v___x_1244_; lean_object* v_fst_1245_; lean_object* v_snd_1246_; lean_object* v___x_1247_; lean_object* v_cache_1248_; lean_object* v_zetaDeltaFVarIds_1249_; lean_object* v_postponed_1250_; lean_object* v_diag_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1260_; 
v___x_1242_ = lean_st_ref_get(v___y_1238_);
v_mctx_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_mctx_1243_);
lean_dec(v___x_1242_);
v___x_1244_ = l_Lean_instantiateMVarsCore(v_mctx_1243_, v_e_1237_);
v_fst_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_fst_1245_);
v_snd_1246_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_snd_1246_);
lean_dec_ref(v___x_1244_);
v___x_1247_ = lean_st_ref_take(v___y_1238_);
v_cache_1248_ = lean_ctor_get(v___x_1247_, 1);
v_zetaDeltaFVarIds_1249_ = lean_ctor_get(v___x_1247_, 2);
v_postponed_1250_ = lean_ctor_get(v___x_1247_, 3);
v_diag_1251_ = lean_ctor_get(v___x_1247_, 4);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v___x_1247_, 0);
lean_dec(v_unused_1261_);
v___x_1253_ = v___x_1247_;
v_isShared_1254_ = v_isSharedCheck_1260_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_diag_1251_);
lean_inc(v_postponed_1250_);
lean_inc(v_zetaDeltaFVarIds_1249_);
lean_inc(v_cache_1248_);
lean_dec(v___x_1247_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1260_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v_snd_1246_);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_snd_1246_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_cache_1248_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_zetaDeltaFVarIds_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_postponed_1250_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_diag_1251_);
v___x_1256_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_st_ref_put(v___y_1238_, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_fst_1245_);
return v___x_1258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg___boxed(lean_object* v_e_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1262_, v___y_1263_);
lean_dec(v___y_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(lean_object* v_e_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_e_1266_, v___y_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___boxed(lean_object* v_e_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0(v_e_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_1286_, size_t v_sz_1287_, size_t v_i_1288_, lean_object* v_b_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_b_1289_);
return v___x_1299_;
}
else
{
lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1358_; 
v_snd_1300_ = lean_ctor_get(v_b_1289_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_b_1289_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v_b_1289_, 0);
lean_dec(v_unused_1359_);
v___x_1302_ = v_b_1289_;
v_isShared_1303_ = v_isSharedCheck_1358_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_dec(v_b_1289_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1358_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v_a_1306_; lean_object* v_a_1313_; 
v___x_1304_ = lean_box(0);
v_a_1313_ = lean_array_uget_borrowed(v_as_1286_, v_i_1288_);
if (lean_obj_tag(v_a_1313_) == 0)
{
v_a_1306_ = v_snd_1300_;
goto v___jp_1305_;
}
else
{
lean_object* v_val_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
lean_dec(v_snd_1300_);
v_val_1314_ = lean_ctor_get(v_a_1313_, 0);
v___x_1315_ = lean_box(0);
v___x_1316_ = l_Lean_LocalDecl_isAuxDecl(v_val_1314_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_LocalDecl_value_x3f(v_val_1314_, v___x_1316_);
if (lean_obj_tag(v___x_1317_) == 1)
{
lean_object* v_val_1318_; lean_object* v___x_1319_; 
v_val_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1318_, v___y_1294_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1320_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_dec_ref_known(v___x_1321_, 1);
v_a_1306_ = v___x_1315_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_del_object(v___x_1302_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_del_object(v___x_1302_);
v_a_1330_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1319_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1319_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v___x_1317_);
v___x_1338_ = l_Lean_LocalDecl_type(v_val_1314_);
v___x_1339_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1338_, v___y_1294_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v___x_1341_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1340_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref_known(v___x_1341_, 1);
v_a_1306_ = v___x_1315_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1302_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_del_object(v___x_1302_);
v_a_1350_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1339_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1339_);
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
}
else
{
v_a_1306_ = v___x_1315_;
goto v___jp_1305_;
}
}
v___jp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 1, v_a_1306_);
lean_ctor_set(v___x_1302_, 0, v___x_1304_);
v___x_1308_ = v___x_1302_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_a_1306_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
size_t v___x_1309_; size_t v___x_1310_; 
v___x_1309_ = ((size_t)1ULL);
v___x_1310_ = lean_usize_add(v_i_1288_, v___x_1309_);
v_i_1288_ = v___x_1310_;
v_b_1289_ = v___x_1308_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
size_t v_sz_boxed_1372_; size_t v_i_boxed_1373_; lean_object* v_res_1374_; 
v_sz_boxed_1372_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1373_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1360_, v_sz_boxed_1372_, v_i_boxed_1373_, v_b_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v_as_1360_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(lean_object* v_as_1375_, size_t v_sz_1376_, size_t v_i_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v___x_1387_; 
v___x_1387_ = lean_usize_dec_lt(v_i_1377_, v_sz_1376_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_b_1378_);
return v___x_1388_;
}
else
{
lean_object* v_snd_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1447_; 
v_snd_1389_ = lean_ctor_get(v_b_1378_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_b_1378_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_b_1378_, 0);
lean_dec(v_unused_1448_);
v___x_1391_ = v_b_1378_;
v_isShared_1392_ = v_isSharedCheck_1447_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snd_1389_);
lean_dec(v_b_1378_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1447_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v_a_1395_; lean_object* v_a_1402_; 
v___x_1393_ = lean_box(0);
v_a_1402_ = lean_array_uget_borrowed(v_as_1375_, v_i_1377_);
if (lean_obj_tag(v_a_1402_) == 0)
{
v_a_1395_ = v_snd_1389_;
goto v___jp_1394_;
}
else
{
lean_object* v_val_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
lean_dec(v_snd_1389_);
v_val_1403_ = lean_ctor_get(v_a_1402_, 0);
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_LocalDecl_isAuxDecl(v_val_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_LocalDecl_value_x3f(v_val_1403_, v___x_1405_);
if (lean_obj_tag(v___x_1406_) == 1)
{
lean_object* v_val_1407_; lean_object* v___x_1408_; 
v_val_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1407_, v___y_1383_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1409_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_dec_ref_known(v___x_1410_, 1);
v_a_1395_ = v___x_1404_;
goto v___jp_1394_;
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_del_object(v___x_1391_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1391_);
v_a_1419_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1408_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1408_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v___x_1406_);
v___x_1427_ = l_Lean_LocalDecl_type(v_val_1403_);
v___x_1428_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1427_, v___y_1383_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1429_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_dec_ref_known(v___x_1430_, 1);
v_a_1395_ = v___x_1404_;
goto v___jp_1394_;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_del_object(v___x_1391_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_del_object(v___x_1391_);
v_a_1439_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1428_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1428_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
else
{
v_a_1395_ = v___x_1404_;
goto v___jp_1394_;
}
}
v___jp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v_a_1395_);
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1397_ = v___x_1391_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_a_1395_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
size_t v___x_1398_; size_t v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1377_, v___x_1398_);
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3_spec__4(v_as_1375_, v_sz_1376_, v___x_1399_, v___x_1397_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
return v___x_1400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1449_, lean_object* v_sz_1450_, lean_object* v_i_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
size_t v_sz_boxed_1461_; size_t v_i_boxed_1462_; lean_object* v_res_1463_; 
v_sz_boxed_1461_ = lean_unbox_usize(v_sz_1450_);
lean_dec(v_sz_1450_);
v_i_boxed_1462_ = lean_unbox_usize(v_i_1451_);
lean_dec(v_i_1451_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_as_1449_, v_sz_boxed_1461_, v_i_boxed_1462_, v_b_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v_as_1449_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(lean_object* v_init_1464_, lean_object* v_n_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
if (lean_obj_tag(v_n_1465_) == 0)
{
lean_object* v_cs_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; size_t v_sz_1478_; size_t v___x_1479_; lean_object* v___x_1480_; 
v_cs_1475_ = lean_ctor_get(v_n_1465_, 0);
v___x_1476_ = lean_box(0);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v_b_1466_);
v_sz_1478_ = lean_array_size(v_cs_1475_);
v___x_1479_ = ((size_t)0ULL);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1464_, v_cs_1475_, v_sz_1478_, v___x_1479_, v___x_1477_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1495_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1495_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1495_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_fst_1485_; 
v_fst_1485_ = lean_ctor_get(v_a_1481_, 0);
if (lean_obj_tag(v_fst_1485_) == 0)
{
lean_object* v_snd_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v_snd_1486_ = lean_ctor_get(v_a_1481_, 1);
lean_inc(v_snd_1486_);
lean_dec(v_a_1481_);
v___x_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_snd_1486_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1487_);
v___x_1489_ = v___x_1483_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
else
{
lean_object* v_val_1491_; lean_object* v___x_1493_; 
lean_inc_ref(v_fst_1485_);
lean_dec(v_a_1481_);
v_val_1491_ = lean_ctor_get(v_fst_1485_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v_fst_1485_, 1);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_val_1491_);
v___x_1493_ = v___x_1483_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_val_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1480_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1480_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_vs_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v_vs_1504_ = lean_ctor_get(v_n_1465_, 0);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v_b_1466_);
v_sz_1507_ = lean_array_size(v_vs_1504_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__3(v_vs_1504_, v_sz_1507_, v___x_1508_, v___x_1506_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1524_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1524_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1524_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_fst_1514_; 
v_fst_1514_ = lean_ctor_get(v_a_1510_, 0);
if (lean_obj_tag(v_fst_1514_) == 0)
{
lean_object* v_snd_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v_snd_1515_ = lean_ctor_get(v_a_1510_, 1);
lean_inc(v_snd_1515_);
lean_dec(v_a_1510_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_snd_1515_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1516_);
v___x_1518_ = v___x_1512_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
else
{
lean_object* v_val_1520_; lean_object* v___x_1522_; 
lean_inc_ref(v_fst_1514_);
lean_dec(v_a_1510_);
v_val_1520_ = lean_ctor_get(v_fst_1514_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v_fst_1514_, 1);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_val_1520_);
v___x_1522_ = v___x_1512_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_val_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_a_1525_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1509_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1509_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(lean_object* v_init_1533_, lean_object* v_as_1534_, size_t v_sz_1535_, size_t v_i_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_usize_dec_lt(v_i_1536_, v_sz_1535_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_b_1537_);
return v___x_1547_;
}
else
{
lean_object* v_snd_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1582_; 
v_snd_1548_ = lean_ctor_get(v_b_1537_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_b_1537_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_b_1537_, 0);
lean_dec(v_unused_1583_);
v___x_1550_ = v_b_1537_;
v_isShared_1551_ = v_isSharedCheck_1582_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_snd_1548_);
lean_dec(v_b_1537_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1582_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_array_uget_borrowed(v_as_1534_, v_i_1536_);
lean_inc(v_snd_1548_);
v___x_1553_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1533_, v_a_1552_, v_snd_1548_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1573_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1573_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1573_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
if (lean_obj_tag(v_a_1554_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_a_1554_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1558_);
v___x_1560_ = v___x_1550_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_snd_1548_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1560_);
v___x_1562_ = v___x_1556_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_del_object(v___x_1556_);
lean_dec(v_snd_1548_);
v_a_1565_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v_a_1554_, 1);
v___x_1566_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v_a_1565_);
lean_ctor_set(v___x_1550_, 0, v___x_1566_);
v___x_1568_ = v___x_1550_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_a_1565_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
size_t v___x_1569_; size_t v___x_1570_; 
v___x_1569_ = ((size_t)1ULL);
v___x_1570_ = lean_usize_add(v_i_1536_, v___x_1569_);
v_i_1536_ = v___x_1570_;
v_b_1537_ = v___x_1568_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_del_object(v___x_1550_);
lean_dec(v_snd_1548_);
v_a_1574_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1553_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1553_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1584_, lean_object* v_as_1585_, lean_object* v_sz_1586_, lean_object* v_i_1587_, lean_object* v_b_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
size_t v_sz_boxed_1597_; size_t v_i_boxed_1598_; lean_object* v_res_1599_; 
v_sz_boxed_1597_ = lean_unbox_usize(v_sz_1586_);
lean_dec(v_sz_1586_);
v_i_boxed_1598_ = lean_unbox_usize(v_i_1587_);
lean_dec(v_i_1587_);
v_res_1599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1_spec__2(v_init_1584_, v_as_1585_, v_sz_boxed_1597_, v_i_boxed_1598_, v_b_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v_as_1585_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1___boxed(lean_object* v_init_1600_, lean_object* v_n_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1600_, v_n_1601_, v_b_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v_n_1601_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(lean_object* v_as_1612_, size_t v_sz_1613_, size_t v_i_1614_, lean_object* v_b_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_usize_dec_lt(v_i_1614_, v_sz_1613_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_b_1615_);
return v___x_1625_;
}
else
{
lean_object* v_snd_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1684_; 
v_snd_1626_ = lean_ctor_get(v_b_1615_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_b_1615_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_b_1615_, 0);
lean_dec(v_unused_1685_);
v___x_1628_ = v_b_1615_;
v_isShared_1629_ = v_isSharedCheck_1684_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_snd_1626_);
lean_dec(v_b_1615_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1684_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v_a_1632_; lean_object* v_a_1639_; 
v___x_1630_ = lean_box(0);
v_a_1639_ = lean_array_uget_borrowed(v_as_1612_, v_i_1614_);
if (lean_obj_tag(v_a_1639_) == 0)
{
v_a_1632_ = v_snd_1626_;
goto v___jp_1631_;
}
else
{
lean_object* v_val_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
lean_dec(v_snd_1626_);
v_val_1640_ = lean_ctor_get(v_a_1639_, 0);
v___x_1641_ = lean_box(0);
v___x_1642_ = l_Lean_LocalDecl_isAuxDecl(v_val_1640_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_LocalDecl_value_x3f(v_val_1640_, v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 1)
{
lean_object* v_val_1644_; lean_object* v___x_1645_; 
v_val_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_val_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1644_, v___y_1620_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1646_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_dec_ref_known(v___x_1647_, 1);
v_a_1632_ = v___x_1641_;
goto v___jp_1631_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_del_object(v___x_1628_);
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_del_object(v___x_1628_);
v_a_1656_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1645_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1645_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1643_);
v___x_1664_ = l_Lean_LocalDecl_type(v_val_1640_);
v___x_1665_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1664_, v___y_1620_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1666_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_dec_ref_known(v___x_1667_, 1);
v_a_1632_ = v___x_1641_;
goto v___jp_1631_;
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1628_);
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
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
lean_del_object(v___x_1628_);
v_a_1676_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1665_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1665_);
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
}
else
{
v_a_1632_ = v___x_1641_;
goto v___jp_1631_;
}
}
v___jp_1631_:
{
lean_object* v___x_1634_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 1, v_a_1632_);
lean_ctor_set(v___x_1628_, 0, v___x_1630_);
v___x_1634_ = v___x_1628_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_a_1632_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
size_t v___x_1635_; size_t v___x_1636_; 
v___x_1635_ = ((size_t)1ULL);
v___x_1636_ = lean_usize_add(v_i_1614_, v___x_1635_);
v_i_1614_ = v___x_1636_;
v_b_1615_ = v___x_1634_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1686_, lean_object* v_sz_1687_, lean_object* v_i_1688_, lean_object* v_b_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
size_t v_sz_boxed_1698_; size_t v_i_boxed_1699_; lean_object* v_res_1700_; 
v_sz_boxed_1698_ = lean_unbox_usize(v_sz_1687_);
lean_dec(v_sz_1687_);
v_i_boxed_1699_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1686_, v_sz_boxed_1698_, v_i_boxed_1699_, v_b_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v_as_1686_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(lean_object* v_as_1701_, size_t v_sz_1702_, size_t v_i_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_lt(v_i_1703_, v_sz_1702_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_b_1704_);
return v___x_1714_;
}
else
{
lean_object* v_snd_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1773_; 
v_snd_1715_ = lean_ctor_get(v_b_1704_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_b_1704_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v_b_1704_, 0);
lean_dec(v_unused_1774_);
v___x_1717_ = v_b_1704_;
v_isShared_1718_ = v_isSharedCheck_1773_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_snd_1715_);
lean_dec(v_b_1704_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1773_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v_a_1721_; lean_object* v_a_1728_; 
v___x_1719_ = lean_box(0);
v_a_1728_ = lean_array_uget_borrowed(v_as_1701_, v_i_1703_);
if (lean_obj_tag(v_a_1728_) == 0)
{
v_a_1721_ = v_snd_1715_;
goto v___jp_1720_;
}
else
{
lean_object* v_val_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
lean_dec(v_snd_1715_);
v_val_1729_ = lean_ctor_get(v_a_1728_, 0);
v___x_1730_ = lean_box(0);
v___x_1731_ = l_Lean_LocalDecl_isAuxDecl(v_val_1729_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_LocalDecl_value_x3f(v_val_1729_, v___x_1731_);
if (lean_obj_tag(v___x_1732_) == 1)
{
lean_object* v_val_1733_; lean_object* v___x_1734_; 
v_val_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_val_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_val_1733_, v___y_1709_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1735_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_dec_ref_known(v___x_1736_, 1);
v_a_1721_ = v___x_1730_;
goto v___jp_1720_;
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_del_object(v___x_1717_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
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
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_del_object(v___x_1717_);
v_a_1745_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1734_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1734_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v___x_1732_);
v___x_1753_ = l_Lean_LocalDecl_type(v_val_1729_);
v___x_1754_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v___x_1753_, v___y_1709_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1755_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_dec_ref_known(v___x_1756_, 1);
v_a_1721_ = v___x_1730_;
goto v___jp_1720_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_del_object(v___x_1717_);
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_del_object(v___x_1717_);
v_a_1765_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1754_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1754_);
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
else
{
v_a_1721_ = v___x_1730_;
goto v___jp_1720_;
}
}
v___jp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v_a_1721_);
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1723_ = v___x_1717_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_a_1721_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = ((size_t)1ULL);
v___x_1725_ = lean_usize_add(v_i_1703_, v___x_1724_);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2_spec__5(v_as_1701_, v_sz_1702_, v___x_1725_, v___x_1723_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2___boxed(lean_object* v_as_1775_, lean_object* v_sz_1776_, lean_object* v_i_1777_, lean_object* v_b_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
size_t v_sz_boxed_1787_; size_t v_i_boxed_1788_; lean_object* v_res_1789_; 
v_sz_boxed_1787_ = lean_unbox_usize(v_sz_1776_);
lean_dec(v_sz_1776_);
v_i_boxed_1788_ = lean_unbox_usize(v_i_1777_);
lean_dec(v_i_1777_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_as_1775_, v_sz_boxed_1787_, v_i_boxed_1788_, v_b_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v_as_1775_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(lean_object* v_t_1790_, lean_object* v_init_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_root_1800_; lean_object* v_tail_1801_; lean_object* v___x_1802_; 
v_root_1800_ = lean_ctor_get(v_t_1790_, 0);
v_tail_1801_ = lean_ctor_get(v_t_1790_, 1);
v___x_1802_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__1(v_init_1791_, v_root_1800_, v_init_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1839_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1839_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1839_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
if (lean_obj_tag(v_a_1803_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; 
v_a_1807_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v_a_1803_, 1);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v_a_1807_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; size_t v_sz_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
lean_del_object(v___x_1805_);
v_a_1811_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v_a_1803_, 1);
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v_a_1811_);
v_sz_1814_ = lean_array_size(v_tail_1801_);
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1_spec__2(v_tail_1801_, v_sz_1814_, v___x_1815_, v___x_1813_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1830_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1830_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1830_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_fst_1821_; 
v_fst_1821_ = lean_ctor_get(v_a_1817_, 0);
if (lean_obj_tag(v_fst_1821_) == 0)
{
lean_object* v_snd_1822_; lean_object* v___x_1824_; 
v_snd_1822_ = lean_ctor_get(v_a_1817_, 1);
lean_inc(v_snd_1822_);
lean_dec(v_a_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v_snd_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_snd_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
else
{
lean_object* v_val_1826_; lean_object* v___x_1828_; 
lean_inc_ref(v_fst_1821_);
lean_dec(v_a_1817_);
v_val_1826_ = lean_ctor_get(v_fst_1821_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v_fst_1821_, 1);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v_val_1826_);
v___x_1828_ = v___x_1819_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_val_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
v_a_1831_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1816_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1816_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1802_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1802_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1___boxed(lean_object* v_t_1848_, lean_object* v_init_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_t_1848_, v_init_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v_t_1848_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(lean_object* v_mvarId_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_lctx_1868_; lean_object* v_decls_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_lctx_1868_ = lean_ctor_get(v_a_1863_, 2);
v_decls_1869_ = lean_ctor_get(v_lctx_1868_, 1);
v___x_1870_ = lean_box(0);
v___x_1871_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__1(v_decls_1869_, v___x_1870_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref_known(v___x_1871_, 1);
v___x_1872_ = l_Lean_MVarId_getType(v_mvarId_1859_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go_spec__0___redArg(v_a_1873_, v_a_1864_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___x_1876_ = l_Lean_Meta_FunInd_Collector_visit(v_a_1875_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
return v___x_1876_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1874_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1874_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_a_1885_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1872_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1872_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_dec(v_mvarId_1859_);
return v___x_1871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go___boxed(lean_object* v_mvarId_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(lean_object* v_mvarId_1903_, lean_object* v_x_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1903_, v_x_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1910_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1910_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg___boxed(lean_object* v_mvarId_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1927_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(lean_object* v_00_u03b1_1935_, lean_object* v_mvarId_1936_, lean_object* v_x_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1936_, v_x_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_mvarId_1945_, lean_object* v_x_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0(v_00_u03b1_1944_, v_mvarId_1945_, v_x_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0(lean_object* v___x_1953_, lean_object* v___x_1954_, lean_object* v_mvarId_1955_, lean_object* v_needle_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_st_mk_ref(v___x_1953_);
v___x_1963_ = lean_st_mk_ref(v___x_1954_);
v___x_1964_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_Collector_main_go(v_mvarId_1955_, v___x_1963_, v_needle_1956_, v___x_1962_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1974_; 
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1964_, 0);
lean_dec(v_unused_1975_);
v___x_1966_ = v___x_1964_;
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___x_1964_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_calls_1970_; lean_object* v___x_1972_; 
v___x_1968_ = lean_st_ref_get(v___x_1963_);
lean_dec(v___x_1963_);
lean_dec(v___x_1968_);
v___x_1969_ = lean_st_ref_get(v___x_1962_);
lean_dec(v___x_1962_);
v_calls_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc_ref(v_calls_1970_);
lean_dec(v___x_1969_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_calls_1970_);
v___x_1972_ = v___x_1966_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_calls_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec(v___x_1963_);
lean_dec(v___x_1962_);
v_a_1976_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1964_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1964_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___lam__0___boxed(lean_object* v___x_1984_, lean_object* v___x_1985_, lean_object* v_mvarId_1986_, lean_object* v_needle_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Meta_FunInd_Collector_main___lam__0(v___x_1984_, v___x_1985_, v_mvarId_1986_, v_needle_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v_needle_1987_);
return v_res_1993_;
}
}
static lean_object* _init_l_Lean_Meta_FunInd_Collector_main___closed__0(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(64u);
v___x_1995_ = l_Lean_mkPtrSet___redArg(v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main(lean_object* v_needle_1996_, lean_object* v_mvarId_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; 
v___x_2003_ = lean_obj_once(&l_Lean_Meta_FunInd_Collector_main___closed__0, &l_Lean_Meta_FunInd_Collector_main___closed__0_once, _init_l_Lean_Meta_FunInd_Collector_main___closed__0);
v___x_2004_ = lean_obj_once(&l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4, &l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4_once, _init_l_Lean_Meta_FunInd_instEmptyCollectionSeenCalls___closed__4);
lean_inc(v_mvarId_1997_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lean_Meta_FunInd_Collector_main___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2005_, 0, v___x_2004_);
lean_closure_set(v___f_2005_, 1, v___x_2003_);
lean_closure_set(v___f_2005_, 2, v_mvarId_1997_);
lean_closure_set(v___f_2005_, 3, v_needle_1996_);
v___x_2006_ = l_Lean_MVarId_withContext___at___00Lean_Meta_FunInd_Collector_main_spec__0___redArg(v_mvarId_1997_, v___f_2005_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_Collector_main___boxed(lean_object* v_needle_2007_, lean_object* v_mvarId_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Meta_FunInd_Collector_main(v_needle_2007_, v_mvarId_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(lean_object* v_needle_2015_, lean_object* v_mvarId_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Meta_FunInd_Collector_main(v_needle_2015_, v_mvarId_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1___boxed(lean_object* v_needle_2023_, lean_object* v_mvarId_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Lean_Meta_Tactic_FunIndCollect_0__Lean_Meta_FunInd_collect_unsafe__1(v_needle_2023_, v_mvarId_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect(lean_object* v_needle_2031_, lean_object* v_mvarId_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Meta_FunInd_Collector_main(v_needle_2031_, v_mvarId_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInd_collect___boxed(lean_object* v_needle_2039_, lean_object* v_mvarId_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_Meta_FunInd_collect(v_needle_2039_, v_mvarId_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2046_;
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
