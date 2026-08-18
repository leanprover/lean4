// Lean compiler output
// Module: Lean.Server.Completion.CompletionInfoSelection
// Imports: public import Lean.Server.Completion.SyntheticCompletion
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_eqWithInfo(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Info_size_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_pos_x3f(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_findSyntheticCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__0;
static lean_once_cell_t l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__1;
static lean_once_cell_t l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_val_7_; uint8_t v___x_8_; 
v_val_6_ = lean_ctor_get(v_x_1_, 0);
v_val_7_ = lean_ctor_get(v_x_2_, 0);
v___x_8_ = lean_name_eq(v_val_6_, v_val_7_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_x_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
switch(lean_obj_tag(v_a_13_))
{
case 0:
{
if (lean_obj_tag(v_a_14_) == 0)
{
lean_object* v_termInfo_15_; lean_object* v_toElabInfo_16_; lean_object* v_termInfo_17_; lean_object* v_toElabInfo_18_; lean_object* v_expr_19_; lean_object* v_stx_20_; lean_object* v_expr_21_; lean_object* v_stx_22_; uint8_t v___x_23_; 
v_termInfo_15_ = lean_ctor_get(v_a_13_, 0);
lean_inc_ref(v_termInfo_15_);
lean_dec_ref_known(v_a_13_, 2);
v_toElabInfo_16_ = lean_ctor_get(v_termInfo_15_, 0);
lean_inc_ref(v_toElabInfo_16_);
v_termInfo_17_ = lean_ctor_get(v_a_14_, 0);
lean_inc_ref(v_termInfo_17_);
lean_dec_ref_known(v_a_14_, 2);
v_toElabInfo_18_ = lean_ctor_get(v_termInfo_17_, 0);
lean_inc_ref(v_toElabInfo_18_);
v_expr_19_ = lean_ctor_get(v_termInfo_15_, 3);
lean_inc_ref(v_expr_19_);
lean_dec_ref(v_termInfo_15_);
v_stx_20_ = lean_ctor_get(v_toElabInfo_16_, 1);
lean_inc(v_stx_20_);
lean_dec_ref(v_toElabInfo_16_);
v_expr_21_ = lean_ctor_get(v_termInfo_17_, 3);
lean_inc_ref(v_expr_21_);
lean_dec_ref(v_termInfo_17_);
v_stx_22_ = lean_ctor_get(v_toElabInfo_18_, 1);
lean_inc(v_stx_22_);
lean_dec_ref(v_toElabInfo_18_);
v___x_23_ = l_Lean_Syntax_eqWithInfo(v_stx_20_, v_stx_22_);
if (v___x_23_ == 0)
{
lean_dec_ref(v_expr_21_);
lean_dec_ref(v_expr_19_);
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_expr_eqv(v_expr_19_, v_expr_21_);
lean_dec_ref(v_expr_21_);
lean_dec_ref(v_expr_19_);
return v___x_24_;
}
}
else
{
uint8_t v___x_25_; 
lean_dec_ref_known(v_a_13_, 2);
lean_dec_ref(v_a_14_);
v___x_25_ = 0;
return v___x_25_;
}
}
case 3:
{
if (lean_obj_tag(v_a_14_) == 3)
{
lean_object* v_stx_26_; lean_object* v_id_27_; lean_object* v_structName_28_; lean_object* v_stx_29_; lean_object* v_id_30_; lean_object* v_structName_31_; uint8_t v___y_33_; uint8_t v___x_35_; 
v_stx_26_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_26_);
v_id_27_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_id_27_);
v_structName_28_ = lean_ctor_get(v_a_13_, 3);
lean_inc(v_structName_28_);
lean_dec_ref_known(v_a_13_, 4);
v_stx_29_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_29_);
v_id_30_ = lean_ctor_get(v_a_14_, 1);
lean_inc(v_id_30_);
v_structName_31_ = lean_ctor_get(v_a_14_, 3);
lean_inc(v_structName_31_);
lean_dec_ref_known(v_a_14_, 4);
v___x_35_ = l_Lean_Syntax_eqWithInfo(v_stx_26_, v_stx_29_);
if (v___x_35_ == 0)
{
lean_dec(v_id_30_);
lean_dec(v_id_27_);
v___y_33_ = v___x_35_;
goto v___jp_32_;
}
else
{
uint8_t v___x_36_; 
v___x_36_ = l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_id_27_, v_id_30_);
lean_dec(v_id_30_);
lean_dec(v_id_27_);
v___y_33_ = v___x_36_;
goto v___jp_32_;
}
v___jp_32_:
{
if (v___y_33_ == 0)
{
lean_dec(v_structName_31_);
lean_dec(v_structName_28_);
return v___y_33_;
}
else
{
uint8_t v___x_34_; 
v___x_34_ = lean_name_eq(v_structName_28_, v_structName_31_);
lean_dec(v_structName_31_);
lean_dec(v_structName_28_);
return v___x_34_;
}
}
}
else
{
uint8_t v___x_37_; 
lean_dec_ref_known(v_a_13_, 4);
lean_dec_ref(v_a_14_);
v___x_37_ = 0;
return v___x_37_;
}
}
case 4:
{
if (lean_obj_tag(v_a_14_) == 4)
{
lean_object* v_stx_38_; lean_object* v_stx_39_; uint8_t v___x_40_; 
v_stx_38_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_38_);
lean_dec_ref_known(v_a_13_, 1);
v_stx_39_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_39_);
lean_dec_ref_known(v_a_14_, 1);
v___x_40_ = l_Lean_Syntax_eqWithInfo(v_stx_38_, v_stx_39_);
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
lean_dec_ref_known(v_a_13_, 1);
lean_dec_ref(v_a_14_);
v___x_41_ = 0;
return v___x_41_;
}
}
case 5:
{
if (lean_obj_tag(v_a_14_) == 5)
{
lean_object* v_stx_42_; lean_object* v_stx_43_; uint8_t v___x_44_; 
v_stx_42_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_42_);
lean_dec_ref_known(v_a_13_, 1);
v_stx_43_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_43_);
lean_dec_ref_known(v_a_14_, 1);
v___x_44_ = l_Lean_Syntax_eqWithInfo(v_stx_42_, v_stx_43_);
return v___x_44_;
}
else
{
uint8_t v___x_45_; 
lean_dec_ref_known(v_a_13_, 1);
lean_dec_ref(v_a_14_);
v___x_45_ = 0;
return v___x_45_;
}
}
case 6:
{
if (lean_obj_tag(v_a_14_) == 6)
{
lean_object* v_stx_46_; lean_object* v_stx_47_; uint8_t v___x_48_; 
v_stx_46_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_46_);
lean_dec_ref_known(v_a_13_, 2);
v_stx_47_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_47_);
lean_dec_ref_known(v_a_14_, 2);
v___x_48_ = l_Lean_Syntax_eqWithInfo(v_stx_46_, v_stx_47_);
return v___x_48_;
}
else
{
uint8_t v___x_49_; 
lean_dec_ref_known(v_a_13_, 2);
lean_dec_ref(v_a_14_);
v___x_49_ = 0;
return v___x_49_;
}
}
case 7:
{
if (lean_obj_tag(v_a_14_) == 7)
{
lean_object* v_stx_50_; lean_object* v_stx_51_; uint8_t v___x_52_; 
v_stx_50_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_50_);
lean_dec_ref_known(v_a_13_, 3);
v_stx_51_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_51_);
lean_dec_ref_known(v_a_14_, 3);
v___x_52_ = l_Lean_Syntax_eqWithInfo(v_stx_50_, v_stx_51_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
lean_dec_ref_known(v_a_13_, 3);
lean_dec_ref(v_a_14_);
v___x_53_ = 0;
return v___x_53_;
}
}
case 8:
{
if (lean_obj_tag(v_a_14_) == 8)
{
lean_object* v_stx_54_; lean_object* v_stx_55_; uint8_t v___x_56_; 
v_stx_54_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_54_);
lean_dec_ref_known(v_a_13_, 1);
v_stx_55_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_55_);
lean_dec_ref_known(v_a_14_, 1);
v___x_56_ = l_Lean_Syntax_eqWithInfo(v_stx_54_, v_stx_55_);
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
lean_dec_ref_known(v_a_13_, 1);
lean_dec_ref(v_a_14_);
v___x_57_ = 0;
return v___x_57_;
}
}
default: 
{
if (lean_obj_tag(v_a_14_) == 1)
{
lean_object* v_stx_58_; lean_object* v_id_59_; lean_object* v_stx_60_; lean_object* v_id_61_; uint8_t v___x_62_; 
v_stx_58_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_58_);
v_id_59_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_id_59_);
lean_dec_ref(v_a_13_);
v_stx_60_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_60_);
v_id_61_ = lean_ctor_get(v_a_14_, 1);
lean_inc(v_id_61_);
lean_dec_ref_known(v_a_14_, 4);
v___x_62_ = l_Lean_Syntax_eqWithInfo(v_stx_58_, v_stx_60_);
if (v___x_62_ == 0)
{
lean_dec(v_id_61_);
lean_dec(v_id_59_);
return v___x_62_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = lean_name_eq(v_id_59_, v_id_61_);
lean_dec(v_id_61_);
lean_dec(v_id_59_);
return v___x_63_;
}
}
else
{
uint8_t v___x_64_; 
lean_dec_ref(v_a_14_);
lean_dec_ref(v_a_13_);
v___x_64_ = 0;
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq___boxed(lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_a_65_, v_a_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(lean_object* v_a_69_, lean_object* v_as_70_, size_t v_i_71_, size_t v_stop_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_eq(v_i_71_, v_stop_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v_info_75_; lean_object* v_info_76_; uint8_t v___x_77_; 
v___x_74_ = lean_array_uget_borrowed(v_as_70_, v_i_71_);
v_info_75_ = lean_ctor_get(v___x_74_, 2);
v_info_76_ = lean_ctor_get(v_a_69_, 2);
lean_inc_ref(v_info_76_);
lean_inc_ref(v_info_75_);
v___x_77_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_info_75_, v_info_76_);
if (v___x_77_ == 0)
{
size_t v___x_78_; size_t v___x_79_; 
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_add(v_i_71_, v___x_78_);
v_i_71_ = v___x_79_;
goto _start;
}
else
{
lean_dec_ref(v_a_69_);
return v___x_77_;
}
}
else
{
uint8_t v___x_81_; 
lean_dec_ref(v_a_69_);
v___x_81_ = 0;
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0___boxed(lean_object* v_a_82_, lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_){
_start:
{
size_t v_i_boxed_86_; size_t v_stop_boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_i_boxed_86_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_87_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_82_, v_as_83_, v_i_boxed_86_, v_stop_boxed_87_);
lean_dec_ref(v_as_83_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(lean_object* v_as_90_, size_t v_sz_91_, size_t v_i_92_, lean_object* v_b_93_){
_start:
{
lean_object* v_a_95_; uint8_t v___x_99_; 
v___x_99_ = lean_usize_dec_lt(v_i_92_, v_sz_91_);
if (v___x_99_ == 0)
{
return v_b_93_;
}
else
{
lean_object* v_a_100_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_a_100_ = lean_array_uget_borrowed(v_as_90_, v_i_92_);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_array_get_size(v_b_93_);
v___x_105_ = lean_nat_dec_lt(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
goto v___jp_101_;
}
else
{
if (v___x_105_ == 0)
{
goto v___jp_101_;
}
else
{
size_t v___x_106_; size_t v___x_107_; uint8_t v___x_108_; 
v___x_106_ = ((size_t)0ULL);
v___x_107_ = lean_usize_of_nat(v___x_104_);
lean_inc(v_a_100_);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_100_, v_b_93_, v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
goto v___jp_101_;
}
else
{
v_a_95_ = v_b_93_;
goto v___jp_94_;
}
}
}
v___jp_101_:
{
lean_object* v___x_102_; 
lean_inc(v_a_100_);
v___x_102_ = lean_array_push(v_b_93_, v_a_100_);
v_a_95_ = v___x_102_;
goto v___jp_94_;
}
}
v___jp_94_:
{
size_t v___x_96_; size_t v___x_97_; 
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_add(v_i_92_, v___x_96_);
v_i_92_ = v___x_97_;
v_b_93_ = v_a_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1___boxed(lean_object* v_as_109_, lean_object* v_sz_110_, lean_object* v_i_111_, lean_object* v_b_112_){
_start:
{
size_t v_sz_boxed_113_; size_t v_i_boxed_114_; lean_object* v_res_115_; 
v_sz_boxed_113_ = lean_unbox_usize(v_sz_110_);
lean_dec(v_sz_110_);
v_i_boxed_114_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_as_109_, v_sz_boxed_113_, v_i_boxed_114_, v_b_112_);
lean_dec_ref(v_as_109_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(lean_object* v_infos_118_){
_start:
{
lean_object* v_deduplicatedInfos_119_; size_t v_sz_120_; size_t v___x_121_; lean_object* v___x_122_; 
v_deduplicatedInfos_119_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
v_sz_120_ = lean_array_size(v_infos_118_);
v___x_121_ = ((size_t)0ULL);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_infos_118_, v_sz_120_, v___x_121_, v_deduplicatedInfos_119_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___boxed(lean_object* v_infos_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_infos_123_);
lean_dec_ref(v_infos_123_);
return v_res_124_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(lean_object* v_hoverPos_125_, lean_object* v_i_126_){
_start:
{
if (lean_obj_tag(v_i_126_) == 5)
{
lean_object* v_stx_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_stx_139_ = lean_ctor_get(v_i_126_, 0);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = l_Lean_Syntax_getArg(v_stx_139_, v___x_140_);
v___x_142_ = l_Lean_Syntax_isMissing(v___x_141_);
lean_dec(v___x_141_);
if (v___x_142_ == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v___x_143_; 
lean_inc(v_stx_139_);
lean_dec_ref_known(v_i_126_, 1);
v___x_143_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_139_, v___x_142_);
lean_dec(v_stx_139_);
if (lean_obj_tag(v___x_143_) == 1)
{
lean_object* v_val_144_; uint8_t v___x_145_; uint8_t v___x_146_; 
v_val_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___x_143_, 1);
v___x_145_ = 0;
v___x_146_ = l_Lean_Syntax_Range_contains(v_val_144_, v_hoverPos_125_, v___x_145_);
lean_dec(v_val_144_);
return v___x_146_;
}
else
{
uint8_t v___x_147_; 
lean_dec(v___x_143_);
v___x_147_ = 0;
return v___x_147_;
}
}
}
else
{
goto v___jp_130_;
}
v___jp_127_:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_128_, 0, v_i_126_);
v___x_129_ = l_Lean_Elab_Info_occursInOrOnBoundary(v___x_128_, v_hoverPos_125_);
lean_dec_ref_known(v___x_128_, 1);
return v___x_129_;
}
v___jp_130_:
{
if (lean_obj_tag(v_i_126_) == 7)
{
lean_object* v_id_x3f_131_; 
v_id_x3f_131_ = lean_ctor_get(v_i_126_, 1);
if (lean_obj_tag(v_id_x3f_131_) == 0)
{
lean_object* v_stx_132_; uint8_t v___x_133_; lean_object* v___x_134_; 
v_stx_132_ = lean_ctor_get(v_i_126_, 0);
lean_inc(v_stx_132_);
lean_dec_ref_known(v_i_126_, 3);
v___x_133_ = 1;
v___x_134_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_132_, v___x_133_);
lean_dec(v_stx_132_);
if (lean_obj_tag(v___x_134_) == 1)
{
lean_object* v_val_135_; uint8_t v___x_136_; uint8_t v___x_137_; 
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v___x_134_, 1);
v___x_136_ = 0;
v___x_137_ = l_Lean_Syntax_Range_contains(v_val_135_, v_hoverPos_125_, v___x_136_);
lean_dec(v_val_135_);
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
lean_dec(v___x_134_);
v___x_138_ = 0;
return v___x_138_;
}
}
else
{
goto v___jp_127_;
}
}
else
{
goto v___jp_127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos___boxed(lean_object* v_hoverPos_148_, lean_object* v_i_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_148_, v_i_149_);
lean_dec(v_hoverPos_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(lean_object* v_msg_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_panic_fn_borrowed(v___x_153_, v_msg_152_);
return v___x_154_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2));
v___x_159_ = lean_unsigned_to_nat(14u);
v___x_160_ = lean_unsigned_to_nat(22u);
v___x_161_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1));
v___x_162_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0));
v___x_163_ = l_mkPanicMessageWithDecl(v___x_162_, v___x_161_, v___x_160_, v___x_159_, v___x_158_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(lean_object* v_fileMap_164_, lean_object* v_hoverPos_165_, lean_object* v_hoverLine_166_, lean_object* v_ctx_167_, lean_object* v_info_168_, lean_object* v_best_169_){
_start:
{
if (lean_obj_tag(v_info_168_) == 8)
{
lean_object* v_i_170_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; uint8_t v___x_178_; lean_object* v___y_180_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_196_; 
v_i_170_ = lean_ctor_get(v_info_168_, 0);
lean_inc_ref_n(v_i_170_, 2);
v___x_178_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_165_, v_i_170_);
if (v___x_178_ == 0)
{
lean_dec_ref_known(v_info_168_, 1);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
lean_dec_ref(v_fileMap_164_);
return v_best_169_;
}
else
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Elab_Info_pos_x3f(v_info_168_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_203_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_202_);
v___y_196_ = v___x_203_;
goto v___jp_195_;
}
else
{
lean_object* v_val_204_; 
v_val_204_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v___x_201_, 1);
v___y_196_ = v_val_204_;
goto v___jp_195_;
}
}
v___jp_171_:
{
uint8_t v___x_175_; 
v___x_175_ = lean_nat_dec_eq(v___y_172_, v___y_174_);
lean_dec(v___y_174_);
lean_dec(v___y_172_);
if (v___x_175_ == 0)
{
lean_dec(v___y_173_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
return v_best_169_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v___y_173_);
lean_ctor_set(v___x_176_, 1, v_ctx_167_);
lean_ctor_set(v___x_176_, 2, v_i_170_);
v___x_177_ = lean_array_push(v_best_169_, v___x_176_);
return v___x_177_;
}
}
v___jp_179_:
{
lean_object* v___x_183_; lean_object* v_line_184_; lean_object* v___x_185_; lean_object* v_line_186_; uint8_t v___x_187_; 
lean_inc_ref(v_fileMap_164_);
v___x_183_ = l_Lean_FileMap_toPosition(v_fileMap_164_, v___y_180_);
lean_dec(v___y_180_);
v_line_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_line_184_);
lean_dec_ref(v___x_183_);
v___x_185_ = l_Lean_FileMap_toPosition(v_fileMap_164_, v___y_181_);
lean_dec(v___y_181_);
v_line_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_line_186_);
lean_dec_ref(v___x_185_);
v___x_187_ = lean_nat_dec_eq(v_line_184_, v_hoverLine_166_);
if (v___x_187_ == 0)
{
if (v___x_178_ == 0)
{
v___y_172_ = v_line_184_;
v___y_173_ = v___y_182_;
v___y_174_ = v_line_186_;
goto v___jp_171_;
}
else
{
lean_dec(v_line_186_);
lean_dec(v_line_184_);
lean_dec(v___y_182_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
return v_best_169_;
}
}
else
{
v___y_172_ = v_line_184_;
v___y_173_ = v___y_182_;
v___y_174_ = v_line_186_;
goto v___jp_171_;
}
}
v___jp_188_:
{
uint8_t v___x_191_; 
v___x_191_ = lean_nat_dec_lt(v_hoverPos_165_, v___y_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
v___y_180_ = v___y_189_;
v___y_181_ = v___y_190_;
v___y_182_ = v___x_192_;
goto v___jp_179_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_nat_sub(v_hoverPos_165_, v___y_189_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
v___y_180_ = v___y_189_;
v___y_181_ = v___y_190_;
v___y_182_ = v___x_194_;
goto v___jp_179_;
}
}
v___jp_195_:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Elab_Info_tailPos_x3f(v_info_168_);
lean_dec_ref_known(v_info_168_, 1);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_199_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_198_);
v___y_189_ = v___y_196_;
v___y_190_ = v___x_199_;
goto v___jp_188_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v___x_197_, 1);
v___y_189_ = v___y_196_;
v___y_190_ = v_val_200_;
goto v___jp_188_;
}
}
}
else
{
lean_dec_ref(v_info_168_);
lean_dec_ref(v_ctx_167_);
lean_dec_ref(v_fileMap_164_);
return v_best_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed(lean_object* v_fileMap_205_, lean_object* v_hoverPos_206_, lean_object* v_hoverLine_207_, lean_object* v_ctx_208_, lean_object* v_info_209_, lean_object* v_best_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(v_fileMap_205_, v_hoverPos_206_, v_hoverLine_207_, v_ctx_208_, v_info_209_, v_best_210_);
lean_dec(v_hoverLine_207_);
lean_dec(v_hoverPos_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object* v_fileMap_212_, lean_object* v_hoverPos_213_, lean_object* v_cmdStx_214_, lean_object* v_infoTree_215_){
_start:
{
uint8_t v_isComplete_217_; lean_object* v_completionInfoCandidates_218_; lean_object* v___x_222_; lean_object* v_line_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_completionInfoCandidates_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
lean_inc_ref_n(v_fileMap_212_, 2);
v___x_222_ = l_Lean_FileMap_toPosition(v_fileMap_212_, v_hoverPos_213_);
v_line_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_line_223_);
lean_dec_ref(v___x_222_);
lean_inc(v_hoverPos_213_);
v___x_224_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed), 6, 3);
lean_closure_set(v___x_224_, 0, v_fileMap_212_);
lean_closure_set(v___x_224_, 1, v_hoverPos_213_);
lean_closure_set(v___x_224_, 2, v_line_223_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
lean_inc_ref(v_infoTree_215_);
v_completionInfoCandidates_227_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___x_224_, v___x_226_, v_infoTree_215_);
v___x_228_ = lean_array_get_size(v_completionInfoCandidates_227_);
v___x_229_ = lean_nat_dec_eq(v___x_228_, v___x_225_);
if (v___x_229_ == 0)
{
uint8_t v_isComplete_230_; 
lean_dec_ref(v_infoTree_215_);
lean_dec(v_cmdStx_214_);
lean_dec(v_hoverPos_213_);
lean_dec_ref(v_fileMap_212_);
v_isComplete_230_ = 1;
v_isComplete_217_ = v_isComplete_230_;
v_completionInfoCandidates_218_ = v_completionInfoCandidates_227_;
goto v___jp_216_;
}
else
{
lean_object* v_completionInfoCandidates_231_; uint8_t v_isComplete_232_; 
lean_dec(v_completionInfoCandidates_227_);
v_completionInfoCandidates_231_ = l_Lean_Server_Completion_findSyntheticCompletions(v_fileMap_212_, v_hoverPos_213_, v_cmdStx_214_, v_infoTree_215_);
v_isComplete_232_ = 0;
v_isComplete_217_ = v_isComplete_232_;
v_completionInfoCandidates_218_ = v_completionInfoCandidates_231_;
goto v___jp_216_;
}
v___jp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_completionInfoCandidates_218_);
lean_dec_ref(v_completionInfoCandidates_218_);
v___x_220_ = lean_box(v_isComplete_217_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(lean_object* v_x_233_){
_start:
{
lean_object* v_fst_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_249_; 
v_fst_234_ = lean_ctor_get(v_x_233_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_233_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v_x_233_, 1);
lean_dec(v_unused_250_);
v___x_236_ = v_x_233_;
v_isShared_237_ = v_isSharedCheck_249_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_fst_234_);
lean_dec(v_x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_249_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_info_238_; uint8_t v___y_240_; 
v_info_238_ = lean_ctor_get(v_fst_234_, 2);
lean_inc_ref(v_info_238_);
lean_dec(v_fst_234_);
if (lean_obj_tag(v_info_238_) == 1)
{
uint8_t v___x_247_; 
v___x_247_ = 1;
v___y_240_ = v___x_247_;
goto v___jp_239_;
}
else
{
uint8_t v___x_248_; 
v___x_248_ = 0;
v___y_240_ = v___x_248_;
goto v___jp_239_;
}
v___jp_239_:
{
lean_object* v___x_241_; lean_object* v_size_x3f_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_241_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_241_, 0, v_info_238_);
v_size_x3f_242_ = l_Lean_Elab_Info_size_x3f(v___x_241_);
lean_dec_ref_known(v___x_241_, 1);
v___x_243_ = lean_box(v___y_240_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_size_x3f_242_);
lean_ctor_set(v___x_236_, 0, v___x_243_);
v___x_245_ = v___x_236_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_size_x3f_242_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0(uint8_t v___x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
lean_object* v_fst_254_; lean_object* v_fst_255_; lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; 
v_fst_254_ = lean_ctor_get(v_x_252_, 0);
v_fst_255_ = lean_ctor_get(v_x_253_, 0);
v_fst_256_ = lean_ctor_get(v_fst_254_, 0);
v_snd_257_ = lean_ctor_get(v_fst_254_, 1);
v_fst_258_ = lean_ctor_get(v_fst_255_, 0);
v_snd_259_ = lean_ctor_get(v_fst_255_, 1);
if (lean_obj_tag(v_snd_257_) == 0)
{
if (lean_obj_tag(v_snd_259_) == 1)
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
else
{
goto v___jp_266_;
}
}
else
{
if (lean_obj_tag(v_snd_259_) == 0)
{
return v___x_251_;
}
else
{
goto v___jp_266_;
}
}
v___jp_260_:
{
if (lean_obj_tag(v_snd_257_) == 1)
{
if (lean_obj_tag(v_snd_259_) == 1)
{
lean_object* v_val_261_; lean_object* v_val_262_; uint8_t v___x_263_; 
v_val_261_ = lean_ctor_get(v_snd_257_, 0);
v_val_262_ = lean_ctor_get(v_snd_259_, 0);
v___x_263_ = lean_nat_dec_lt(v_val_261_, v_val_262_);
return v___x_263_;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = 0;
return v___x_264_;
}
}
else
{
uint8_t v___x_265_; 
v___x_265_ = 0;
return v___x_265_;
}
}
v___jp_266_:
{
uint8_t v___x_267_; 
v___x_267_ = lean_unbox(v_fst_256_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_fst_258_);
if (v___x_268_ == 1)
{
uint8_t v___x_269_; 
v___x_269_ = lean_unbox(v_fst_258_);
return v___x_269_;
}
else
{
goto v___jp_260_;
}
}
else
{
uint8_t v___x_270_; 
v___x_270_ = lean_unbox(v_fst_258_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; 
v___x_271_ = lean_unbox(v_fst_258_);
return v___x_271_;
}
else
{
goto v___jp_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0___boxed(lean_object* v___x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint8_t v___x_2458__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v___x_2458__boxed_276_ = lean_unbox(v___x_273_);
v_res_277_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0(v___x_2458__boxed_276_, v_x_274_, v_x_275_);
lean_dec_ref(v_x_275_);
lean_dec_ref(v_x_274_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___redArg(lean_object* v_hi_279_, lean_object* v_pivot_280_, lean_object* v_as_281_, lean_object* v_i_282_, lean_object* v_k_283_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = lean_nat_dec_lt(v_k_283_, v_hi_279_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_k_283_);
v___x_295_ = lean_array_fswap(v_as_281_, v_i_282_, v_hi_279_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_i_282_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v_fst_298_; lean_object* v_fst_299_; lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v_fst_302_; lean_object* v_snd_303_; 
v___x_297_ = lean_array_fget_borrowed(v_as_281_, v_k_283_);
v_fst_298_ = lean_ctor_get(v___x_297_, 0);
v_fst_299_ = lean_ctor_get(v_pivot_280_, 0);
v_fst_300_ = lean_ctor_get(v_fst_298_, 0);
v_snd_301_ = lean_ctor_get(v_fst_298_, 1);
v_fst_302_ = lean_ctor_get(v_fst_299_, 0);
v_snd_303_ = lean_ctor_get(v_fst_299_, 1);
if (lean_obj_tag(v_snd_301_) == 0)
{
if (lean_obj_tag(v_snd_303_) == 1)
{
goto v___jp_284_;
}
else
{
goto v___jp_308_;
}
}
else
{
if (lean_obj_tag(v_snd_303_) == 0)
{
goto v___jp_288_;
}
else
{
goto v___jp_308_;
}
}
v___jp_304_:
{
if (lean_obj_tag(v_snd_301_) == 1)
{
if (lean_obj_tag(v_snd_303_) == 1)
{
lean_object* v_val_305_; lean_object* v_val_306_; uint8_t v___x_307_; 
v_val_305_ = lean_ctor_get(v_snd_301_, 0);
v_val_306_ = lean_ctor_get(v_snd_303_, 0);
v___x_307_ = lean_nat_dec_lt(v_val_305_, v_val_306_);
if (v___x_307_ == 0)
{
goto v___jp_284_;
}
else
{
goto v___jp_288_;
}
}
else
{
goto v___jp_284_;
}
}
else
{
goto v___jp_284_;
}
}
v___jp_308_:
{
uint8_t v___x_309_; 
v___x_309_ = lean_unbox(v_fst_300_);
if (v___x_309_ == 0)
{
uint8_t v___x_310_; 
v___x_310_ = lean_unbox(v_fst_302_);
if (v___x_310_ == 1)
{
goto v___jp_288_;
}
else
{
goto v___jp_304_;
}
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_unbox(v_fst_302_);
if (v___x_311_ == 0)
{
goto v___jp_284_;
}
else
{
goto v___jp_304_;
}
}
}
}
v___jp_284_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_k_283_, v___x_285_);
lean_dec(v_k_283_);
v_k_283_ = v___x_286_;
goto _start;
}
v___jp_288_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_array_fswap(v_as_281_, v_i_282_, v_k_283_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_i_282_, v___x_290_);
lean_dec(v_i_282_);
v___x_292_ = lean_nat_add(v_k_283_, v___x_290_);
lean_dec(v_k_283_);
v_as_281_ = v___x_289_;
v_i_282_ = v___x_291_;
v_k_283_ = v___x_292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___redArg___boxed(lean_object* v_hi_312_, lean_object* v_pivot_313_, lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_k_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___redArg(v_hi_312_, v_pivot_313_, v_as_314_, v_i_315_, v_k_316_);
lean_dec_ref(v_pivot_313_);
lean_dec(v_hi_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg(lean_object* v_n_318_, lean_object* v_as_319_, lean_object* v_lo_320_, lean_object* v_hi_321_){
_start:
{
lean_object* v___y_323_; uint8_t v___x_333_; 
v___x_333_ = lean_nat_dec_lt(v_lo_320_, v_hi_321_);
if (v___x_333_ == 0)
{
lean_dec(v_lo_320_);
return v_as_319_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_mid_336_; lean_object* v___y_338_; lean_object* v___y_344_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_334_ = lean_nat_add(v_lo_320_, v_hi_321_);
v___x_335_ = lean_unsigned_to_nat(1u);
v_mid_336_ = lean_nat_shiftr(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
v___x_349_ = lean_array_fget_borrowed(v_as_319_, v_mid_336_);
v___x_350_ = lean_array_fget_borrowed(v_as_319_, v_lo_320_);
v___x_351_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0(v___x_333_, v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
v___y_344_ = v_as_319_;
goto v___jp_343_;
}
else
{
lean_object* v___x_352_; 
v___x_352_ = lean_array_fswap(v_as_319_, v_lo_320_, v_mid_336_);
v___y_344_ = v___x_352_;
goto v___jp_343_;
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_array_fget_borrowed(v___y_338_, v_mid_336_);
v___x_340_ = lean_array_fget_borrowed(v___y_338_, v_hi_321_);
v___x_341_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0(v___x_333_, v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec(v_mid_336_);
v___y_323_ = v___y_338_;
goto v___jp_322_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_array_fswap(v___y_338_, v_mid_336_, v_hi_321_);
lean_dec(v_mid_336_);
v___y_323_ = v___x_342_;
goto v___jp_322_;
}
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_array_fget_borrowed(v___y_344_, v_hi_321_);
v___x_346_ = lean_array_fget_borrowed(v___y_344_, v_lo_320_);
v___x_347_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___lam__0(v___x_333_, v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
v___y_338_ = v___y_344_;
goto v___jp_337_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_array_fswap(v___y_344_, v_lo_320_, v_hi_321_);
v___y_338_ = v___x_348_;
goto v___jp_337_;
}
}
}
v___jp_322_:
{
lean_object* v_pivot_324_; lean_object* v___x_325_; lean_object* v_fst_326_; lean_object* v_snd_327_; uint8_t v___x_328_; 
v_pivot_324_ = lean_array_fget(v___y_323_, v_hi_321_);
lean_inc_n(v_lo_320_, 2);
v___x_325_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___redArg(v_hi_321_, v_pivot_324_, v___y_323_, v_lo_320_, v_lo_320_);
lean_dec(v_pivot_324_);
v_fst_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_fst_326_);
v_snd_327_ = lean_ctor_get(v___x_325_, 1);
lean_inc(v_snd_327_);
lean_dec_ref(v___x_325_);
v___x_328_ = lean_nat_dec_le(v_hi_321_, v_fst_326_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg(v_n_318_, v_snd_327_, v_lo_320_, v_fst_326_);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_fst_326_, v___x_330_);
lean_dec(v_fst_326_);
v_as_319_ = v___x_329_;
v_lo_320_ = v___x_331_;
goto _start;
}
else
{
lean_dec(v_fst_326_);
lean_dec(v_lo_320_);
return v_snd_327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg___boxed(lean_object* v_n_353_, lean_object* v_as_354_, lean_object* v_lo_355_, lean_object* v_hi_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg(v_n_353_, v_as_354_, v_lo_355_, v_hi_356_);
lean_dec(v_hi_356_);
lean_dec(v_n_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_361_ == 0)
{
return v_bs_360_;
}
else
{
lean_object* v_v_362_; lean_object* v_snd_363_; lean_object* v___x_364_; lean_object* v_bs_x27_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v_v_362_ = lean_array_uget_borrowed(v_bs_360_, v_i_359_);
v_snd_363_ = lean_ctor_get(v_v_362_, 1);
lean_inc(v_snd_363_);
v___x_364_ = lean_unsigned_to_nat(0u);
v_bs_x27_365_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_364_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_359_, v___x_366_);
v___x_368_ = lean_array_uset(v_bs_x27_365_, v_i_359_, v_snd_363_);
v_i_359_ = v___x_367_;
v_bs_360_ = v___x_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_bs_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_374_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_373_, v_i_boxed_374_, v_bs_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0(lean_object* v_a_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___y_381_; 
if (lean_obj_tag(v_x_379_) == 0)
{
lean_object* v___x_384_; 
v___x_384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0___closed__0));
v___y_381_ = v___x_384_;
goto v___jp_380_;
}
else
{
lean_object* v_val_385_; 
v_val_385_ = lean_ctor_get(v_x_379_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v_x_379_, 1);
v___y_381_ = v_val_385_;
goto v___jp_380_;
}
v___jp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_array_push(v___y_381_, v_a_378_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
if (lean_obj_tag(v_x_387_) == 0)
{
uint8_t v___x_388_; 
v___x_388_ = 1;
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = 0;
return v___x_389_;
}
}
else
{
if (lean_obj_tag(v_x_387_) == 0)
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
else
{
lean_object* v_val_391_; lean_object* v_val_392_; uint8_t v___x_393_; 
v_val_391_ = lean_ctor_get(v_x_386_, 0);
v_val_392_ = lean_ctor_get(v_x_387_, 0);
v___x_393_ = lean_nat_dec_eq(v_val_391_, v_val_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2_spec__5(v_x_394_, v_x_395_);
lean_dec(v_x_395_);
lean_dec(v_x_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___redArg(lean_object* v_m_398_, lean_object* v_query_399_, lean_object* v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_zero_403_; uint8_t v_isZero_404_; 
v_zero_403_ = lean_unsigned_to_nat(0u);
v_isZero_404_ = lean_nat_dec_eq(v_x_401_, v_zero_403_);
if (v_isZero_404_ == 1)
{
lean_dec(v_x_402_);
lean_dec(v_x_401_);
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v___x_405_; 
v___x_405_ = lean_box(2);
return v___x_405_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_val_406_ = lean_ctor_get(v_x_400_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v_x_400_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_val_406_);
lean_dec(v_x_400_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_val_406_);
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
lean_object* v_keyArray_414_; lean_object* v_valueArray_415_; lean_object* v___x_416_; uint8_t v_isSome_417_; 
v_keyArray_414_ = lean_ctor_get(v_m_398_, 1);
v_valueArray_415_ = lean_ctor_get(v_m_398_, 2);
v___x_416_ = lean_array_fget_borrowed(v_keyArray_414_, v_x_402_);
v_isSome_417_ = lean_noption_is_some(v___x_416_);
if (v_isSome_417_ == 0)
{
lean_dec(v_x_401_);
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v___x_418_; 
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_x_402_);
return v___x_418_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_x_402_);
v_val_419_ = lean_ctor_get(v_x_400_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v_x_400_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_val_419_);
lean_dec(v_x_400_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_val_419_);
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
lean_object* v_one_427_; lean_object* v_n_428_; lean_object* v___y_430_; 
v_one_427_ = lean_unsigned_to_nat(1u);
v_n_428_ = lean_nat_sub(v_x_401_, v_one_427_);
lean_dec(v_x_401_);
if (v_isSome_417_ == 0)
{
goto v___jp_436_;
}
else
{
lean_object* v___x_444_; uint8_t v_isSome_445_; 
v___x_444_ = lean_array_fget_borrowed(v_valueArray_415_, v_x_402_);
v_isSome_445_ = lean_noption_is_some(v___x_444_);
if (v_isSome_445_ == 0)
{
goto v___jp_436_;
}
else
{
lean_object* v_val_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v_val_451_; uint8_t v___y_453_; uint8_t v___x_456_; 
lean_inc(v___x_416_);
v_val_446_ = lean_noption_get(v___x_416_);
v_fst_447_ = lean_ctor_get(v_val_446_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v_val_446_, 1);
lean_inc(v_snd_448_);
v_fst_449_ = lean_ctor_get(v_query_399_, 0);
v_snd_450_ = lean_ctor_get(v_query_399_, 1);
lean_inc(v___x_444_);
v_val_451_ = lean_noption_get(v___x_444_);
v___x_456_ = lean_unbox(v_fst_447_);
lean_dec(v_fst_447_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = lean_unbox(v_fst_449_);
if (v___x_457_ == 0)
{
v___y_453_ = v_isSome_445_;
goto v___jp_452_;
}
else
{
lean_dec(v_val_451_);
lean_dec(v_snd_448_);
lean_dec(v_val_446_);
goto v___jp_438_;
}
}
else
{
uint8_t v___x_458_; 
v___x_458_ = lean_unbox(v_fst_449_);
v___y_453_ = v___x_458_;
goto v___jp_452_;
}
v___jp_452_:
{
if (v___y_453_ == 0)
{
lean_dec(v_val_451_);
lean_dec(v_snd_448_);
lean_dec(v_val_446_);
goto v___jp_438_;
}
else
{
uint8_t v___x_454_; 
v___x_454_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2_spec__5(v_snd_448_, v_snd_450_);
lean_dec(v_snd_448_);
if (v___x_454_ == 0)
{
lean_dec(v_val_451_);
lean_dec(v_val_446_);
goto v___jp_438_;
}
else
{
lean_object* v___x_455_; 
lean_dec(v_n_428_);
lean_dec(v_x_400_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v_x_402_);
lean_ctor_set(v___x_455_, 1, v_val_446_);
lean_ctor_set(v___x_455_, 2, v_val_451_);
return v___x_455_;
}
}
}
}
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_array_get_size(v_keyArray_414_);
v___x_432_ = lean_nat_add(v_x_402_, v_one_427_);
lean_dec(v_x_402_);
v___x_433_ = lean_nat_dec_lt(v___x_432_, v___x_431_);
if (v___x_433_ == 0)
{
lean_dec(v___x_432_);
v_x_400_ = v___y_430_;
v_x_401_ = v_n_428_;
v_x_402_ = v_zero_403_;
goto _start;
}
else
{
v_x_400_ = v___y_430_;
v_x_401_ = v_n_428_;
v_x_402_ = v___x_432_;
goto _start;
}
}
v___jp_436_:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v___x_437_; 
lean_inc(v_x_402_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v_x_402_);
v___y_430_ = v___x_437_;
goto v___jp_429_;
}
else
{
v___y_430_ = v_x_400_;
goto v___jp_429_;
}
}
v___jp_438_:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_array_get_size(v_keyArray_414_);
v___x_440_ = lean_nat_add(v_x_402_, v_one_427_);
lean_dec(v_x_402_);
v___x_441_ = lean_nat_dec_lt(v___x_440_, v___x_439_);
if (v___x_441_ == 0)
{
lean_dec(v___x_440_);
v_x_401_ = v_n_428_;
v_x_402_ = v_zero_403_;
goto _start;
}
else
{
v_x_401_ = v_n_428_;
v_x_402_ = v___x_440_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_459_, lean_object* v_query_460_, lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___redArg(v_m_459_, v_query_460_, v_x_461_, v_x_462_, v_x_463_);
lean_dec_ref(v_query_460_);
lean_dec_ref(v_m_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object* v_m_465_, lean_object* v_query_466_){
_start:
{
lean_object* v_keyArray_467_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_470_; uint64_t v___y_472_; uint64_t v___y_473_; uint64_t v___y_490_; uint8_t v___x_496_; 
v_keyArray_467_ = lean_ctor_get(v_m_465_, 1);
v_fst_468_ = lean_ctor_get(v_query_466_, 0);
v_snd_469_ = lean_ctor_get(v_query_466_, 1);
v___x_470_ = lean_array_get_size(v_keyArray_467_);
v___x_496_ = lean_unbox(v_fst_468_);
if (v___x_496_ == 0)
{
uint64_t v___x_497_; 
v___x_497_ = 13ULL;
v___y_490_ = v___x_497_;
goto v___jp_489_;
}
else
{
uint64_t v___x_498_; 
v___x_498_ = 11ULL;
v___y_490_ = v___x_498_;
goto v___jp_489_;
}
v___jp_471_:
{
uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v_fold_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_474_ = lean_uint64_mix_hash(v___y_472_, v___y_473_);
v___x_475_ = 32ULL;
v___x_476_ = lean_uint64_shift_right(v___x_474_, v___x_475_);
v_fold_477_ = lean_uint64_xor(v___x_474_, v___x_476_);
v___x_478_ = 16ULL;
v___x_479_ = lean_uint64_shift_right(v_fold_477_, v___x_478_);
v___x_480_ = lean_uint64_xor(v_fold_477_, v___x_479_);
v___x_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = lean_usize_of_nat(v___x_470_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v___x_482_, v___x_483_);
v___x_485_ = lean_usize_land(v___x_481_, v___x_484_);
v___x_486_ = lean_usize_to_nat(v___x_485_);
v___x_487_ = lean_box(0);
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___redArg(v_m_465_, v_query_466_, v___x_487_, v___x_470_, v___x_486_);
return v___x_488_;
}
v___jp_489_:
{
if (lean_obj_tag(v_snd_469_) == 0)
{
uint64_t v___x_491_; 
v___x_491_ = 11ULL;
v___y_472_ = v___y_490_;
v___y_473_ = v___x_491_;
goto v___jp_471_;
}
else
{
lean_object* v_val_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; 
v_val_492_ = lean_ctor_get(v_snd_469_, 0);
v___x_493_ = l_String_instHashableRaw_hash(v_val_492_);
v___x_494_ = 13ULL;
v___x_495_ = lean_uint64_mix_hash(v___x_493_, v___x_494_);
v___y_472_ = v___y_490_;
v___y_473_ = v___x_495_;
goto v___jp_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(lean_object* v_m_499_, lean_object* v_query_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_m_499_, v_query_500_);
lean_dec_ref(v_query_500_);
lean_dec_ref(v_m_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_b_502_, lean_object* v_acc_503_, lean_object* v_i_504_){
_start:
{
lean_object* v___y_506_; lean_object* v_keyArray_514_; lean_object* v_valueArray_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_keyArray_514_ = lean_ctor_get(v_b_502_, 1);
v_valueArray_515_ = lean_ctor_get(v_b_502_, 2);
v___x_516_ = lean_array_get_size(v_keyArray_514_);
v___x_517_ = lean_nat_dec_lt(v_i_504_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec(v_i_504_);
return v_acc_503_;
}
else
{
lean_object* v___x_518_; uint8_t v_isSome_519_; 
v___x_518_ = lean_array_fget_borrowed(v_keyArray_514_, v_i_504_);
v_isSome_519_ = lean_noption_is_some(v___x_518_);
if (v_isSome_519_ == 0)
{
goto v___jp_510_;
}
else
{
lean_object* v___x_520_; uint8_t v_isSome_521_; 
v___x_520_ = lean_array_fget_borrowed(v_valueArray_515_, v_i_504_);
v_isSome_521_ = lean_noption_is_some(v___x_520_);
if (v_isSome_521_ == 0)
{
goto v___jp_510_;
}
else
{
lean_object* v_val_522_; lean_object* v_val_523_; lean_object* v_i_525_; lean_object* v___x_530_; 
lean_inc(v___x_518_);
v_val_522_ = lean_noption_get(v___x_518_);
lean_inc(v___x_520_);
v_val_523_ = lean_noption_get(v___x_520_);
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_acc_503_, v_val_522_);
switch(lean_obj_tag(v___x_530_))
{
case 0:
{
lean_object* v_index_531_; lean_object* v_size_532_; lean_object* v___x_533_; 
v_index_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_index_531_);
lean_dec_ref_known(v___x_530_, 3);
v_size_532_ = lean_ctor_get(v_acc_503_, 0);
lean_inc(v_size_532_);
v___x_533_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_503_, v_size_532_, v_index_531_, v_val_522_, v_val_523_);
lean_dec(v_index_531_);
v___y_506_ = v___x_533_;
goto v___jp_505_;
}
case 1:
{
lean_object* v_index_534_; 
v_index_534_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_index_534_);
lean_dec_ref_known(v___x_530_, 1);
v_i_525_ = v_index_534_;
goto v___jp_524_;
}
default: 
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_503_, v___x_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_index_537_; 
v_index_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_index_537_);
lean_dec_ref_known(v___x_536_, 1);
v_i_525_ = v_index_537_;
goto v___jp_524_;
}
else
{
lean_dec(v_val_523_);
lean_dec(v_val_522_);
v___y_506_ = v_acc_503_;
goto v___jp_505_;
}
}
}
v___jp_524_:
{
lean_object* v_size_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_size_526_ = lean_ctor_get(v_acc_503_, 0);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v_size_526_, v___x_527_);
v___x_529_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_503_, v___x_528_, v_i_525_, v_val_522_, v_val_523_);
lean_dec(v_i_525_);
v___y_506_ = v___x_529_;
goto v___jp_505_;
}
}
}
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_i_504_, v___x_507_);
lean_dec(v_i_504_);
v_acc_503_ = v___y_506_;
v_i_504_ = v___x_508_;
goto _start;
}
v___jp_510_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_add(v_i_504_, v___x_511_);
lean_dec(v_i_504_);
v_i_504_ = v___x_512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_b_538_, lean_object* v_acc_539_, lean_object* v_i_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___redArg(v_b_538_, v_acc_539_, v_i_540_);
lean_dec_ref(v_b_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___redArg(lean_object* v_init_542_, lean_object* v_b_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___redArg(v_b_543_, v_init_542_, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_init_546_, lean_object* v_b_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___redArg(v_init_546_, v_b_547_);
lean_dec_ref(v_b_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg(lean_object* v_m_549_){
_start:
{
lean_object* v_keyArray_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_cellCount_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_target_557_; lean_object* v___x_558_; 
v_keyArray_550_ = lean_ctor_get(v_m_549_, 1);
v___x_551_ = lean_array_get_size(v_keyArray_550_);
v___x_552_ = lean_unsigned_to_nat(2u);
v_cellCount_553_ = lean_nat_mul(v___x_551_, v___x_552_);
v___x_554_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_553_);
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_553_);
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_553_);
v_target_557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_557_, 0, v___x_554_);
lean_ctor_set(v_target_557_, 1, v___x_555_);
lean_ctor_set(v_target_557_, 2, v___x_556_);
v___x_558_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___redArg(v_target_557_, v_m_549_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg___boxed(lean_object* v_m_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg(v_m_559_);
lean_dec_ref(v_m_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg(lean_object* v_key_561_, lean_object* v_as_562_, size_t v_sz_563_, size_t v_i_564_, lean_object* v_b_565_){
_start:
{
lean_object* v___y_567_; uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_lt(v_i_564_, v_sz_563_);
if (v___x_571_ == 0)
{
lean_dec_ref(v_key_561_);
return v_b_565_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_572_ = lean_array_uget_borrowed(v_as_562_, v_i_564_);
lean_inc_ref(v_key_561_);
lean_inc(v_a_572_);
v___x_573_ = lean_apply_1(v_key_561_, v_a_572_);
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_b_565_, v___x_573_);
switch(lean_obj_tag(v___x_574_))
{
case 0:
{
lean_object* v_index_575_; lean_object* v_value_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_index_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_index_575_);
v_value_576_ = lean_ctor_get(v___x_574_, 2);
lean_inc(v_value_576_);
lean_dec_ref_known(v___x_574_, 3);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_value_576_);
lean_inc(v_a_572_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0(v_a_572_, v___x_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_size_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec_ref(v___x_573_);
v_size_579_ = lean_ctor_get(v_b_565_, 0);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_sub(v_size_579_, v___x_580_);
v___x_582_ = l_Std_DHashMap_Raw_clearCell___redArg(v_b_565_, v___x_581_, v_index_575_);
lean_dec(v_index_575_);
v___y_567_ = v___x_582_;
goto v___jp_566_;
}
else
{
lean_object* v_val_583_; lean_object* v_size_584_; lean_object* v___x_585_; 
v_val_583_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v___x_578_, 1);
v_size_584_ = lean_ctor_get(v_b_565_, 0);
lean_inc(v_size_584_);
v___x_585_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_565_, v_size_584_, v_index_575_, v___x_573_, v_val_583_);
lean_dec(v_index_575_);
v___y_567_ = v___x_585_;
goto v___jp_566_;
}
}
case 1:
{
lean_object* v_index_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_index_586_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_index_586_);
lean_dec_ref_known(v___x_574_, 1);
v___x_587_ = lean_box(0);
lean_inc(v_a_572_);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0(v_a_572_, v___x_587_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_dec(v_index_586_);
lean_dec_ref(v___x_573_);
v___y_567_ = v_b_565_;
goto v___jp_566_;
}
else
{
lean_object* v_val_589_; lean_object* v___y_591_; lean_object* v_i_592_; lean_object* v_size_607_; lean_object* v_keyArray_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_val_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v___x_588_, 1);
v_size_607_ = lean_ctor_get(v_b_565_, 0);
v_keyArray_608_ = lean_ctor_get(v_b_565_, 1);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_size_607_, v___x_609_);
v___x_611_ = lean_array_get_size(v_keyArray_608_);
v___x_612_ = lean_nat_dec_lt(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_dec(v___x_610_);
lean_dec(v_index_586_);
goto v___jp_597_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_613_ = lean_unsigned_to_nat(4u);
v___x_614_ = lean_nat_mul(v___x_610_, v___x_613_);
v___x_615_ = lean_unsigned_to_nat(3u);
v___x_616_ = lean_nat_mul(v___x_611_, v___x_615_);
v___x_617_ = lean_nat_dec_le(v___x_614_, v___x_616_);
lean_dec(v___x_616_);
lean_dec(v___x_614_);
if (v___x_617_ == 0)
{
lean_dec(v___x_610_);
lean_dec(v_index_586_);
goto v___jp_597_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_565_, v___x_610_, v_index_586_, v___x_573_, v_val_589_);
lean_dec(v_index_586_);
v___y_567_ = v___x_618_;
goto v___jp_566_;
}
}
v___jp_590_:
{
lean_object* v_size_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_size_593_ = lean_ctor_get(v___y_591_, 0);
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_size_593_, v___x_594_);
v___x_596_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_591_, v___x_595_, v_i_592_, v___x_573_, v_val_589_);
lean_dec(v_i_592_);
v___y_567_ = v___x_596_;
goto v___jp_566_;
}
v___jp_597_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg(v_b_565_);
lean_dec_ref(v_b_565_);
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v___x_598_, v___x_573_);
switch(lean_obj_tag(v___x_599_))
{
case 0:
{
lean_object* v_index_600_; lean_object* v_size_601_; lean_object* v___x_602_; 
v_index_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_index_600_);
lean_dec_ref_known(v___x_599_, 3);
v_size_601_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_size_601_);
v___x_602_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_598_, v_size_601_, v_index_600_, v___x_573_, v_val_589_);
lean_dec(v_index_600_);
v___y_567_ = v___x_602_;
goto v___jp_566_;
}
case 1:
{
lean_object* v_index_603_; 
v_index_603_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_index_603_);
lean_dec_ref_known(v___x_599_, 1);
v___y_591_ = v___x_598_;
v_i_592_ = v_index_603_;
goto v___jp_590_;
}
default: 
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_598_, v___x_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_index_606_; 
v_index_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_index_606_);
lean_dec_ref_known(v___x_605_, 1);
v___y_591_ = v___x_598_;
v_i_592_ = v_index_606_;
goto v___jp_590_;
}
else
{
lean_dec(v_val_589_);
lean_dec_ref(v___x_573_);
v___y_567_ = v___x_598_;
goto v___jp_566_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(0);
lean_inc(v_a_572_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___lam__0(v_a_572_, v___x_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec_ref(v___x_573_);
v___y_567_ = v_b_565_;
goto v___jp_566_;
}
else
{
lean_object* v_val_621_; lean_object* v___y_623_; lean_object* v_i_624_; lean_object* v___y_630_; lean_object* v_size_639_; lean_object* v_keyArray_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_val_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v___x_620_, 1);
v_size_639_ = lean_ctor_get(v_b_565_, 0);
v_keyArray_640_ = lean_ctor_get(v_b_565_, 1);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_size_639_, v___x_641_);
v___x_643_ = lean_array_get_size(v_keyArray_640_);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v___x_642_);
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg(v_b_565_);
lean_dec_ref(v_b_565_);
v___y_630_ = v___x_645_;
goto v___jp_629_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_646_ = lean_unsigned_to_nat(4u);
v___x_647_ = lean_nat_mul(v___x_642_, v___x_646_);
lean_dec(v___x_642_);
v___x_648_ = lean_unsigned_to_nat(3u);
v___x_649_ = lean_nat_mul(v___x_643_, v___x_648_);
v___x_650_ = lean_nat_dec_le(v___x_647_, v___x_649_);
lean_dec(v___x_649_);
lean_dec(v___x_647_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg(v_b_565_);
lean_dec_ref(v_b_565_);
v___y_630_ = v___x_651_;
goto v___jp_629_;
}
else
{
v___y_630_ = v_b_565_;
goto v___jp_629_;
}
}
v___jp_622_:
{
lean_object* v_size_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_size_625_ = lean_ctor_get(v___y_623_, 0);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_size_625_, v___x_626_);
v___x_628_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_623_, v___x_627_, v_i_624_, v___x_573_, v_val_621_);
lean_dec(v_i_624_);
v___y_567_ = v___x_628_;
goto v___jp_566_;
}
v___jp_629_:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v___y_630_, v___x_573_);
switch(lean_obj_tag(v___x_631_))
{
case 0:
{
lean_object* v_index_632_; lean_object* v_size_633_; lean_object* v___x_634_; 
v_index_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_index_632_);
lean_dec_ref_known(v___x_631_, 3);
v_size_633_ = lean_ctor_get(v___y_630_, 0);
lean_inc(v_size_633_);
v___x_634_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_630_, v_size_633_, v_index_632_, v___x_573_, v_val_621_);
lean_dec(v_index_632_);
v___y_567_ = v___x_634_;
goto v___jp_566_;
}
case 1:
{
lean_object* v_index_635_; 
v_index_635_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_index_635_);
lean_dec_ref_known(v___x_631_, 1);
v___y_623_ = v___y_630_;
v_i_624_ = v_index_635_;
goto v___jp_622_;
}
default: 
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_630_, v___x_636_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_index_638_; 
v_index_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_index_638_);
lean_dec_ref_known(v___x_637_, 1);
v___y_623_ = v___y_630_;
v_i_624_ = v_index_638_;
goto v___jp_622_;
}
else
{
lean_dec(v_val_621_);
lean_dec_ref(v___x_573_);
v___y_567_ = v___y_630_;
goto v___jp_566_;
}
}
}
}
}
}
}
}
v___jp_566_:
{
size_t v___x_568_; size_t v___x_569_; 
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_564_, v___x_568_);
v_i_564_ = v___x_569_;
v_b_565_ = v___y_567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg___boxed(lean_object* v_key_652_, lean_object* v_as_653_, lean_object* v_sz_654_, lean_object* v_i_655_, lean_object* v_b_656_){
_start:
{
size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_sz_boxed_657_ = lean_unbox_usize(v_sz_654_);
lean_dec(v_sz_654_);
v_i_boxed_658_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg(v_key_652_, v_as_653_, v_sz_boxed_657_, v_i_boxed_658_, v_b_656_);
lean_dec_ref(v_as_653_);
return v_res_659_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_660_; lean_object* v___x_661_; 
v_cellCount_660_ = lean_unsigned_to_nat(16u);
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_662_; lean_object* v___x_663_; 
v_cellCount_662_ = lean_unsigned_to_nat(16u);
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_groups_667_; 
v___x_664_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__1, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__1_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__1);
v___x_665_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__0, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__0_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__0);
v___x_666_ = lean_unsigned_to_nat(0u);
v_groups_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_groups_667_, 0, v___x_666_);
lean_ctor_set(v_groups_667_, 1, v___x_665_);
lean_ctor_set(v_groups_667_, 2, v___x_664_);
return v_groups_667_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(lean_object* v_key_668_, lean_object* v_xs_669_){
_start:
{
lean_object* v_groups_670_; size_t v_sz_671_; size_t v___x_672_; lean_object* v___x_673_; 
v_groups_670_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__2, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__2_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___closed__2);
v_sz_671_ = lean_array_size(v_xs_669_);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg(v_key_668_, v_xs_669_, v_sz_671_, v___x_672_, v_groups_670_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(lean_object* v_key_674_, lean_object* v_xs_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_key_674_, v_xs_675_);
lean_dec_ref(v_xs_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__5(lean_object* v_b_677_, lean_object* v_acc_678_, lean_object* v_i_679_){
_start:
{
lean_object* v_keyArray_684_; lean_object* v_valueArray_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_keyArray_684_ = lean_ctor_get(v_b_677_, 1);
v_valueArray_685_ = lean_ctor_get(v_b_677_, 2);
v___x_686_ = lean_array_get_size(v_keyArray_684_);
v___x_687_ = lean_nat_dec_lt(v_i_679_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v_i_679_);
return v_acc_678_;
}
else
{
lean_object* v___x_688_; uint8_t v_isSome_689_; 
v___x_688_ = lean_array_fget_borrowed(v_keyArray_684_, v_i_679_);
v_isSome_689_ = lean_noption_is_some(v___x_688_);
if (v_isSome_689_ == 0)
{
goto v___jp_680_;
}
else
{
lean_object* v___x_690_; uint8_t v_isSome_691_; 
v___x_690_ = lean_array_fget_borrowed(v_valueArray_685_, v_i_679_);
v_isSome_691_ = lean_noption_is_some(v___x_690_);
if (v_isSome_691_ == 0)
{
goto v___jp_680_;
}
else
{
lean_object* v_val_692_; lean_object* v_val_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc(v___x_688_);
v_val_692_ = lean_noption_get(v___x_688_);
lean_inc(v___x_690_);
v_val_693_ = lean_noption_get(v___x_690_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_val_692_);
lean_ctor_set(v___x_694_, 1, v_val_693_);
v___x_695_ = lean_array_push(v_acc_678_, v___x_694_);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v_i_679_, v___x_696_);
lean_dec(v_i_679_);
v_acc_678_ = v___x_695_;
v_i_679_ = v___x_697_;
goto _start;
}
}
}
v___jp_680_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_i_679_, v___x_681_);
lean_dec(v_i_679_);
v_i_679_ = v___x_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__5___boxed(lean_object* v_b_699_, lean_object* v_acc_700_, lean_object* v_i_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__5(v_b_699_, v_acc_700_, v_i_701_);
lean_dec_ref(v_b_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object* v_init_703_, lean_object* v_b_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__5(v_b_704_, v_init_703_, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object* v_init_707_, lean_object* v_b_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_init_707_, v_b_708_);
lean_dec_ref(v_b_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object* v_items_711_){
_start:
{
lean_object* v___y_713_; lean_object* v___f_717_; lean_object* v_partitions_718_; lean_object* v_size_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___f_717_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0));
v_partitions_718_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v___f_717_, v_items_711_);
v_size_719_ = lean_ctor_get(v_partitions_718_, 0);
lean_inc(v_size_719_);
v___x_720_ = lean_mk_empty_array_with_capacity(v_size_719_);
lean_dec(v_size_719_);
v___x_721_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v___x_720_, v_partitions_718_);
lean_dec_ref(v_partitions_718_);
v___x_722_ = lean_array_get_size(v___x_721_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_nat_dec_eq(v___x_722_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___y_732_; uint8_t v___x_734_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_sub(v___x_722_, v___x_729_);
v___x_734_ = lean_nat_dec_le(v___x_727_, v___x_730_);
if (v___x_734_ == 0)
{
lean_inc(v___x_730_);
v___y_732_ = v___x_730_;
goto v___jp_731_;
}
else
{
v___y_732_ = v___x_727_;
goto v___jp_731_;
}
v___jp_731_:
{
uint8_t v___x_733_; 
v___x_733_ = lean_nat_dec_le(v___y_732_, v___x_730_);
if (v___x_733_ == 0)
{
lean_dec(v___x_730_);
lean_inc(v___y_732_);
v___y_724_ = v___y_732_;
v___y_725_ = v___y_732_;
goto v___jp_723_;
}
else
{
v___y_724_ = v___y_732_;
v___y_725_ = v___x_730_;
goto v___jp_723_;
}
}
}
else
{
v___y_713_ = v___x_721_;
goto v___jp_712_;
}
v___jp_712_:
{
size_t v_sz_714_; size_t v___x_715_; lean_object* v___x_716_; 
v_sz_714_ = lean_array_size(v___y_713_);
v___x_715_ = ((size_t)0ULL);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_714_, v___x_715_, v___y_713_);
return v___x_716_;
}
v___jp_723_:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg(v___x_722_, v___x_721_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
v___y_713_ = v___x_726_;
goto v___jp_712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object* v_items_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_735_);
lean_dec_ref(v_items_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object* v_00_u03b2_737_, lean_object* v_key_738_, lean_object* v_xs_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_key_738_, v_xs_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object* v_00_u03b2_741_, lean_object* v_key_742_, lean_object* v_xs_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_00_u03b2_741_, v_key_742_, v_xs_743_);
lean_dec_ref(v_xs_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object* v_n_745_, lean_object* v_as_746_, lean_object* v_lo_747_, lean_object* v_hi_748_, lean_object* v_w_749_, lean_object* v_hlo_750_, lean_object* v_hhi_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___redArg(v_n_745_, v_as_746_, v_lo_747_, v_hi_748_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object* v_n_753_, lean_object* v_as_754_, lean_object* v_lo_755_, lean_object* v_hi_756_, lean_object* v_w_757_, lean_object* v_hlo_758_, lean_object* v_hhi_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_n_753_, v_as_754_, v_lo_755_, v_hi_756_, v_w_757_, v_hlo_758_, v_hhi_759_);
lean_dec(v_hi_756_);
lean_dec(v_n_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object* v_00_u03b2_761_, lean_object* v_m_762_, lean_object* v_query_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_m_762_, v_query_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object* v_00_u03b2_765_, lean_object* v_m_766_, lean_object* v_query_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_00_u03b2_765_, v_m_766_, v_query_767_);
lean_dec_ref(v_query_767_);
lean_dec_ref(v_m_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2(lean_object* v_00_u03b2_769_, lean_object* v_m_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___redArg(v_m_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2___boxed(lean_object* v_00_u03b2_772_, lean_object* v_m_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2(v_00_u03b2_772_, v_m_773_);
lean_dec_ref(v_m_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3(lean_object* v_00_u03b2_775_, lean_object* v_key_776_, lean_object* v_as_777_, size_t v_sz_778_, size_t v_i_779_, lean_object* v_b_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___redArg(v_key_776_, v_as_777_, v_sz_778_, v_i_779_, v_b_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3___boxed(lean_object* v_00_u03b2_782_, lean_object* v_key_783_, lean_object* v_as_784_, lean_object* v_sz_785_, lean_object* v_i_786_, lean_object* v_b_787_){
_start:
{
size_t v_sz_boxed_788_; size_t v_i_boxed_789_; lean_object* v_res_790_; 
v_sz_boxed_788_ = lean_unbox_usize(v_sz_785_);
lean_dec(v_sz_785_);
v_i_boxed_789_ = lean_unbox_usize(v_i_786_);
lean_dec(v_i_786_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__3(v_00_u03b2_782_, v_key_783_, v_as_784_, v_sz_boxed_788_, v_i_boxed_789_, v_b_787_);
lean_dec_ref(v_as_784_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7(lean_object* v_n_791_, lean_object* v_lo_792_, lean_object* v_hi_793_, lean_object* v_hhi_794_, lean_object* v_pivot_795_, lean_object* v_as_796_, lean_object* v_i_797_, lean_object* v_k_798_, lean_object* v_ilo_799_, lean_object* v_ik_800_, lean_object* v_w_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___redArg(v_hi_793_, v_pivot_795_, v_as_796_, v_i_797_, v_k_798_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7___boxed(lean_object* v_n_803_, lean_object* v_lo_804_, lean_object* v_hi_805_, lean_object* v_hhi_806_, lean_object* v_pivot_807_, lean_object* v_as_808_, lean_object* v_i_809_, lean_object* v_k_810_, lean_object* v_ilo_811_, lean_object* v_ik_812_, lean_object* v_w_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3_spec__7(v_n_803_, v_lo_804_, v_hi_805_, v_hhi_806_, v_pivot_807_, v_as_808_, v_i_809_, v_k_810_, v_ilo_811_, v_ik_812_, v_w_813_);
lean_dec_ref(v_pivot_807_);
lean_dec(v_hi_805_);
lean_dec(v_lo_804_);
lean_dec(v_n_803_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_815_, lean_object* v_m_816_, lean_object* v_query_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___redArg(v_m_816_, v_query_817_, v_x_818_, v_x_819_, v_x_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_823_, lean_object* v_m_824_, lean_object* v_query_825_, lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1_spec__2(v_00_u03b2_823_, v_m_824_, v_query_825_, v_x_826_, v_x_827_, v_x_828_, v_x_829_);
lean_dec_ref(v_query_825_);
lean_dec_ref(v_m_824_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_831_, lean_object* v_init_832_, lean_object* v_b_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___redArg(v_init_832_, v_b_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_835_, lean_object* v_init_836_, lean_object* v_b_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4(v_00_u03b2_835_, v_init_836_, v_b_837_);
lean_dec_ref(v_b_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_839_, lean_object* v_b_840_, lean_object* v_acc_841_, lean_object* v_i_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___redArg(v_b_840_, v_acc_841_, v_i_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_844_, lean_object* v_b_845_, lean_object* v_acc_846_, lean_object* v_i_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_844_, v_b_845_, v_acc_846_, v_i_847_);
lean_dec_ref(v_b_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object* v_fileMap_849_, lean_object* v_hoverPos_850_, lean_object* v_cmdStx_851_, lean_object* v_infoTree_852_){
_start:
{
lean_object* v___x_853_; lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v___x_853_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_849_, v_hoverPos_850_, v_cmdStx_851_, v_infoTree_852_);
v_fst_854_ = lean_ctor_get(v___x_853_, 0);
v_snd_855_ = lean_ctor_get(v___x_853_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v___x_853_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_snd_855_);
lean_inc(v_fst_854_);
lean_dec(v___x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_partitions_861_; lean_object* v___x_863_; 
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = l_Array_zipIdx___redArg(v_fst_854_, v___x_859_);
v_partitions_861_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_860_);
lean_dec_ref(v___x_860_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v_partitions_861_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_partitions_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_snd_855_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
lean_object* runtime_initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
}
#ifdef __cplusplus
}
#endif
