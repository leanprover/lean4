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
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_size_x3f(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0;
static lean_once_cell_t l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_13_);
v_toElabInfo_16_ = lean_ctor_get(v_termInfo_15_, 0);
lean_inc_ref(v_toElabInfo_16_);
v_termInfo_17_ = lean_ctor_get(v_a_14_, 0);
lean_inc_ref(v_termInfo_17_);
lean_dec_ref(v_a_14_);
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
lean_dec_ref(v_a_13_);
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
lean_dec_ref(v_a_13_);
v_stx_29_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_29_);
v_id_30_ = lean_ctor_get(v_a_14_, 1);
lean_inc(v_id_30_);
v_structName_31_ = lean_ctor_get(v_a_14_, 3);
lean_inc(v_structName_31_);
lean_dec_ref(v_a_14_);
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
lean_dec_ref(v_a_13_);
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
lean_dec_ref(v_a_13_);
v_stx_39_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_39_);
lean_dec_ref(v_a_14_);
v___x_40_ = l_Lean_Syntax_eqWithInfo(v_stx_38_, v_stx_39_);
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
lean_dec_ref(v_a_13_);
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
lean_dec_ref(v_a_13_);
v_stx_43_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_43_);
lean_dec_ref(v_a_14_);
v___x_44_ = l_Lean_Syntax_eqWithInfo(v_stx_42_, v_stx_43_);
return v___x_44_;
}
else
{
uint8_t v___x_45_; 
lean_dec_ref(v_a_13_);
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
lean_dec_ref(v_a_13_);
v_stx_47_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_47_);
lean_dec_ref(v_a_14_);
v___x_48_ = l_Lean_Syntax_eqWithInfo(v_stx_46_, v_stx_47_);
return v___x_48_;
}
else
{
uint8_t v___x_49_; 
lean_dec_ref(v_a_13_);
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
lean_dec_ref(v_a_13_);
v_stx_51_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_51_);
lean_dec_ref(v_a_14_);
v___x_52_ = l_Lean_Syntax_eqWithInfo(v_stx_50_, v_stx_51_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
lean_dec_ref(v_a_13_);
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
lean_dec_ref(v_a_13_);
v_stx_55_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_55_);
lean_dec_ref(v_a_14_);
v___x_56_ = l_Lean_Syntax_eqWithInfo(v_stx_54_, v_stx_55_);
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
lean_dec_ref(v_a_13_);
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
lean_dec_ref(v_a_14_);
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
lean_dec_ref(v_i_126_);
v___x_143_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_139_, v___x_142_);
lean_dec(v_stx_139_);
if (lean_obj_tag(v___x_143_) == 1)
{
lean_object* v_val_144_; uint8_t v___x_145_; uint8_t v___x_146_; 
v_val_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_val_144_);
lean_dec_ref(v___x_143_);
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
lean_dec_ref(v___x_128_);
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
lean_dec_ref(v_i_126_);
v___x_133_ = 1;
v___x_134_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_132_, v___x_133_);
lean_dec(v_stx_132_);
if (lean_obj_tag(v___x_134_) == 1)
{
lean_object* v_val_135_; uint8_t v___x_136_; uint8_t v___x_137_; 
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v___x_134_);
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
lean_dec_ref(v_info_168_);
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
lean_dec_ref(v___x_201_);
v___y_196_ = v_val_204_;
goto v___jp_195_;
}
}
v___jp_171_:
{
uint8_t v___x_175_; 
v___x_175_ = lean_nat_dec_eq(v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec(v___y_172_);
if (v___x_175_ == 0)
{
lean_dec(v___y_174_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
return v_best_169_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v___y_174_);
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
v___y_173_ = v_line_186_;
v___y_174_ = v___y_182_;
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
v___y_173_ = v_line_186_;
v___y_174_ = v___y_182_;
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
lean_dec_ref(v_info_168_);
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
lean_dec_ref(v___x_197_);
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
lean_dec_ref(v___x_241_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
return v_x_251_;
}
else
{
lean_object* v_key_253_; lean_object* v_value_254_; lean_object* v_tail_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_key_253_ = lean_ctor_get(v_x_252_, 0);
v_value_254_ = lean_ctor_get(v_x_252_, 1);
v_tail_255_ = lean_ctor_get(v_x_252_, 2);
lean_inc(v_value_254_);
lean_inc(v_key_253_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_key_253_);
lean_ctor_set(v___x_256_, 1, v_value_254_);
v___x_257_ = lean_array_push(v_x_251_, v___x_256_);
v_x_251_ = v___x_257_;
v_x_252_ = v_tail_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_x_259_, v_x_260_);
lean_dec(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(lean_object* v_as_262_, size_t v_i_263_, size_t v_stop_264_, lean_object* v_b_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_eq(v_i_263_, v_stop_264_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; size_t v___x_269_; size_t v___x_270_; 
v___x_267_ = lean_array_uget_borrowed(v_as_262_, v_i_263_);
v___x_268_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_b_265_, v___x_267_);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_add(v_i_263_, v___x_269_);
v_i_263_ = v___x_270_;
v_b_265_ = v___x_268_;
goto _start;
}
else
{
return v_b_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4___boxed(lean_object* v_as_272_, lean_object* v_i_273_, lean_object* v_stop_274_, lean_object* v_b_275_){
_start:
{
size_t v_i_boxed_276_; size_t v_stop_boxed_277_; lean_object* v_res_278_; 
v_i_boxed_276_ = lean_unbox_usize(v_i_273_);
lean_dec(v_i_273_);
v_stop_boxed_277_ = lean_unbox_usize(v_stop_274_);
lean_dec(v_stop_274_);
v_res_278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_272_, v_i_boxed_276_, v_stop_boxed_277_, v_b_275_);
lean_dec_ref(v_as_272_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t v_sz_279_, size_t v_i_280_, lean_object* v_bs_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = lean_usize_dec_lt(v_i_280_, v_sz_279_);
if (v___x_282_ == 0)
{
return v_bs_281_;
}
else
{
lean_object* v_v_283_; lean_object* v_snd_284_; lean_object* v___x_285_; lean_object* v_bs_x27_286_; size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v_v_283_ = lean_array_uget_borrowed(v_bs_281_, v_i_280_);
v_snd_284_ = lean_ctor_get(v_v_283_, 1);
lean_inc(v_snd_284_);
v___x_285_ = lean_unsigned_to_nat(0u);
v_bs_x27_286_ = lean_array_uset(v_bs_281_, v_i_280_, v___x_285_);
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_i_280_, v___x_287_);
v___x_289_ = lean_array_uset(v_bs_x27_286_, v_i_280_, v_snd_284_);
v_i_280_ = v___x_288_;
v_bs_281_ = v___x_289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object* v_sz_291_, lean_object* v_i_292_, lean_object* v_bs_293_){
_start:
{
size_t v_sz_boxed_294_; size_t v_i_boxed_295_; lean_object* v_res_296_; 
v_sz_boxed_294_ = lean_unbox_usize(v_sz_291_);
lean_dec(v_sz_291_);
v_i_boxed_295_ = lean_unbox_usize(v_i_292_);
lean_dec(v_i_292_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_294_, v_i_boxed_295_, v_bs_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object* v_hi_297_, lean_object* v_pivot_298_, lean_object* v_as_299_, lean_object* v_i_300_, lean_object* v_k_301_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_nat_dec_lt(v_k_301_, v_hi_297_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_k_301_);
v___x_313_ = lean_array_fswap(v_as_299_, v_i_300_, v_hi_297_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_i_300_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v_fst_316_; lean_object* v_fst_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; lean_object* v_fst_320_; lean_object* v_snd_321_; 
v___x_315_ = lean_array_fget_borrowed(v_as_299_, v_k_301_);
v_fst_316_ = lean_ctor_get(v___x_315_, 0);
v_fst_317_ = lean_ctor_get(v_pivot_298_, 0);
v_fst_318_ = lean_ctor_get(v_fst_316_, 0);
v_snd_319_ = lean_ctor_get(v_fst_316_, 1);
v_fst_320_ = lean_ctor_get(v_fst_317_, 0);
v_snd_321_ = lean_ctor_get(v_fst_317_, 1);
if (lean_obj_tag(v_snd_319_) == 0)
{
if (lean_obj_tag(v_snd_321_) == 1)
{
goto v___jp_302_;
}
else
{
goto v___jp_326_;
}
}
else
{
if (lean_obj_tag(v_snd_321_) == 0)
{
goto v___jp_306_;
}
else
{
goto v___jp_326_;
}
}
v___jp_322_:
{
if (lean_obj_tag(v_snd_319_) == 1)
{
if (lean_obj_tag(v_snd_321_) == 1)
{
lean_object* v_val_323_; lean_object* v_val_324_; uint8_t v___x_325_; 
v_val_323_ = lean_ctor_get(v_snd_319_, 0);
v_val_324_ = lean_ctor_get(v_snd_321_, 0);
v___x_325_ = lean_nat_dec_lt(v_val_323_, v_val_324_);
if (v___x_325_ == 0)
{
goto v___jp_302_;
}
else
{
goto v___jp_306_;
}
}
else
{
goto v___jp_302_;
}
}
else
{
goto v___jp_302_;
}
}
v___jp_326_:
{
uint8_t v___x_327_; 
v___x_327_ = lean_unbox(v_fst_318_);
if (v___x_327_ == 0)
{
uint8_t v___x_328_; 
v___x_328_ = lean_unbox(v_fst_320_);
if (v___x_328_ == 1)
{
goto v___jp_306_;
}
else
{
goto v___jp_322_;
}
}
else
{
uint8_t v___x_329_; 
v___x_329_ = lean_unbox(v_fst_320_);
if (v___x_329_ == 0)
{
goto v___jp_302_;
}
else
{
goto v___jp_322_;
}
}
}
}
v___jp_302_:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_k_301_, v___x_303_);
lean_dec(v_k_301_);
v_k_301_ = v___x_304_;
goto _start;
}
v___jp_306_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_array_fswap(v_as_299_, v_i_300_, v_k_301_);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_i_300_, v___x_308_);
lean_dec(v_i_300_);
v___x_310_ = lean_nat_add(v_k_301_, v___x_308_);
lean_dec(v_k_301_);
v_as_299_ = v___x_307_;
v_i_300_ = v___x_309_;
v_k_301_ = v___x_310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(lean_object* v_hi_330_, lean_object* v_pivot_331_, lean_object* v_as_332_, lean_object* v_i_333_, lean_object* v_k_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_330_, v_pivot_331_, v_as_332_, v_i_333_, v_k_334_);
lean_dec_ref(v_pivot_331_);
lean_dec(v_hi_330_);
return v_res_335_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(uint8_t v___x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_fst_339_; lean_object* v_fst_340_; lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v_fst_343_; lean_object* v_snd_344_; 
v_fst_339_ = lean_ctor_get(v_x_337_, 0);
v_fst_340_ = lean_ctor_get(v_x_338_, 0);
v_fst_341_ = lean_ctor_get(v_fst_339_, 0);
v_snd_342_ = lean_ctor_get(v_fst_339_, 1);
v_fst_343_ = lean_ctor_get(v_fst_340_, 0);
v_snd_344_ = lean_ctor_get(v_fst_340_, 1);
if (lean_obj_tag(v_snd_342_) == 0)
{
if (lean_obj_tag(v_snd_344_) == 1)
{
uint8_t v___x_357_; 
v___x_357_ = 0;
return v___x_357_;
}
else
{
goto v___jp_351_;
}
}
else
{
if (lean_obj_tag(v_snd_344_) == 0)
{
return v___x_336_;
}
else
{
goto v___jp_351_;
}
}
v___jp_345_:
{
if (lean_obj_tag(v_snd_342_) == 1)
{
if (lean_obj_tag(v_snd_344_) == 1)
{
lean_object* v_val_346_; lean_object* v_val_347_; uint8_t v___x_348_; 
v_val_346_ = lean_ctor_get(v_snd_342_, 0);
v_val_347_ = lean_ctor_get(v_snd_344_, 0);
v___x_348_ = lean_nat_dec_lt(v_val_346_, v_val_347_);
return v___x_348_;
}
else
{
uint8_t v___x_349_; 
v___x_349_ = 0;
return v___x_349_;
}
}
else
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
v___jp_351_:
{
uint8_t v___x_352_; 
v___x_352_ = lean_unbox(v_fst_341_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
v___x_353_ = lean_unbox(v_fst_343_);
if (v___x_353_ == 1)
{
uint8_t v___x_354_; 
v___x_354_ = lean_unbox(v_fst_343_);
return v___x_354_;
}
else
{
goto v___jp_345_;
}
}
else
{
uint8_t v___x_355_; 
v___x_355_ = lean_unbox(v_fst_343_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
v___x_356_ = lean_unbox(v_fst_343_);
return v___x_356_;
}
else
{
goto v___jp_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0___boxed(lean_object* v___x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
uint8_t v___x_2350__boxed_361_; uint8_t v_res_362_; lean_object* v_r_363_; 
v___x_2350__boxed_361_ = lean_unbox(v___x_358_);
v_res_362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_2350__boxed_361_, v_x_359_, v_x_360_);
lean_dec_ref(v_x_360_);
lean_dec_ref(v_x_359_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(lean_object* v_n_364_, lean_object* v_as_365_, lean_object* v_lo_366_, lean_object* v_hi_367_){
_start:
{
lean_object* v___y_369_; uint8_t v___x_379_; 
v___x_379_ = lean_nat_dec_lt(v_lo_366_, v_hi_367_);
if (v___x_379_ == 0)
{
lean_dec(v_lo_366_);
return v_as_365_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_mid_382_; lean_object* v___y_384_; lean_object* v___y_390_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_380_ = lean_nat_add(v_lo_366_, v_hi_367_);
v___x_381_ = lean_unsigned_to_nat(1u);
v_mid_382_ = lean_nat_shiftr(v___x_380_, v___x_381_);
lean_dec(v___x_380_);
v___x_395_ = lean_array_fget_borrowed(v_as_365_, v_mid_382_);
v___x_396_ = lean_array_fget_borrowed(v_as_365_, v_lo_366_);
v___x_397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_379_, v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
v___y_390_ = v_as_365_;
goto v___jp_389_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_array_fswap(v_as_365_, v_lo_366_, v_mid_382_);
v___y_390_ = v___x_398_;
goto v___jp_389_;
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_385_ = lean_array_fget_borrowed(v___y_384_, v_mid_382_);
v___x_386_ = lean_array_fget_borrowed(v___y_384_, v_hi_367_);
v___x_387_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_379_, v___x_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_dec(v_mid_382_);
v___y_369_ = v___y_384_;
goto v___jp_368_;
}
else
{
lean_object* v___x_388_; 
v___x_388_ = lean_array_fswap(v___y_384_, v_mid_382_, v_hi_367_);
lean_dec(v_mid_382_);
v___y_369_ = v___x_388_;
goto v___jp_368_;
}
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_array_fget_borrowed(v___y_390_, v_hi_367_);
v___x_392_ = lean_array_fget_borrowed(v___y_390_, v_lo_366_);
v___x_393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_379_, v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
v___y_384_ = v___y_390_;
goto v___jp_383_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_array_fswap(v___y_390_, v_lo_366_, v_hi_367_);
v___y_384_ = v___x_394_;
goto v___jp_383_;
}
}
}
v___jp_368_:
{
lean_object* v_pivot_370_; lean_object* v___x_371_; lean_object* v_fst_372_; lean_object* v_snd_373_; uint8_t v___x_374_; 
v_pivot_370_ = lean_array_fget(v___y_369_, v_hi_367_);
lean_inc_n(v_lo_366_, 2);
v___x_371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_367_, v_pivot_370_, v___y_369_, v_lo_366_, v_lo_366_);
lean_dec(v_pivot_370_);
v_fst_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_fst_372_);
v_snd_373_ = lean_ctor_get(v___x_371_, 1);
lean_inc(v_snd_373_);
lean_dec_ref(v___x_371_);
v___x_374_ = lean_nat_dec_le(v_hi_367_, v_fst_372_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_364_, v_snd_373_, v_lo_366_, v_fst_372_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_fst_372_, v___x_376_);
lean_dec(v_fst_372_);
v_as_365_ = v___x_375_;
v_lo_366_ = v___x_377_;
goto _start;
}
else
{
lean_dec(v_fst_372_);
lean_dec(v_lo_366_);
return v_snd_373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(lean_object* v_n_399_, lean_object* v_as_400_, lean_object* v_lo_401_, lean_object* v_hi_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_399_, v_as_400_, v_lo_401_, v_hi_402_);
lean_dec(v_hi_402_);
lean_dec(v_n_399_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
return v_x_404_;
}
else
{
lean_object* v_key_406_; lean_object* v_value_407_; lean_object* v_tail_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_446_; 
v_key_406_ = lean_ctor_get(v_x_405_, 0);
v_value_407_ = lean_ctor_get(v_x_405_, 1);
v_tail_408_ = lean_ctor_get(v_x_405_, 2);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_446_ == 0)
{
v___x_410_ = v_x_405_;
v_isShared_411_ = v_isSharedCheck_446_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_tail_408_);
lean_inc(v_value_407_);
lean_inc(v_key_406_);
lean_dec(v_x_405_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_446_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_fst_412_; lean_object* v_snd_413_; lean_object* v___x_414_; uint64_t v___y_416_; uint64_t v___y_417_; uint64_t v___y_437_; uint8_t v___x_443_; 
v_fst_412_ = lean_ctor_get(v_key_406_, 0);
v_snd_413_ = lean_ctor_get(v_key_406_, 1);
v___x_414_ = lean_array_get_size(v_x_404_);
v___x_443_ = lean_unbox(v_fst_412_);
if (v___x_443_ == 0)
{
uint64_t v___x_444_; 
v___x_444_ = 13ULL;
v___y_437_ = v___x_444_;
goto v___jp_436_;
}
else
{
uint64_t v___x_445_; 
v___x_445_ = 11ULL;
v___y_437_ = v___x_445_;
goto v___jp_436_;
}
v___jp_415_:
{
uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v_fold_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_418_ = lean_uint64_mix_hash(v___y_416_, v___y_417_);
v___x_419_ = 32ULL;
v___x_420_ = lean_uint64_shift_right(v___x_418_, v___x_419_);
v_fold_421_ = lean_uint64_xor(v___x_418_, v___x_420_);
v___x_422_ = 16ULL;
v___x_423_ = lean_uint64_shift_right(v_fold_421_, v___x_422_);
v___x_424_ = lean_uint64_xor(v_fold_421_, v___x_423_);
v___x_425_ = lean_uint64_to_usize(v___x_424_);
v___x_426_ = lean_usize_of_nat(v___x_414_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_sub(v___x_426_, v___x_427_);
v___x_429_ = lean_usize_land(v___x_425_, v___x_428_);
v___x_430_ = lean_array_uget_borrowed(v_x_404_, v___x_429_);
lean_inc(v___x_430_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 2, v___x_430_);
v___x_432_ = v___x_410_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_key_406_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_value_407_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v___x_430_);
v___x_432_ = v_reuseFailAlloc_435_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; 
v___x_433_ = lean_array_uset(v_x_404_, v___x_429_, v___x_432_);
v_x_404_ = v___x_433_;
v_x_405_ = v_tail_408_;
goto _start;
}
}
v___jp_436_:
{
if (lean_obj_tag(v_snd_413_) == 0)
{
uint64_t v___x_438_; 
v___x_438_ = 11ULL;
v___y_416_ = v___y_437_;
v___y_417_ = v___x_438_;
goto v___jp_415_;
}
else
{
lean_object* v_val_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; 
v_val_439_ = lean_ctor_get(v_snd_413_, 0);
v___x_440_ = l_String_instHashableRaw_hash(v_val_439_);
v___x_441_ = 13ULL;
v___x_442_ = lean_uint64_mix_hash(v___x_440_, v___x_441_);
v___y_416_ = v___y_437_;
v___y_417_ = v___x_442_;
goto v___jp_415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_i_447_, lean_object* v_source_448_, lean_object* v_target_449_){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_array_get_size(v_source_448_);
v___x_451_ = lean_nat_dec_lt(v_i_447_, v___x_450_);
if (v___x_451_ == 0)
{
lean_dec_ref(v_source_448_);
lean_dec(v_i_447_);
return v_target_449_;
}
else
{
lean_object* v_es_452_; lean_object* v___x_453_; lean_object* v_source_454_; lean_object* v_target_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_es_452_ = lean_array_fget(v_source_448_, v_i_447_);
v___x_453_ = lean_box(0);
v_source_454_ = lean_array_fset(v_source_448_, v_i_447_, v___x_453_);
v_target_455_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_target_449_, v_es_452_);
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v_i_447_, v___x_456_);
lean_dec(v_i_447_);
v_i_447_ = v___x_457_;
v_source_448_ = v_source_454_;
v_target_449_ = v_target_455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(lean_object* v_data_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_nbuckets_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_460_ = lean_array_get_size(v_data_459_);
v___x_461_ = lean_unsigned_to_nat(2u);
v_nbuckets_462_ = lean_nat_mul(v___x_460_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_box(0);
v___x_465_ = lean_mk_array(v_nbuckets_462_, v___x_464_);
v___x_466_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v___x_463_, v_data_459_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
if (lean_obj_tag(v_x_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 1;
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
else
{
if (lean_obj_tag(v_x_468_) == 0)
{
uint8_t v___x_471_; 
v___x_471_ = 0;
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v_val_473_; uint8_t v___x_474_; 
v_val_472_ = lean_ctor_get(v_x_467_, 0);
v_val_473_ = lean_ctor_get(v_x_468_, 0);
v___x_474_ = lean_nat_dec_eq(v_val_472_, v_val_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_475_, v_x_476_);
lean_dec(v_x_476_);
lean_dec(v_x_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
else
{
lean_object* v_key_482_; lean_object* v_tail_483_; lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v_fst_486_; lean_object* v_snd_487_; uint8_t v___x_491_; 
v_key_482_ = lean_ctor_get(v_x_480_, 0);
v_tail_483_ = lean_ctor_get(v_x_480_, 2);
v_fst_484_ = lean_ctor_get(v_key_482_, 0);
v_snd_485_ = lean_ctor_get(v_key_482_, 1);
v_fst_486_ = lean_ctor_get(v_a_479_, 0);
v_snd_487_ = lean_ctor_get(v_a_479_, 1);
v___x_491_ = lean_unbox(v_fst_484_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
v___x_492_ = lean_unbox(v_fst_486_);
if (v___x_492_ == 0)
{
goto v___jp_488_;
}
else
{
v_x_480_ = v_tail_483_;
goto _start;
}
}
else
{
uint8_t v___x_494_; 
v___x_494_ = lean_unbox(v_fst_486_);
if (v___x_494_ == 0)
{
v_x_480_ = v_tail_483_;
goto _start;
}
else
{
goto v___jp_488_;
}
}
v___jp_488_:
{
uint8_t v___x_489_; 
v___x_489_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_485_, v_snd_487_);
if (v___x_489_ == 0)
{
v_x_480_ = v_tail_483_;
goto _start;
}
else
{
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_496_, v_x_497_);
lean_dec(v_x_497_);
lean_dec_ref(v_a_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_a_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___y_505_; 
if (lean_obj_tag(v_x_503_) == 0)
{
lean_object* v___x_508_; 
v___x_508_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___y_505_ = v___x_508_;
goto v___jp_504_;
}
else
{
lean_object* v_val_509_; 
v_val_509_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_val_509_);
lean_dec_ref(v_x_503_);
v___y_505_ = v_val_509_;
goto v___jp_504_;
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_array_push(v___y_505_, v_a_502_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_val_515_; lean_object* v___x_516_; 
v___x_513_ = lean_box(0);
v___x_514_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_510_, v___x_513_);
v_val_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_val_515_);
lean_dec(v___x_514_);
v___x_516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_516_, 0, v_a_511_);
lean_ctor_set(v___x_516_, 1, v_val_515_);
lean_ctor_set(v___x_516_, 2, v_x_512_);
return v___x_516_;
}
else
{
lean_object* v_key_517_; lean_object* v_value_518_; lean_object* v_tail_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_541_; 
v_key_517_ = lean_ctor_get(v_x_512_, 0);
v_value_518_ = lean_ctor_get(v_x_512_, 1);
v_tail_519_ = lean_ctor_get(v_x_512_, 2);
v_isSharedCheck_541_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_541_ == 0)
{
v___x_521_ = v_x_512_;
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_tail_519_);
lean_inc(v_value_518_);
lean_inc(v_key_517_);
lean_dec(v_x_512_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_fst_528_; lean_object* v_snd_529_; lean_object* v_fst_530_; lean_object* v_snd_531_; uint8_t v___x_538_; 
v_fst_528_ = lean_ctor_get(v_key_517_, 0);
v_snd_529_ = lean_ctor_get(v_key_517_, 1);
v_fst_530_ = lean_ctor_get(v_a_511_, 0);
v_snd_531_ = lean_ctor_get(v_a_511_, 1);
v___x_538_ = lean_unbox(v_fst_528_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; 
v___x_539_ = lean_unbox(v_fst_530_);
if (v___x_539_ == 0)
{
goto v___jp_532_;
}
else
{
goto v___jp_523_;
}
}
else
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_fst_530_);
if (v___x_540_ == 0)
{
goto v___jp_523_;
}
else
{
goto v___jp_532_;
}
}
v___jp_523_:
{
lean_object* v_tail_524_; lean_object* v___x_526_; 
v_tail_524_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_510_, v_a_511_, v_tail_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 2, v_tail_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_key_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_value_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_tail_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
v___jp_532_:
{
uint8_t v___x_533_; 
v___x_533_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_529_, v_snd_531_);
if (v___x_533_ == 0)
{
goto v___jp_523_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_val_536_; lean_object* v___x_537_; 
lean_del_object(v___x_521_);
lean_dec(v_key_517_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_value_518_);
v___x_535_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_510_, v___x_534_);
v_val_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_val_536_);
lean_dec(v___x_535_);
v___x_537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_537_, 0, v_a_511_);
lean_ctor_set(v___x_537_, 1, v_val_536_);
lean_ctor_set(v___x_537_, 2, v_tail_519_);
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(lean_object* v_a_542_, lean_object* v_m_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___y_546_; lean_object* v___y_547_; size_t v___y_548_; lean_object* v___y_549_; lean_object* v_size_552_; lean_object* v_buckets_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_612_; 
v_size_552_ = lean_ctor_get(v_m_543_, 0);
v_buckets_553_ = lean_ctor_get(v_m_543_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_m_543_);
if (v_isSharedCheck_612_ == 0)
{
v___x_555_ = v_m_543_;
v_isShared_556_ = v_isSharedCheck_612_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_buckets_553_);
lean_inc(v_size_552_);
lean_dec(v_m_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_612_;
goto v_resetjp_554_;
}
v___jp_545_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_array_uset(v___y_547_, v___y_548_, v___y_546_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___y_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
return v___x_551_;
}
v_resetjp_554_:
{
lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___x_559_; uint64_t v___y_561_; uint64_t v___y_562_; uint64_t v___y_603_; uint8_t v___x_609_; 
v_fst_557_ = lean_ctor_get(v_a_544_, 0);
v_snd_558_ = lean_ctor_get(v_a_544_, 1);
v___x_559_ = lean_array_get_size(v_buckets_553_);
v___x_609_ = lean_unbox(v_fst_557_);
if (v___x_609_ == 0)
{
uint64_t v___x_610_; 
v___x_610_ = 13ULL;
v___y_603_ = v___x_610_;
goto v___jp_602_;
}
else
{
uint64_t v___x_611_; 
v___x_611_ = 11ULL;
v___y_603_ = v___x_611_;
goto v___jp_602_;
}
v___jp_560_:
{
uint64_t v___x_563_; uint64_t v___x_564_; uint64_t v___x_565_; uint64_t v_fold_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v_bkt_575_; uint8_t v___x_576_; 
v___x_563_ = lean_uint64_mix_hash(v___y_561_, v___y_562_);
v___x_564_ = 32ULL;
v___x_565_ = lean_uint64_shift_right(v___x_563_, v___x_564_);
v_fold_566_ = lean_uint64_xor(v___x_563_, v___x_565_);
v___x_567_ = 16ULL;
v___x_568_ = lean_uint64_shift_right(v_fold_566_, v___x_567_);
v___x_569_ = lean_uint64_xor(v_fold_566_, v___x_568_);
v___x_570_ = lean_uint64_to_usize(v___x_569_);
v___x_571_ = lean_usize_of_nat(v___x_559_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_sub(v___x_571_, v___x_572_);
v___x_574_ = lean_usize_land(v___x_570_, v___x_573_);
v_bkt_575_ = lean_array_uget_borrowed(v_buckets_553_, v___x_574_);
v___x_576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_544_, v_bkt_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_size_x27_580_; lean_object* v___x_581_; lean_object* v_buckets_x27_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_577_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___x_578_ = lean_array_push(v___x_577_, v_a_542_);
v___x_579_ = lean_unsigned_to_nat(1u);
v_size_x27_580_ = lean_nat_add(v_size_552_, v___x_579_);
lean_dec(v_size_552_);
lean_inc(v_bkt_575_);
v___x_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_581_, 0, v_a_544_);
lean_ctor_set(v___x_581_, 1, v___x_578_);
lean_ctor_set(v___x_581_, 2, v_bkt_575_);
v_buckets_x27_582_ = lean_array_uset(v_buckets_553_, v___x_574_, v___x_581_);
v___x_583_ = lean_unsigned_to_nat(4u);
v___x_584_ = lean_nat_mul(v_size_x27_580_, v___x_583_);
v___x_585_ = lean_unsigned_to_nat(3u);
v___x_586_ = lean_nat_div(v___x_584_, v___x_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_array_get_size(v_buckets_x27_582_);
v___x_588_ = lean_nat_dec_le(v___x_586_, v___x_587_);
lean_dec(v___x_586_);
if (v___x_588_ == 0)
{
lean_object* v_val_589_; lean_object* v___x_591_; 
v_val_589_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_buckets_x27_582_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v_val_589_);
lean_ctor_set(v___x_555_, 0, v_size_x27_580_);
v___x_591_ = v___x_555_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_size_x27_580_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_val_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v___x_594_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v_buckets_x27_582_);
lean_ctor_set(v___x_555_, 0, v_size_x27_580_);
v___x_594_ = v___x_555_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_size_x27_580_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_buckets_x27_582_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v___x_596_; lean_object* v_buckets_x27_597_; lean_object* v_bkt_x27_598_; uint8_t v___x_599_; 
lean_inc(v_bkt_575_);
lean_del_object(v___x_555_);
v___x_596_ = lean_box(0);
v_buckets_x27_597_ = lean_array_uset(v_buckets_553_, v___x_574_, v___x_596_);
lean_inc_ref(v_a_544_);
v_bkt_x27_598_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_542_, v_a_544_, v_bkt_575_);
v___x_599_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_544_, v_bkt_x27_598_);
lean_dec_ref(v_a_544_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_sub(v_size_552_, v___x_600_);
lean_dec(v_size_552_);
v___y_546_ = v_bkt_x27_598_;
v___y_547_ = v_buckets_x27_597_;
v___y_548_ = v___x_574_;
v___y_549_ = v___x_601_;
goto v___jp_545_;
}
else
{
v___y_546_ = v_bkt_x27_598_;
v___y_547_ = v_buckets_x27_597_;
v___y_548_ = v___x_574_;
v___y_549_ = v_size_552_;
goto v___jp_545_;
}
}
}
v___jp_602_:
{
if (lean_obj_tag(v_snd_558_) == 0)
{
uint64_t v___x_604_; 
v___x_604_ = 11ULL;
v___y_561_ = v___y_603_;
v___y_562_ = v___x_604_;
goto v___jp_560_;
}
else
{
lean_object* v_val_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; 
v_val_605_ = lean_ctor_get(v_snd_558_, 0);
v___x_606_ = l_String_instHashableRaw_hash(v_val_605_);
v___x_607_ = 13ULL;
v___x_608_ = lean_uint64_mix_hash(v___x_606_, v___x_607_);
v___y_561_ = v___y_603_;
v___y_562_ = v___x_608_;
goto v___jp_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(lean_object* v_key_613_, lean_object* v_as_614_, size_t v_sz_615_, size_t v_i_616_, lean_object* v_b_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_lt(v_i_616_, v_sz_615_);
if (v___x_618_ == 0)
{
lean_dec_ref(v_key_613_);
return v_b_617_;
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; size_t v___x_622_; size_t v___x_623_; 
v_a_619_ = lean_array_uget_borrowed(v_as_614_, v_i_616_);
lean_inc_ref(v_key_613_);
lean_inc_n(v_a_619_, 2);
v___x_620_ = lean_apply_1(v_key_613_, v_a_619_);
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_619_, v_b_617_, v___x_620_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_616_, v___x_622_);
v_i_616_ = v___x_623_;
v_b_617_ = v___x_621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg___boxed(lean_object* v_key_625_, lean_object* v_as_626_, lean_object* v_sz_627_, lean_object* v_i_628_, lean_object* v_b_629_){
_start:
{
size_t v_sz_boxed_630_; size_t v_i_boxed_631_; lean_object* v_res_632_; 
v_sz_boxed_630_ = lean_unbox_usize(v_sz_627_);
lean_dec(v_sz_627_);
v_i_boxed_631_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_625_, v_as_626_, v_sz_boxed_630_, v_i_boxed_631_, v_b_629_);
lean_dec_ref(v_as_626_);
return v_res_632_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
v___x_634_ = lean_unsigned_to_nat(16u);
v___x_635_ = lean_mk_array(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_groups_638_; 
v___x_636_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0);
v___x_637_ = lean_unsigned_to_nat(0u);
v_groups_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_638_, 0, v___x_637_);
lean_ctor_set(v_groups_638_, 1, v___x_636_);
return v_groups_638_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(lean_object* v_key_639_, lean_object* v_xs_640_){
_start:
{
lean_object* v_groups_641_; size_t v_sz_642_; size_t v___x_643_; lean_object* v___x_644_; 
v_groups_641_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1);
v_sz_642_ = lean_array_size(v_xs_640_);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_639_, v_xs_640_, v_sz_642_, v___x_643_, v_groups_641_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(lean_object* v_key_645_, lean_object* v_xs_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_645_, v_xs_646_);
lean_dec_ref(v_xs_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object* v_items_649_){
_start:
{
lean_object* v___y_651_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_668_; lean_object* v___f_675_; lean_object* v_partitions_676_; lean_object* v_size_677_; lean_object* v_buckets_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___f_675_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0));
v_partitions_676_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v___f_675_, v_items_649_);
v_size_677_ = lean_ctor_get(v_partitions_676_, 0);
lean_inc(v_size_677_);
v_buckets_678_ = lean_ctor_get(v_partitions_676_, 1);
lean_inc_ref(v_buckets_678_);
lean_dec_ref(v_partitions_676_);
v___x_679_ = lean_mk_empty_array_with_capacity(v_size_677_);
lean_dec(v_size_677_);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_get_size(v_buckets_678_);
v___x_682_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_dec_ref(v_buckets_678_);
v___y_668_ = v___x_679_;
goto v___jp_667_;
}
else
{
uint8_t v___x_683_; 
v___x_683_ = lean_nat_dec_le(v___x_681_, v___x_681_);
if (v___x_683_ == 0)
{
if (v___x_682_ == 0)
{
lean_dec_ref(v_buckets_678_);
v___y_668_ = v___x_679_;
goto v___jp_667_;
}
else
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_681_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_678_, v___x_684_, v___x_685_, v___x_679_);
lean_dec_ref(v_buckets_678_);
v___y_668_ = v___x_686_;
goto v___jp_667_;
}
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_681_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_678_, v___x_687_, v___x_688_, v___x_679_);
lean_dec_ref(v_buckets_678_);
v___y_668_ = v___x_689_;
goto v___jp_667_;
}
}
v___jp_650_:
{
size_t v_sz_652_; size_t v___x_653_; lean_object* v___x_654_; 
v_sz_652_ = lean_array_size(v___y_651_);
v___x_653_ = ((size_t)0ULL);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_652_, v___x_653_, v___y_651_);
return v___x_654_;
}
v___jp_655_:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v___y_657_, v___y_656_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec(v___y_657_);
v___y_651_ = v___x_660_;
goto v___jp_650_;
}
v___jp_661_:
{
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_le(v___y_665_, v___y_664_);
if (v___x_666_ == 0)
{
lean_dec(v___y_664_);
lean_inc(v___y_665_);
v___y_656_ = v___y_662_;
v___y_657_ = v___y_663_;
v___y_658_ = v___y_665_;
v___y_659_ = v___y_665_;
goto v___jp_655_;
}
else
{
v___y_656_ = v___y_662_;
v___y_657_ = v___y_663_;
v___y_658_ = v___y_665_;
v___y_659_ = v___y_664_;
goto v___jp_655_;
}
}
v___jp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_array_get_size(v___y_668_);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_nat_dec_eq(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_sub(v___x_669_, v___x_672_);
v___x_674_ = lean_nat_dec_le(v___x_670_, v___x_673_);
if (v___x_674_ == 0)
{
lean_inc(v___x_673_);
v___y_662_ = v___y_668_;
v___y_663_ = v___x_669_;
v___y_664_ = v___x_673_;
v___y_665_ = v___x_673_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___y_668_;
v___y_663_ = v___x_669_;
v___y_664_ = v___x_673_;
v___y_665_ = v___x_670_;
goto v___jp_661_;
}
}
else
{
v___y_651_ = v___y_668_;
goto v___jp_650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object* v_items_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_690_);
lean_dec_ref(v_items_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object* v_n_692_, lean_object* v_as_693_, lean_object* v_lo_694_, lean_object* v_hi_695_, lean_object* v_w_696_, lean_object* v_hlo_697_, lean_object* v_hhi_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_692_, v_as_693_, v_lo_694_, v_hi_695_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object* v_n_700_, lean_object* v_as_701_, lean_object* v_lo_702_, lean_object* v_hi_703_, lean_object* v_w_704_, lean_object* v_hlo_705_, lean_object* v_hhi_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_n_700_, v_as_701_, v_lo_702_, v_hi_703_, v_w_704_, v_hlo_705_, v_hhi_706_);
lean_dec(v_hi_703_);
lean_dec(v_n_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object* v_00_u03b2_708_, lean_object* v_key_709_, lean_object* v_xs_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_709_, v_xs_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object* v_00_u03b2_712_, lean_object* v_key_713_, lean_object* v_xs_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_00_u03b2_712_, v_key_713_, v_xs_714_);
lean_dec_ref(v_xs_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object* v_n_716_, lean_object* v_lo_717_, lean_object* v_hi_718_, lean_object* v_hhi_719_, lean_object* v_pivot_720_, lean_object* v_as_721_, lean_object* v_i_722_, lean_object* v_k_723_, lean_object* v_ilo_724_, lean_object* v_ik_725_, lean_object* v_w_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_718_, v_pivot_720_, v_as_721_, v_i_722_, v_k_723_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object* v_n_728_, lean_object* v_lo_729_, lean_object* v_hi_730_, lean_object* v_hhi_731_, lean_object* v_pivot_732_, lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_k_735_, lean_object* v_ilo_736_, lean_object* v_ik_737_, lean_object* v_w_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_n_728_, v_lo_729_, v_hi_730_, v_hhi_731_, v_pivot_732_, v_as_733_, v_i_734_, v_k_735_, v_ilo_736_, v_ik_737_, v_w_738_);
lean_dec_ref(v_pivot_732_);
lean_dec(v_hi_730_);
lean_dec(v_lo_729_);
lean_dec(v_n_728_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(lean_object* v_00_u03b2_740_, lean_object* v_a_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_741_, v_m_742_, v_a_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(lean_object* v_00_u03b2_745_, lean_object* v_key_746_, lean_object* v_as_747_, size_t v_sz_748_, size_t v_i_749_, lean_object* v_b_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_746_, v_as_747_, v_sz_748_, v_i_749_, v_b_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(lean_object* v_00_u03b2_752_, lean_object* v_key_753_, lean_object* v_as_754_, lean_object* v_sz_755_, lean_object* v_i_756_, lean_object* v_b_757_){
_start:
{
size_t v_sz_boxed_758_; size_t v_i_boxed_759_; lean_object* v_res_760_; 
v_sz_boxed_758_ = lean_unbox_usize(v_sz_755_);
lean_dec(v_sz_755_);
v_i_boxed_759_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(v_00_u03b2_752_, v_key_753_, v_as_754_, v_sz_boxed_758_, v_i_boxed_759_, v_b_757_);
lean_dec_ref(v_as_754_);
return v_res_760_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_761_, lean_object* v_a_762_, lean_object* v_x_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_765_, lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(v_00_u03b2_765_, v_a_766_, v_x_767_);
lean_dec(v_x_767_);
lean_dec_ref(v_a_766_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_770_, lean_object* v_data_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_data_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_774_, v_a_775_, v_x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_778_, lean_object* v_i_779_, lean_object* v_source_780_, lean_object* v_target_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v_i_779_, v_source_780_, v_target_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_x_784_, v_x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object* v_fileMap_787_, lean_object* v_hoverPos_788_, lean_object* v_cmdStx_789_, lean_object* v_infoTree_790_){
_start:
{
lean_object* v___x_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v___x_791_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_787_, v_hoverPos_788_, v_cmdStx_789_, v_infoTree_790_);
v_fst_792_ = lean_ctor_get(v___x_791_, 0);
v_snd_793_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_partitions_799_; lean_object* v___x_801_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Array_zipIdx___redArg(v_fst_792_, v___x_797_);
lean_dec(v_fst_792_);
v_partitions_799_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_798_);
lean_dec_ref(v___x_798_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_partitions_799_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_partitions_799_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_793_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
lean_object* runtime_initialize_Lean_Server_Completion_SyntheticCompletion(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
