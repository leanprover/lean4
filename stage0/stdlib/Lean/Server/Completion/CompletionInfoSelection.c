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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_size_x3f(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_occursInOrOnBoundary(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
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
lean_object* v_i_170_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_193_; uint8_t v___x_198_; 
v_i_170_ = lean_ctor_get(v_info_168_, 0);
lean_inc_ref_n(v_i_170_, 2);
v___x_198_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_165_, v_i_170_);
if (v___x_198_ == 0)
{
lean_dec_ref_known(v_info_168_, 1);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
lean_dec_ref(v_fileMap_164_);
return v_best_169_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_Info_pos_x3f(v_info_168_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_201_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_200_);
v___y_193_ = v___x_201_;
goto v___jp_192_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_199_, 1);
v___y_193_ = v_val_202_;
goto v___jp_192_;
}
}
v___jp_171_:
{
lean_object* v___x_175_; lean_object* v_line_176_; lean_object* v___x_177_; lean_object* v_line_178_; uint8_t v___x_179_; 
lean_inc_ref(v_fileMap_164_);
v___x_175_ = l_Lean_FileMap_toPosition(v_fileMap_164_, v___y_173_);
lean_dec(v___y_173_);
v_line_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_line_176_);
lean_dec_ref(v___x_175_);
v___x_177_ = l_Lean_FileMap_toPosition(v_fileMap_164_, v___y_172_);
lean_dec(v___y_172_);
v_line_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_line_178_);
lean_dec_ref(v___x_177_);
v___x_179_ = lean_nat_dec_eq(v_line_176_, v_hoverLine_166_);
if (v___x_179_ == 0)
{
lean_dec(v_line_178_);
lean_dec(v_line_176_);
lean_dec(v___y_174_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
return v_best_169_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = lean_nat_dec_eq(v_line_176_, v_line_178_);
lean_dec(v_line_178_);
lean_dec(v_line_176_);
if (v___x_180_ == 0)
{
lean_dec(v___y_174_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
return v_best_169_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_181_, 0, v___y_174_);
lean_ctor_set(v___x_181_, 1, v_ctx_167_);
lean_ctor_set(v___x_181_, 2, v_i_170_);
v___x_182_ = lean_array_push(v_best_169_, v___x_181_);
return v___x_182_;
}
}
}
v___jp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_hoverPos_165_, v___x_186_);
v___x_188_ = lean_nat_dec_le(v___x_187_, v___y_185_);
lean_dec(v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
v___y_172_ = v___y_185_;
v___y_173_ = v___y_184_;
v___y_174_ = v___x_189_;
goto v___jp_171_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_nat_sub(v_hoverPos_165_, v___y_184_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
v___y_172_ = v___y_185_;
v___y_173_ = v___y_184_;
v___y_174_ = v___x_191_;
goto v___jp_171_;
}
}
v___jp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Elab_Info_tailPos_x3f(v_info_168_);
lean_dec_ref_known(v_info_168_, 1);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_196_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_195_);
v___y_184_ = v___y_193_;
v___y_185_ = v___x_196_;
goto v___jp_183_;
}
else
{
lean_object* v_val_197_; 
v_val_197_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_194_, 1);
v___y_184_ = v___y_193_;
v___y_185_ = v_val_197_;
goto v___jp_183_;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed(lean_object* v_fileMap_203_, lean_object* v_hoverPos_204_, lean_object* v_hoverLine_205_, lean_object* v_ctx_206_, lean_object* v_info_207_, lean_object* v_best_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(v_fileMap_203_, v_hoverPos_204_, v_hoverLine_205_, v_ctx_206_, v_info_207_, v_best_208_);
lean_dec(v_hoverLine_205_);
lean_dec(v_hoverPos_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object* v_fileMap_210_, lean_object* v_hoverPos_211_, lean_object* v_cmdStx_212_, lean_object* v_infoTree_213_){
_start:
{
uint8_t v_isComplete_215_; lean_object* v_completionInfoCandidates_216_; lean_object* v___x_220_; lean_object* v_line_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_completionInfoCandidates_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
lean_inc_ref_n(v_fileMap_210_, 2);
v___x_220_ = l_Lean_FileMap_toPosition(v_fileMap_210_, v_hoverPos_211_);
v_line_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_line_221_);
lean_dec_ref(v___x_220_);
lean_inc(v_hoverPos_211_);
v___x_222_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed), 6, 3);
lean_closure_set(v___x_222_, 0, v_fileMap_210_);
lean_closure_set(v___x_222_, 1, v_hoverPos_211_);
lean_closure_set(v___x_222_, 2, v_line_221_);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
lean_inc_ref(v_infoTree_213_);
v_completionInfoCandidates_225_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___x_222_, v___x_224_, v_infoTree_213_);
v___x_226_ = lean_array_get_size(v_completionInfoCandidates_225_);
v___x_227_ = lean_nat_dec_eq(v___x_226_, v___x_223_);
if (v___x_227_ == 0)
{
uint8_t v_isComplete_228_; 
lean_dec_ref(v_infoTree_213_);
lean_dec(v_cmdStx_212_);
lean_dec(v_hoverPos_211_);
lean_dec_ref(v_fileMap_210_);
v_isComplete_228_ = 1;
v_isComplete_215_ = v_isComplete_228_;
v_completionInfoCandidates_216_ = v_completionInfoCandidates_225_;
goto v___jp_214_;
}
else
{
lean_object* v_completionInfoCandidates_229_; uint8_t v_isComplete_230_; 
lean_dec(v_completionInfoCandidates_225_);
v_completionInfoCandidates_229_ = l_Lean_Server_Completion_findSyntheticCompletions(v_fileMap_210_, v_hoverPos_211_, v_cmdStx_212_, v_infoTree_213_);
v_isComplete_230_ = 0;
v_isComplete_215_ = v_isComplete_230_;
v_completionInfoCandidates_216_ = v_completionInfoCandidates_229_;
goto v___jp_214_;
}
v___jp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_completionInfoCandidates_216_);
lean_dec_ref(v_completionInfoCandidates_216_);
v___x_218_ = lean_box(v_isComplete_215_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(lean_object* v_x_231_){
_start:
{
lean_object* v_fst_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_247_; 
v_fst_232_ = lean_ctor_get(v_x_231_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v_x_231_, 1);
lean_dec(v_unused_248_);
v___x_234_ = v_x_231_;
v_isShared_235_ = v_isSharedCheck_247_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_fst_232_);
lean_dec(v_x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_247_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_info_236_; uint8_t v___y_238_; 
v_info_236_ = lean_ctor_get(v_fst_232_, 2);
lean_inc_ref(v_info_236_);
lean_dec(v_fst_232_);
if (lean_obj_tag(v_info_236_) == 1)
{
uint8_t v___x_245_; 
v___x_245_ = 1;
v___y_238_ = v___x_245_;
goto v___jp_237_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
v___y_238_ = v___x_246_;
goto v___jp_237_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v_size_x3f_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_239_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_239_, 0, v_info_236_);
v_size_x3f_240_ = l_Lean_Elab_Info_size_x3f(v___x_239_);
lean_dec_ref_known(v___x_239_, 1);
v___x_241_ = lean_box(v___y_238_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v_size_x3f_240_);
lean_ctor_set(v___x_234_, 0, v___x_241_);
v___x_243_ = v___x_234_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_size_x3f_240_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
return v_x_249_;
}
else
{
lean_object* v_key_251_; lean_object* v_value_252_; lean_object* v_tail_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_key_251_ = lean_ctor_get(v_x_250_, 0);
v_value_252_ = lean_ctor_get(v_x_250_, 1);
v_tail_253_ = lean_ctor_get(v_x_250_, 2);
lean_inc(v_value_252_);
lean_inc(v_key_251_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_key_251_);
lean_ctor_set(v___x_254_, 1, v_value_252_);
v___x_255_ = lean_array_push(v_x_249_, v___x_254_);
v_x_249_ = v___x_255_;
v_x_250_ = v_tail_253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_x_257_, v_x_258_);
lean_dec(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(lean_object* v_as_260_, size_t v_i_261_, size_t v_stop_262_, lean_object* v_b_263_){
_start:
{
uint8_t v___x_264_; 
v___x_264_ = lean_usize_dec_eq(v_i_261_, v_stop_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; size_t v___x_267_; size_t v___x_268_; 
v___x_265_ = lean_array_uget_borrowed(v_as_260_, v_i_261_);
v___x_266_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_b_263_, v___x_265_);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_add(v_i_261_, v___x_267_);
v_i_261_ = v___x_268_;
v_b_263_ = v___x_266_;
goto _start;
}
else
{
return v_b_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4___boxed(lean_object* v_as_270_, lean_object* v_i_271_, lean_object* v_stop_272_, lean_object* v_b_273_){
_start:
{
size_t v_i_boxed_274_; size_t v_stop_boxed_275_; lean_object* v_res_276_; 
v_i_boxed_274_ = lean_unbox_usize(v_i_271_);
lean_dec(v_i_271_);
v_stop_boxed_275_ = lean_unbox_usize(v_stop_272_);
lean_dec(v_stop_272_);
v_res_276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_270_, v_i_boxed_274_, v_stop_boxed_275_, v_b_273_);
lean_dec_ref(v_as_270_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t v_sz_277_, size_t v_i_278_, lean_object* v_bs_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_usize_dec_lt(v_i_278_, v_sz_277_);
if (v___x_280_ == 0)
{
return v_bs_279_;
}
else
{
lean_object* v_v_281_; lean_object* v_snd_282_; lean_object* v___x_283_; lean_object* v_bs_x27_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v_v_281_ = lean_array_uget_borrowed(v_bs_279_, v_i_278_);
v_snd_282_ = lean_ctor_get(v_v_281_, 1);
lean_inc(v_snd_282_);
v___x_283_ = lean_unsigned_to_nat(0u);
v_bs_x27_284_ = lean_array_uset(v_bs_279_, v_i_278_, v___x_283_);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_add(v_i_278_, v___x_285_);
v___x_287_ = lean_array_uset(v_bs_x27_284_, v_i_278_, v_snd_282_);
v_i_278_ = v___x_286_;
v_bs_279_ = v___x_287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object* v_sz_289_, lean_object* v_i_290_, lean_object* v_bs_291_){
_start:
{
size_t v_sz_boxed_292_; size_t v_i_boxed_293_; lean_object* v_res_294_; 
v_sz_boxed_292_ = lean_unbox_usize(v_sz_289_);
lean_dec(v_sz_289_);
v_i_boxed_293_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_res_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_292_, v_i_boxed_293_, v_bs_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object* v_hi_295_, lean_object* v_pivot_296_, lean_object* v_as_297_, lean_object* v_i_298_, lean_object* v_k_299_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = lean_nat_dec_lt(v_k_299_, v_hi_295_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_k_299_);
v___x_311_ = lean_array_fswap(v_as_297_, v_i_298_, v_hi_295_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_i_298_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v_fst_314_; lean_object* v_fst_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; 
v___x_313_ = lean_array_fget_borrowed(v_as_297_, v_k_299_);
v_fst_314_ = lean_ctor_get(v___x_313_, 0);
v_fst_315_ = lean_ctor_get(v_pivot_296_, 0);
v_fst_316_ = lean_ctor_get(v_fst_314_, 0);
v_snd_317_ = lean_ctor_get(v_fst_314_, 1);
v_fst_318_ = lean_ctor_get(v_fst_315_, 0);
v_snd_319_ = lean_ctor_get(v_fst_315_, 1);
if (lean_obj_tag(v_snd_317_) == 0)
{
if (lean_obj_tag(v_snd_319_) == 1)
{
goto v___jp_300_;
}
else
{
goto v___jp_326_;
}
}
else
{
if (lean_obj_tag(v_snd_319_) == 0)
{
goto v___jp_304_;
}
else
{
goto v___jp_326_;
}
}
v___jp_320_:
{
if (lean_obj_tag(v_snd_317_) == 1)
{
if (lean_obj_tag(v_snd_319_) == 1)
{
lean_object* v_val_321_; lean_object* v_val_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_val_321_ = lean_ctor_get(v_snd_317_, 0);
v_val_322_ = lean_ctor_get(v_snd_319_, 0);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_add(v_val_321_, v___x_323_);
v___x_325_ = lean_nat_dec_le(v___x_324_, v_val_322_);
lean_dec(v___x_324_);
if (v___x_325_ == 0)
{
goto v___jp_300_;
}
else
{
goto v___jp_304_;
}
}
else
{
goto v___jp_300_;
}
}
else
{
goto v___jp_300_;
}
}
v___jp_326_:
{
uint8_t v___x_327_; 
v___x_327_ = lean_unbox(v_fst_316_);
if (v___x_327_ == 0)
{
uint8_t v___x_328_; 
v___x_328_ = lean_unbox(v_fst_318_);
if (v___x_328_ == 1)
{
goto v___jp_304_;
}
else
{
goto v___jp_320_;
}
}
else
{
uint8_t v___x_329_; 
v___x_329_ = lean_unbox(v_fst_318_);
if (v___x_329_ == 0)
{
goto v___jp_300_;
}
else
{
goto v___jp_320_;
}
}
}
}
v___jp_300_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_k_299_, v___x_301_);
lean_dec(v_k_299_);
v_k_299_ = v___x_302_;
goto _start;
}
v___jp_304_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = lean_array_fswap(v_as_297_, v_i_298_, v_k_299_);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_i_298_, v___x_306_);
lean_dec(v_i_298_);
v___x_308_ = lean_nat_add(v_k_299_, v___x_306_);
lean_dec(v_k_299_);
v_as_297_ = v___x_305_;
v_i_298_ = v___x_307_;
v_k_299_ = v___x_308_;
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
uint8_t v___x_359_; 
v___x_359_ = 0;
return v___x_359_;
}
else
{
goto v___jp_353_;
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
goto v___jp_353_;
}
}
v___jp_345_:
{
if (lean_obj_tag(v_snd_342_) == 1)
{
if (lean_obj_tag(v_snd_344_) == 1)
{
lean_object* v_val_346_; lean_object* v_val_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_val_346_ = lean_ctor_get(v_snd_342_, 0);
v_val_347_ = lean_ctor_get(v_snd_344_, 0);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_val_346_, v___x_348_);
v___x_350_ = lean_nat_dec_le(v___x_349_, v_val_347_);
lean_dec(v___x_349_);
return v___x_350_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = 0;
return v___x_351_;
}
}
else
{
uint8_t v___x_352_; 
v___x_352_ = 0;
return v___x_352_;
}
}
v___jp_353_:
{
uint8_t v___x_354_; 
v___x_354_ = lean_unbox(v_fst_341_);
if (v___x_354_ == 0)
{
uint8_t v___x_355_; 
v___x_355_ = lean_unbox(v_fst_343_);
if (v___x_355_ == 1)
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
else
{
uint8_t v___x_357_; 
v___x_357_ = lean_unbox(v_fst_343_);
if (v___x_357_ == 0)
{
uint8_t v___x_358_; 
v___x_358_ = lean_unbox(v_fst_343_);
return v___x_358_;
}
else
{
goto v___jp_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0___boxed(lean_object* v___x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v___x_2379__boxed_363_; uint8_t v_res_364_; lean_object* v_r_365_; 
v___x_2379__boxed_363_ = lean_unbox(v___x_360_);
v_res_364_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_2379__boxed_363_, v_x_361_, v_x_362_);
lean_dec_ref(v_x_362_);
lean_dec_ref(v_x_361_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(lean_object* v_n_366_, lean_object* v_as_367_, lean_object* v_lo_368_, lean_object* v_hi_369_){
_start:
{
lean_object* v___y_371_; uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_lt(v_lo_368_, v_hi_369_);
if (v___x_381_ == 0)
{
lean_dec(v_lo_368_);
return v_as_367_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_mid_384_; lean_object* v___y_386_; lean_object* v___y_392_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_382_ = lean_nat_add(v_lo_368_, v_hi_369_);
v___x_383_ = lean_unsigned_to_nat(1u);
v_mid_384_ = lean_nat_shiftr(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
v___x_397_ = lean_array_fget_borrowed(v_as_367_, v_mid_384_);
v___x_398_ = lean_array_fget_borrowed(v_as_367_, v_lo_368_);
v___x_399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_381_, v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
v___y_392_ = v_as_367_;
goto v___jp_391_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_array_fswap(v_as_367_, v_lo_368_, v_mid_384_);
v___y_392_ = v___x_400_;
goto v___jp_391_;
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = lean_array_fget_borrowed(v___y_386_, v_mid_384_);
v___x_388_ = lean_array_fget_borrowed(v___y_386_, v_hi_369_);
v___x_389_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_381_, v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_dec(v_mid_384_);
v___y_371_ = v___y_386_;
goto v___jp_370_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = lean_array_fswap(v___y_386_, v_mid_384_, v_hi_369_);
lean_dec(v_mid_384_);
v___y_371_ = v___x_390_;
goto v___jp_370_;
}
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_array_fget_borrowed(v___y_392_, v_hi_369_);
v___x_394_ = lean_array_fget_borrowed(v___y_392_, v_lo_368_);
v___x_395_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_381_, v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
v___y_386_ = v___y_392_;
goto v___jp_385_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_array_fswap(v___y_392_, v_lo_368_, v_hi_369_);
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
}
}
v___jp_370_:
{
lean_object* v_pivot_372_; lean_object* v___x_373_; lean_object* v_fst_374_; lean_object* v_snd_375_; uint8_t v___x_376_; 
v_pivot_372_ = lean_array_fget(v___y_371_, v_hi_369_);
lean_inc_n(v_lo_368_, 2);
v___x_373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_369_, v_pivot_372_, v___y_371_, v_lo_368_, v_lo_368_);
lean_dec(v_pivot_372_);
v_fst_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_fst_374_);
v_snd_375_ = lean_ctor_get(v___x_373_, 1);
lean_inc(v_snd_375_);
lean_dec_ref(v___x_373_);
v___x_376_ = lean_nat_dec_le(v_hi_369_, v_fst_374_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_366_, v_snd_375_, v_lo_368_, v_fst_374_);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_fst_374_, v___x_378_);
lean_dec(v_fst_374_);
v_as_367_ = v___x_377_;
v_lo_368_ = v___x_379_;
goto _start;
}
else
{
lean_dec(v_fst_374_);
lean_dec(v_lo_368_);
return v_snd_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(lean_object* v_n_401_, lean_object* v_as_402_, lean_object* v_lo_403_, lean_object* v_hi_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_401_, v_as_402_, v_lo_403_, v_hi_404_);
lean_dec(v_hi_404_);
lean_dec(v_n_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
return v_x_406_;
}
else
{
lean_object* v_key_408_; lean_object* v_value_409_; lean_object* v_tail_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_448_; 
v_key_408_ = lean_ctor_get(v_x_407_, 0);
v_value_409_ = lean_ctor_get(v_x_407_, 1);
v_tail_410_ = lean_ctor_get(v_x_407_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_448_ == 0)
{
v___x_412_ = v_x_407_;
v_isShared_413_ = v_isSharedCheck_448_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_tail_410_);
lean_inc(v_value_409_);
lean_inc(v_key_408_);
lean_dec(v_x_407_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_448_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; uint64_t v___y_418_; uint64_t v___y_419_; uint64_t v___y_439_; uint8_t v___x_445_; 
v_fst_414_ = lean_ctor_get(v_key_408_, 0);
v_snd_415_ = lean_ctor_get(v_key_408_, 1);
v___x_416_ = lean_array_get_size(v_x_406_);
v___x_445_ = lean_unbox(v_fst_414_);
if (v___x_445_ == 0)
{
uint64_t v___x_446_; 
v___x_446_ = 13ULL;
v___y_439_ = v___x_446_;
goto v___jp_438_;
}
else
{
uint64_t v___x_447_; 
v___x_447_ = 11ULL;
v___y_439_ = v___x_447_;
goto v___jp_438_;
}
v___jp_417_:
{
uint64_t v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v_fold_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_420_ = lean_uint64_mix_hash(v___y_418_, v___y_419_);
v___x_421_ = 32ULL;
v___x_422_ = lean_uint64_shift_right(v___x_420_, v___x_421_);
v_fold_423_ = lean_uint64_xor(v___x_420_, v___x_422_);
v___x_424_ = 16ULL;
v___x_425_ = lean_uint64_shift_right(v_fold_423_, v___x_424_);
v___x_426_ = lean_uint64_xor(v_fold_423_, v___x_425_);
v___x_427_ = lean_uint64_to_usize(v___x_426_);
v___x_428_ = lean_usize_of_nat(v___x_416_);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_sub(v___x_428_, v___x_429_);
v___x_431_ = lean_usize_land(v___x_427_, v___x_430_);
v___x_432_ = lean_array_uget_borrowed(v_x_406_, v___x_431_);
lean_inc(v___x_432_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 2, v___x_432_);
v___x_434_ = v___x_412_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_key_408_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_value_409_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v___x_432_);
v___x_434_ = v_reuseFailAlloc_437_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_array_uset(v_x_406_, v___x_431_, v___x_434_);
v_x_406_ = v___x_435_;
v_x_407_ = v_tail_410_;
goto _start;
}
}
v___jp_438_:
{
if (lean_obj_tag(v_snd_415_) == 0)
{
uint64_t v___x_440_; 
v___x_440_ = 11ULL;
v___y_418_ = v___y_439_;
v___y_419_ = v___x_440_;
goto v___jp_417_;
}
else
{
lean_object* v_val_441_; uint64_t v___x_442_; uint64_t v___x_443_; uint64_t v___x_444_; 
v_val_441_ = lean_ctor_get(v_snd_415_, 0);
v___x_442_ = l_String_instHashableRaw_hash(v_val_441_);
v___x_443_ = 13ULL;
v___x_444_ = lean_uint64_mix_hash(v___x_442_, v___x_443_);
v___y_418_ = v___y_439_;
v___y_419_ = v___x_444_;
goto v___jp_417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_i_449_, lean_object* v_source_450_, lean_object* v_target_451_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_array_get_size(v_source_450_);
v___x_453_ = lean_nat_dec_lt(v_i_449_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec_ref(v_source_450_);
lean_dec(v_i_449_);
return v_target_451_;
}
else
{
lean_object* v_es_454_; lean_object* v___x_455_; lean_object* v_source_456_; lean_object* v_target_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_es_454_ = lean_array_fget(v_source_450_, v_i_449_);
v___x_455_ = lean_box(0);
v_source_456_ = lean_array_fset(v_source_450_, v_i_449_, v___x_455_);
v_target_457_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_target_451_, v_es_454_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_add(v_i_449_, v___x_458_);
lean_dec(v_i_449_);
v_i_449_ = v___x_459_;
v_source_450_ = v_source_456_;
v_target_451_ = v_target_457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(lean_object* v_data_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_nbuckets_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_462_ = lean_array_get_size(v_data_461_);
v___x_463_ = lean_unsigned_to_nat(2u);
v_nbuckets_464_ = lean_nat_mul(v___x_462_, v___x_463_);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_box(0);
v___x_467_ = lean_mk_array(v_nbuckets_464_, v___x_466_);
v___x_468_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v___x_465_, v_data_461_, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
if (lean_obj_tag(v_x_470_) == 0)
{
uint8_t v___x_471_; 
v___x_471_ = 1;
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = 0;
return v___x_472_;
}
}
else
{
if (lean_obj_tag(v_x_470_) == 0)
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v_val_475_; uint8_t v_decide_476_; 
v_val_474_ = lean_ctor_get(v_x_469_, 0);
v_val_475_ = lean_ctor_get(v_x_470_, 0);
v_decide_476_ = lean_nat_dec_eq(v_val_474_, v_val_475_);
return v_decide_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_477_, v_x_478_);
lean_dec(v_x_478_);
lean_dec(v_x_477_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
else
{
lean_object* v_key_484_; lean_object* v_tail_485_; lean_object* v_fst_486_; lean_object* v_snd_487_; lean_object* v_fst_488_; lean_object* v_snd_489_; uint8_t v___x_493_; 
v_key_484_ = lean_ctor_get(v_x_482_, 0);
v_tail_485_ = lean_ctor_get(v_x_482_, 2);
v_fst_486_ = lean_ctor_get(v_key_484_, 0);
v_snd_487_ = lean_ctor_get(v_key_484_, 1);
v_fst_488_ = lean_ctor_get(v_a_481_, 0);
v_snd_489_ = lean_ctor_get(v_a_481_, 1);
v___x_493_ = lean_unbox(v_fst_488_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = lean_unbox(v_fst_486_);
if (v___x_494_ == 0)
{
goto v___jp_490_;
}
else
{
v_x_482_ = v_tail_485_;
goto _start;
}
}
else
{
uint8_t v___x_496_; 
v___x_496_ = lean_unbox(v_fst_486_);
if (v___x_496_ == 0)
{
v_x_482_ = v_tail_485_;
goto _start;
}
else
{
goto v___jp_490_;
}
}
v___jp_490_:
{
uint8_t v___x_491_; 
v___x_491_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_487_, v_snd_489_);
if (v___x_491_ == 0)
{
v_x_482_ = v_tail_485_;
goto _start;
}
else
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec_ref(v_a_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___y_507_; 
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___y_507_ = v___x_510_;
goto v___jp_506_;
}
else
{
lean_object* v_val_511_; 
v_val_511_ = lean_ctor_get(v_x_505_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_x_505_, 1);
v___y_507_ = v_val_511_;
goto v___jp_506_;
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_array_push(v___y_507_, v_a_504_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_val_517_; lean_object* v___x_518_; 
v___x_515_ = lean_box(0);
v___x_516_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_512_, v___x_515_);
v_val_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_val_517_);
lean_dec(v___x_516_);
v___x_518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_518_, 0, v_a_513_);
lean_ctor_set(v___x_518_, 1, v_val_517_);
lean_ctor_set(v___x_518_, 2, v_x_514_);
return v___x_518_;
}
else
{
lean_object* v_key_519_; lean_object* v_value_520_; lean_object* v_tail_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_543_; 
v_key_519_ = lean_ctor_get(v_x_514_, 0);
v_value_520_ = lean_ctor_get(v_x_514_, 1);
v_tail_521_ = lean_ctor_get(v_x_514_, 2);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_543_ == 0)
{
v___x_523_ = v_x_514_;
v_isShared_524_ = v_isSharedCheck_543_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_tail_521_);
lean_inc(v_value_520_);
lean_inc(v_key_519_);
lean_dec(v_x_514_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_543_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; uint8_t v___x_540_; 
v_fst_530_ = lean_ctor_get(v_key_519_, 0);
v_snd_531_ = lean_ctor_get(v_key_519_, 1);
v_fst_532_ = lean_ctor_get(v_a_513_, 0);
v_snd_533_ = lean_ctor_get(v_a_513_, 1);
v___x_540_ = lean_unbox(v_fst_532_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = lean_unbox(v_fst_530_);
if (v___x_541_ == 0)
{
goto v___jp_534_;
}
else
{
goto v___jp_525_;
}
}
else
{
uint8_t v___x_542_; 
v___x_542_ = lean_unbox(v_fst_530_);
if (v___x_542_ == 0)
{
goto v___jp_525_;
}
else
{
goto v___jp_534_;
}
}
v___jp_525_:
{
lean_object* v_tail_526_; lean_object* v___x_528_; 
v_tail_526_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_512_, v_a_513_, v_tail_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 2, v_tail_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_key_519_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_value_520_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_tail_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
v___jp_534_:
{
uint8_t v___x_535_; 
v___x_535_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_531_, v_snd_533_);
if (v___x_535_ == 0)
{
goto v___jp_525_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_val_538_; lean_object* v___x_539_; 
lean_del_object(v___x_523_);
lean_dec(v_key_519_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_value_520_);
v___x_537_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_512_, v___x_536_);
v_val_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_val_538_);
lean_dec(v___x_537_);
v___x_539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_539_, 0, v_a_513_);
lean_ctor_set(v___x_539_, 1, v_val_538_);
lean_ctor_set(v___x_539_, 2, v_tail_521_);
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(lean_object* v_a_544_, lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
size_t v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v_size_554_; lean_object* v_buckets_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_614_; 
v_size_554_ = lean_ctor_get(v_m_545_, 0);
v_buckets_555_ = lean_ctor_get(v_m_545_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_m_545_);
if (v_isSharedCheck_614_ == 0)
{
v___x_557_ = v_m_545_;
v_isShared_558_ = v_isSharedCheck_614_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_buckets_555_);
lean_inc(v_size_554_);
lean_dec(v_m_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_614_;
goto v_resetjp_556_;
}
v___jp_547_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_array_uset(v___y_549_, v___y_548_, v___y_550_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___y_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
return v___x_553_;
}
v_resetjp_556_:
{
lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_561_; uint64_t v___y_563_; uint64_t v___y_564_; uint64_t v___y_605_; uint8_t v___x_611_; 
v_fst_559_ = lean_ctor_get(v_a_546_, 0);
v_snd_560_ = lean_ctor_get(v_a_546_, 1);
v___x_561_ = lean_array_get_size(v_buckets_555_);
v___x_611_ = lean_unbox(v_fst_559_);
if (v___x_611_ == 0)
{
uint64_t v___x_612_; 
v___x_612_ = 13ULL;
v___y_605_ = v___x_612_;
goto v___jp_604_;
}
else
{
uint64_t v___x_613_; 
v___x_613_ = 11ULL;
v___y_605_ = v___x_613_;
goto v___jp_604_;
}
v___jp_562_:
{
uint64_t v___x_565_; uint64_t v___x_566_; uint64_t v___x_567_; uint64_t v_fold_568_; uint64_t v___x_569_; uint64_t v___x_570_; uint64_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; lean_object* v_bkt_577_; uint8_t v___x_578_; 
v___x_565_ = lean_uint64_mix_hash(v___y_563_, v___y_564_);
v___x_566_ = 32ULL;
v___x_567_ = lean_uint64_shift_right(v___x_565_, v___x_566_);
v_fold_568_ = lean_uint64_xor(v___x_565_, v___x_567_);
v___x_569_ = 16ULL;
v___x_570_ = lean_uint64_shift_right(v_fold_568_, v___x_569_);
v___x_571_ = lean_uint64_xor(v_fold_568_, v___x_570_);
v___x_572_ = lean_uint64_to_usize(v___x_571_);
v___x_573_ = lean_usize_of_nat(v___x_561_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_sub(v___x_573_, v___x_574_);
v___x_576_ = lean_usize_land(v___x_572_, v___x_575_);
v_bkt_577_ = lean_array_uget_borrowed(v_buckets_555_, v___x_576_);
v___x_578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_546_, v_bkt_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_size_x27_582_; lean_object* v___x_583_; lean_object* v_buckets_x27_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_579_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___x_580_ = lean_array_push(v___x_579_, v_a_544_);
v___x_581_ = lean_unsigned_to_nat(1u);
v_size_x27_582_ = lean_nat_add(v_size_554_, v___x_581_);
lean_dec(v_size_554_);
lean_inc(v_bkt_577_);
v___x_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_583_, 0, v_a_546_);
lean_ctor_set(v___x_583_, 1, v___x_580_);
lean_ctor_set(v___x_583_, 2, v_bkt_577_);
v_buckets_x27_584_ = lean_array_uset(v_buckets_555_, v___x_576_, v___x_583_);
v___x_585_ = lean_unsigned_to_nat(4u);
v___x_586_ = lean_nat_mul(v_size_x27_582_, v___x_585_);
v___x_587_ = lean_unsigned_to_nat(3u);
v___x_588_ = lean_nat_div(v___x_586_, v___x_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_array_get_size(v_buckets_x27_584_);
v___x_590_ = lean_nat_dec_le(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
if (v___x_590_ == 0)
{
lean_object* v_val_591_; lean_object* v___x_593_; 
v_val_591_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_buckets_x27_584_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_val_591_);
lean_ctor_set(v___x_557_, 0, v_size_x27_582_);
v___x_593_ = v___x_557_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_size_x27_582_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_val_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_596_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_buckets_x27_584_);
lean_ctor_set(v___x_557_, 0, v_size_x27_582_);
v___x_596_ = v___x_557_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_size_x27_582_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_buckets_x27_584_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v___x_598_; lean_object* v_buckets_x27_599_; lean_object* v_bkt_x27_600_; uint8_t v___x_601_; 
lean_inc(v_bkt_577_);
lean_del_object(v___x_557_);
v___x_598_ = lean_box(0);
v_buckets_x27_599_ = lean_array_uset(v_buckets_555_, v___x_576_, v___x_598_);
lean_inc_ref(v_a_546_);
v_bkt_x27_600_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_544_, v_a_546_, v_bkt_577_);
v___x_601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_546_, v_bkt_x27_600_);
lean_dec_ref(v_a_546_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_sub(v_size_554_, v___x_602_);
lean_dec(v_size_554_);
v___y_548_ = v___x_576_;
v___y_549_ = v_buckets_x27_599_;
v___y_550_ = v_bkt_x27_600_;
v___y_551_ = v___x_603_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___x_576_;
v___y_549_ = v_buckets_x27_599_;
v___y_550_ = v_bkt_x27_600_;
v___y_551_ = v_size_554_;
goto v___jp_547_;
}
}
}
v___jp_604_:
{
if (lean_obj_tag(v_snd_560_) == 0)
{
uint64_t v___x_606_; 
v___x_606_ = 11ULL;
v___y_563_ = v___y_605_;
v___y_564_ = v___x_606_;
goto v___jp_562_;
}
else
{
lean_object* v_val_607_; uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; 
v_val_607_ = lean_ctor_get(v_snd_560_, 0);
v___x_608_ = l_String_instHashableRaw_hash(v_val_607_);
v___x_609_ = 13ULL;
v___x_610_ = lean_uint64_mix_hash(v___x_608_, v___x_609_);
v___y_563_ = v___y_605_;
v___y_564_ = v___x_610_;
goto v___jp_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(lean_object* v_key_615_, lean_object* v_as_616_, size_t v_sz_617_, size_t v_i_618_, lean_object* v_b_619_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_lt(v_i_618_, v_sz_617_);
if (v___x_620_ == 0)
{
lean_dec_ref(v_key_615_);
return v_b_619_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; size_t v___x_624_; size_t v___x_625_; 
v_a_621_ = lean_array_uget_borrowed(v_as_616_, v_i_618_);
lean_inc_ref(v_key_615_);
lean_inc_n(v_a_621_, 2);
v___x_622_ = lean_apply_1(v_key_615_, v_a_621_);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_621_, v_b_619_, v___x_622_);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_i_618_, v___x_624_);
v_i_618_ = v___x_625_;
v_b_619_ = v___x_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg___boxed(lean_object* v_key_627_, lean_object* v_as_628_, lean_object* v_sz_629_, lean_object* v_i_630_, lean_object* v_b_631_){
_start:
{
size_t v_sz_boxed_632_; size_t v_i_boxed_633_; lean_object* v_res_634_; 
v_sz_boxed_632_ = lean_unbox_usize(v_sz_629_);
lean_dec(v_sz_629_);
v_i_boxed_633_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_627_, v_as_628_, v_sz_boxed_632_, v_i_boxed_633_, v_b_631_);
lean_dec_ref(v_as_628_);
return v_res_634_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_box(0);
v___x_636_ = lean_unsigned_to_nat(16u);
v___x_637_ = lean_mk_array(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_groups_640_; 
v___x_638_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0);
v___x_639_ = lean_unsigned_to_nat(0u);
v_groups_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_640_, 0, v___x_639_);
lean_ctor_set(v_groups_640_, 1, v___x_638_);
return v_groups_640_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(lean_object* v_key_641_, lean_object* v_xs_642_){
_start:
{
lean_object* v_groups_643_; size_t v_sz_644_; size_t v___x_645_; lean_object* v___x_646_; 
v_groups_643_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1);
v_sz_644_ = lean_array_size(v_xs_642_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_641_, v_xs_642_, v_sz_644_, v___x_645_, v_groups_643_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(lean_object* v_key_647_, lean_object* v_xs_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_647_, v_xs_648_);
lean_dec_ref(v_xs_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object* v_items_651_){
_start:
{
lean_object* v___y_653_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_670_; lean_object* v___f_677_; lean_object* v_partitions_678_; lean_object* v_size_679_; lean_object* v_buckets_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___f_677_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0));
v_partitions_678_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v___f_677_, v_items_651_);
v_size_679_ = lean_ctor_get(v_partitions_678_, 0);
lean_inc(v_size_679_);
v_buckets_680_ = lean_ctor_get(v_partitions_678_, 1);
lean_inc_ref(v_buckets_680_);
lean_dec_ref(v_partitions_678_);
v___x_681_ = lean_mk_empty_array_with_capacity(v_size_679_);
lean_dec(v_size_679_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_array_get_size(v_buckets_680_);
v___x_684_ = lean_nat_dec_lt(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_dec_ref(v_buckets_680_);
v___y_670_ = v___x_681_;
goto v___jp_669_;
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_683_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_680_, v___x_685_, v___x_686_, v___x_681_);
lean_dec_ref(v_buckets_680_);
v___y_670_ = v___x_687_;
goto v___jp_669_;
}
v___jp_652_:
{
size_t v_sz_654_; size_t v___x_655_; lean_object* v___x_656_; 
v_sz_654_ = lean_array_size(v___y_653_);
v___x_655_ = ((size_t)0ULL);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_654_, v___x_655_, v___y_653_);
return v___x_656_;
}
v___jp_657_:
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v___y_659_, v___y_658_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec(v___y_659_);
v___y_653_ = v___x_662_;
goto v___jp_652_;
}
v___jp_663_:
{
uint8_t v___x_668_; 
v___x_668_ = lean_nat_dec_le(v___y_667_, v___y_664_);
if (v___x_668_ == 0)
{
lean_dec(v___y_664_);
lean_inc(v___y_667_);
v___y_658_ = v___y_665_;
v___y_659_ = v___y_666_;
v___y_660_ = v___y_667_;
v___y_661_ = v___y_667_;
goto v___jp_657_;
}
else
{
v___y_658_ = v___y_665_;
v___y_659_ = v___y_666_;
v___y_660_ = v___y_667_;
v___y_661_ = v___y_664_;
goto v___jp_657_;
}
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_array_get_size(v___y_670_);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_nat_dec_eq(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_sub(v___x_671_, v___x_674_);
v___x_676_ = lean_nat_dec_le(v___x_672_, v___x_675_);
if (v___x_676_ == 0)
{
lean_inc(v___x_675_);
v___y_664_ = v___x_675_;
v___y_665_ = v___y_670_;
v___y_666_ = v___x_671_;
v___y_667_ = v___x_675_;
goto v___jp_663_;
}
else
{
v___y_664_ = v___x_675_;
v___y_665_ = v___y_670_;
v___y_666_ = v___x_671_;
v___y_667_ = v___x_672_;
goto v___jp_663_;
}
}
else
{
v___y_653_ = v___y_670_;
goto v___jp_652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object* v_items_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_688_);
lean_dec_ref(v_items_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object* v_n_690_, lean_object* v_as_691_, lean_object* v_lo_692_, lean_object* v_hi_693_, lean_object* v_w_694_, lean_object* v_hlo_695_, lean_object* v_hhi_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_690_, v_as_691_, v_lo_692_, v_hi_693_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object* v_n_698_, lean_object* v_as_699_, lean_object* v_lo_700_, lean_object* v_hi_701_, lean_object* v_w_702_, lean_object* v_hlo_703_, lean_object* v_hhi_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_n_698_, v_as_699_, v_lo_700_, v_hi_701_, v_w_702_, v_hlo_703_, v_hhi_704_);
lean_dec(v_hi_701_);
lean_dec(v_n_698_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object* v_00_u03b2_706_, lean_object* v_key_707_, lean_object* v_xs_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_707_, v_xs_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object* v_00_u03b2_710_, lean_object* v_key_711_, lean_object* v_xs_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_00_u03b2_710_, v_key_711_, v_xs_712_);
lean_dec_ref(v_xs_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object* v_n_714_, lean_object* v_lo_715_, lean_object* v_hi_716_, lean_object* v_hhi_717_, lean_object* v_pivot_718_, lean_object* v_as_719_, lean_object* v_i_720_, lean_object* v_k_721_, lean_object* v_ilo_722_, lean_object* v_ik_723_, lean_object* v_w_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_716_, v_pivot_718_, v_as_719_, v_i_720_, v_k_721_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object* v_n_726_, lean_object* v_lo_727_, lean_object* v_hi_728_, lean_object* v_hhi_729_, lean_object* v_pivot_730_, lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_k_733_, lean_object* v_ilo_734_, lean_object* v_ik_735_, lean_object* v_w_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_n_726_, v_lo_727_, v_hi_728_, v_hhi_729_, v_pivot_730_, v_as_731_, v_i_732_, v_k_733_, v_ilo_734_, v_ik_735_, v_w_736_);
lean_dec_ref(v_pivot_730_);
lean_dec(v_hi_728_);
lean_dec(v_lo_727_);
lean_dec(v_n_726_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(lean_object* v_00_u03b2_738_, lean_object* v_a_739_, lean_object* v_m_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_739_, v_m_740_, v_a_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(lean_object* v_00_u03b2_743_, lean_object* v_key_744_, lean_object* v_as_745_, size_t v_sz_746_, size_t v_i_747_, lean_object* v_b_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_744_, v_as_745_, v_sz_746_, v_i_747_, v_b_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(lean_object* v_00_u03b2_750_, lean_object* v_key_751_, lean_object* v_as_752_, lean_object* v_sz_753_, lean_object* v_i_754_, lean_object* v_b_755_){
_start:
{
size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v_sz_boxed_756_ = lean_unbox_usize(v_sz_753_);
lean_dec(v_sz_753_);
v_i_boxed_757_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(v_00_u03b2_750_, v_key_751_, v_as_752_, v_sz_boxed_756_, v_i_boxed_757_, v_b_755_);
lean_dec_ref(v_as_752_);
return v_res_758_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_759_, lean_object* v_a_760_, lean_object* v_x_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_763_, lean_object* v_a_764_, lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(v_00_u03b2_763_, v_a_764_, v_x_765_);
lean_dec(v_x_765_);
lean_dec_ref(v_a_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_768_, lean_object* v_data_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_data_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_772_, v_a_773_, v_x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_776_, lean_object* v_i_777_, lean_object* v_source_778_, lean_object* v_target_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v_i_777_, v_source_778_, v_target_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_x_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object* v_fileMap_785_, lean_object* v_hoverPos_786_, lean_object* v_cmdStx_787_, lean_object* v_infoTree_788_){
_start:
{
lean_object* v___x_789_; lean_object* v_fst_790_; lean_object* v_snd_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_801_; 
v___x_789_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_785_, v_hoverPos_786_, v_cmdStx_787_, v_infoTree_788_);
v_fst_790_ = lean_ctor_get(v___x_789_, 0);
v_snd_791_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_801_ == 0)
{
v___x_793_ = v___x_789_;
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snd_791_);
lean_inc(v_fst_790_);
lean_dec(v___x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_partitions_797_; lean_object* v___x_799_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = l_Array_zipIdx___redArg(v_fst_790_, v___x_795_);
v_partitions_797_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_796_);
lean_dec_ref(v___x_796_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_partitions_797_);
v___x_799_ = v___x_793_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_partitions_797_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_791_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
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
