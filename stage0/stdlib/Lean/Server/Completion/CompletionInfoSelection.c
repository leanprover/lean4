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
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_i_170_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_193_; uint8_t v___x_198_; uint8_t v___x_199_; 
v_i_170_ = lean_ctor_get(v_info_168_, 0);
lean_inc_ref_n(v_i_170_, 2);
v___x_198_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_165_, v_i_170_);
v___x_199_ = lean_bool_not(v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Elab_Info_pos_x3f(v_info_168_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_202_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_201_);
v___y_193_ = v___x_202_;
goto v___jp_192_;
}
else
{
lean_object* v_val_203_; 
v_val_203_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v___x_200_, 1);
v___y_193_ = v_val_203_;
goto v___jp_192_;
}
}
else
{
lean_dec_ref(v_i_170_);
lean_dec_ref_known(v_info_168_, 1);
lean_dec_ref(v_ctx_167_);
lean_dec_ref(v_fileMap_164_);
return v_best_169_;
}
v___jp_171_:
{
lean_object* v___x_175_; lean_object* v_line_176_; lean_object* v___x_177_; lean_object* v_line_178_; uint8_t v___x_179_; uint8_t v___x_180_; 
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
v___x_180_ = lean_bool_not(v___x_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_nat_dec_eq(v_line_176_, v_line_178_);
lean_dec(v_line_178_);
lean_dec(v_line_176_);
v___x_182_ = lean_bool_not(v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_183_, 0, v___y_174_);
lean_ctor_set(v___x_183_, 1, v_ctx_167_);
lean_ctor_set(v___x_183_, 2, v_i_170_);
v___x_184_ = lean_array_push(v_best_169_, v___x_183_);
return v___x_184_;
}
else
{
lean_dec(v___y_174_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
return v_best_169_;
}
}
else
{
lean_dec(v_line_178_);
lean_dec(v_line_176_);
lean_dec(v___y_174_);
lean_dec_ref(v_i_170_);
lean_dec_ref(v_ctx_167_);
return v_best_169_;
}
}
v___jp_185_:
{
uint8_t v___x_188_; 
v___x_188_ = lean_nat_dec_lt(v_hoverPos_165_, v___y_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
v___y_172_ = v___y_187_;
v___y_173_ = v___y_186_;
v___y_174_ = v___x_189_;
goto v___jp_171_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_nat_sub(v_hoverPos_165_, v___y_186_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
v___y_172_ = v___y_187_;
v___y_173_ = v___y_186_;
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
v___y_186_ = v___y_193_;
v___y_187_ = v___x_196_;
goto v___jp_185_;
}
else
{
lean_object* v_val_197_; 
v_val_197_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_194_, 1);
v___y_186_ = v___y_193_;
v___y_187_ = v_val_197_;
goto v___jp_185_;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed(lean_object* v_fileMap_204_, lean_object* v_hoverPos_205_, lean_object* v_hoverLine_206_, lean_object* v_ctx_207_, lean_object* v_info_208_, lean_object* v_best_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(v_fileMap_204_, v_hoverPos_205_, v_hoverLine_206_, v_ctx_207_, v_info_208_, v_best_209_);
lean_dec(v_hoverLine_206_);
lean_dec(v_hoverPos_205_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object* v_fileMap_211_, lean_object* v_hoverPos_212_, lean_object* v_cmdStx_213_, lean_object* v_infoTree_214_){
_start:
{
uint8_t v_isComplete_216_; lean_object* v_completionInfoCandidates_217_; lean_object* v___x_221_; lean_object* v_line_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_completionInfoCandidates_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
lean_inc_ref_n(v_fileMap_211_, 2);
v___x_221_ = l_Lean_FileMap_toPosition(v_fileMap_211_, v_hoverPos_212_);
v_line_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_line_222_);
lean_dec_ref(v___x_221_);
lean_inc(v_hoverPos_212_);
v___x_223_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed), 6, 3);
lean_closure_set(v___x_223_, 0, v_fileMap_211_);
lean_closure_set(v___x_223_, 1, v_hoverPos_212_);
lean_closure_set(v___x_223_, 2, v_line_222_);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
lean_inc_ref(v_infoTree_214_);
v_completionInfoCandidates_226_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___x_223_, v___x_225_, v_infoTree_214_);
v___x_227_ = lean_array_get_size(v_completionInfoCandidates_226_);
v___x_228_ = lean_nat_dec_eq(v___x_227_, v___x_224_);
if (v___x_228_ == 0)
{
uint8_t v_isComplete_229_; 
lean_dec_ref(v_infoTree_214_);
lean_dec(v_cmdStx_213_);
lean_dec(v_hoverPos_212_);
lean_dec_ref(v_fileMap_211_);
v_isComplete_229_ = 1;
v_isComplete_216_ = v_isComplete_229_;
v_completionInfoCandidates_217_ = v_completionInfoCandidates_226_;
goto v___jp_215_;
}
else
{
lean_object* v_completionInfoCandidates_230_; uint8_t v_isComplete_231_; 
lean_dec(v_completionInfoCandidates_226_);
v_completionInfoCandidates_230_ = l_Lean_Server_Completion_findSyntheticCompletions(v_fileMap_211_, v_hoverPos_212_, v_cmdStx_213_, v_infoTree_214_);
v_isComplete_231_ = 0;
v_isComplete_216_ = v_isComplete_231_;
v_completionInfoCandidates_217_ = v_completionInfoCandidates_230_;
goto v___jp_215_;
}
v___jp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_completionInfoCandidates_217_);
lean_dec_ref(v_completionInfoCandidates_217_);
v___x_219_ = lean_box(v_isComplete_216_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(lean_object* v_x_232_){
_start:
{
lean_object* v_fst_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_248_; 
v_fst_233_ = lean_ctor_get(v_x_232_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_x_232_, 1);
lean_dec(v_unused_249_);
v___x_235_ = v_x_232_;
v_isShared_236_ = v_isSharedCheck_248_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_fst_233_);
lean_dec(v_x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_248_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_info_237_; uint8_t v___y_239_; 
v_info_237_ = lean_ctor_get(v_fst_233_, 2);
lean_inc_ref(v_info_237_);
lean_dec(v_fst_233_);
if (lean_obj_tag(v_info_237_) == 1)
{
uint8_t v___x_246_; 
v___x_246_ = 1;
v___y_239_ = v___x_246_;
goto v___jp_238_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
v___y_239_ = v___x_247_;
goto v___jp_238_;
}
v___jp_238_:
{
lean_object* v___x_240_; lean_object* v_size_x3f_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_240_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_240_, 0, v_info_237_);
v_size_x3f_241_ = l_Lean_Elab_Info_size_x3f(v___x_240_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = lean_box(v___y_239_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_size_x3f_241_);
lean_ctor_set(v___x_235_, 0, v___x_242_);
v___x_244_ = v___x_235_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_size_x3f_241_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
return v_x_250_;
}
else
{
lean_object* v_key_252_; lean_object* v_value_253_; lean_object* v_tail_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_key_252_ = lean_ctor_get(v_x_251_, 0);
v_value_253_ = lean_ctor_get(v_x_251_, 1);
v_tail_254_ = lean_ctor_get(v_x_251_, 2);
lean_inc(v_value_253_);
lean_inc(v_key_252_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_key_252_);
lean_ctor_set(v___x_255_, 1, v_value_253_);
v___x_256_ = lean_array_push(v_x_250_, v___x_255_);
v_x_250_ = v___x_256_;
v_x_251_ = v_tail_254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_x_258_, v_x_259_);
lean_dec(v_x_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(lean_object* v_as_261_, size_t v_i_262_, size_t v_stop_263_, lean_object* v_b_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_eq(v_i_262_, v_stop_263_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; size_t v___x_268_; size_t v___x_269_; 
v___x_266_ = lean_array_uget_borrowed(v_as_261_, v_i_262_);
v___x_267_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_b_264_, v___x_266_);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_i_262_, v___x_268_);
v_i_262_ = v___x_269_;
v_b_264_ = v___x_267_;
goto _start;
}
else
{
return v_b_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4___boxed(lean_object* v_as_271_, lean_object* v_i_272_, lean_object* v_stop_273_, lean_object* v_b_274_){
_start:
{
size_t v_i_boxed_275_; size_t v_stop_boxed_276_; lean_object* v_res_277_; 
v_i_boxed_275_ = lean_unbox_usize(v_i_272_);
lean_dec(v_i_272_);
v_stop_boxed_276_ = lean_unbox_usize(v_stop_273_);
lean_dec(v_stop_273_);
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_271_, v_i_boxed_275_, v_stop_boxed_276_, v_b_274_);
lean_dec_ref(v_as_271_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t v_sz_278_, size_t v_i_279_, lean_object* v_bs_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_usize_dec_lt(v_i_279_, v_sz_278_);
if (v___x_281_ == 0)
{
return v_bs_280_;
}
else
{
lean_object* v_v_282_; lean_object* v_snd_283_; lean_object* v___x_284_; lean_object* v_bs_x27_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; 
v_v_282_ = lean_array_uget_borrowed(v_bs_280_, v_i_279_);
v_snd_283_ = lean_ctor_get(v_v_282_, 1);
lean_inc(v_snd_283_);
v___x_284_ = lean_unsigned_to_nat(0u);
v_bs_x27_285_ = lean_array_uset(v_bs_280_, v_i_279_, v___x_284_);
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_add(v_i_279_, v___x_286_);
v___x_288_ = lean_array_uset(v_bs_x27_285_, v_i_279_, v_snd_283_);
v_i_279_ = v___x_287_;
v_bs_280_ = v___x_288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object* v_sz_290_, lean_object* v_i_291_, lean_object* v_bs_292_){
_start:
{
size_t v_sz_boxed_293_; size_t v_i_boxed_294_; lean_object* v_res_295_; 
v_sz_boxed_293_ = lean_unbox_usize(v_sz_290_);
lean_dec(v_sz_290_);
v_i_boxed_294_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_293_, v_i_boxed_294_, v_bs_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object* v_hi_296_, lean_object* v_pivot_297_, lean_object* v_as_298_, lean_object* v_i_299_, lean_object* v_k_300_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_lt(v_k_300_, v_hi_296_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_k_300_);
v___x_312_ = lean_array_fswap(v_as_298_, v_i_299_, v_hi_296_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v_i_299_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v_fst_315_; lean_object* v_fst_316_; lean_object* v_fst_317_; lean_object* v_snd_318_; lean_object* v_fst_319_; lean_object* v_snd_320_; 
v___x_314_ = lean_array_fget_borrowed(v_as_298_, v_k_300_);
v_fst_315_ = lean_ctor_get(v___x_314_, 0);
v_fst_316_ = lean_ctor_get(v_pivot_297_, 0);
v_fst_317_ = lean_ctor_get(v_fst_315_, 0);
v_snd_318_ = lean_ctor_get(v_fst_315_, 1);
v_fst_319_ = lean_ctor_get(v_fst_316_, 0);
v_snd_320_ = lean_ctor_get(v_fst_316_, 1);
if (lean_obj_tag(v_snd_318_) == 0)
{
if (lean_obj_tag(v_snd_320_) == 1)
{
goto v___jp_301_;
}
else
{
goto v___jp_325_;
}
}
else
{
if (lean_obj_tag(v_snd_320_) == 0)
{
goto v___jp_305_;
}
else
{
goto v___jp_325_;
}
}
v___jp_321_:
{
if (lean_obj_tag(v_snd_318_) == 1)
{
if (lean_obj_tag(v_snd_320_) == 1)
{
lean_object* v_val_322_; lean_object* v_val_323_; uint8_t v___x_324_; 
v_val_322_ = lean_ctor_get(v_snd_318_, 0);
v_val_323_ = lean_ctor_get(v_snd_320_, 0);
v___x_324_ = lean_nat_dec_lt(v_val_322_, v_val_323_);
if (v___x_324_ == 0)
{
goto v___jp_301_;
}
else
{
goto v___jp_305_;
}
}
else
{
goto v___jp_301_;
}
}
else
{
goto v___jp_301_;
}
}
v___jp_325_:
{
uint8_t v___x_326_; 
v___x_326_ = lean_unbox(v_fst_317_);
if (v___x_326_ == 0)
{
uint8_t v___x_327_; 
v___x_327_ = lean_unbox(v_fst_319_);
if (v___x_327_ == 1)
{
goto v___jp_305_;
}
else
{
goto v___jp_321_;
}
}
else
{
uint8_t v___x_328_; 
v___x_328_ = lean_unbox(v_fst_319_);
if (v___x_328_ == 0)
{
goto v___jp_301_;
}
else
{
goto v___jp_321_;
}
}
}
}
v___jp_301_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_k_300_, v___x_302_);
lean_dec(v_k_300_);
v_k_300_ = v___x_303_;
goto _start;
}
v___jp_305_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_array_fswap(v_as_298_, v_i_299_, v_k_300_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_i_299_, v___x_307_);
lean_dec(v_i_299_);
v___x_309_ = lean_nat_add(v_k_300_, v___x_307_);
lean_dec(v_k_300_);
v_as_298_ = v___x_306_;
v_i_299_ = v___x_308_;
v_k_300_ = v___x_309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(lean_object* v_hi_329_, lean_object* v_pivot_330_, lean_object* v_as_331_, lean_object* v_i_332_, lean_object* v_k_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_329_, v_pivot_330_, v_as_331_, v_i_332_, v_k_333_);
lean_dec_ref(v_pivot_330_);
lean_dec(v_hi_329_);
return v_res_334_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(uint8_t v___x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_fst_338_; lean_object* v_fst_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v_fst_342_; lean_object* v_snd_343_; 
v_fst_338_ = lean_ctor_get(v_x_336_, 0);
v_fst_339_ = lean_ctor_get(v_x_337_, 0);
v_fst_340_ = lean_ctor_get(v_fst_338_, 0);
v_snd_341_ = lean_ctor_get(v_fst_338_, 1);
v_fst_342_ = lean_ctor_get(v_fst_339_, 0);
v_snd_343_ = lean_ctor_get(v_fst_339_, 1);
if (lean_obj_tag(v_snd_341_) == 0)
{
if (lean_obj_tag(v_snd_343_) == 1)
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
else
{
goto v___jp_350_;
}
}
else
{
if (lean_obj_tag(v_snd_343_) == 0)
{
return v___x_335_;
}
else
{
goto v___jp_350_;
}
}
v___jp_344_:
{
if (lean_obj_tag(v_snd_341_) == 1)
{
if (lean_obj_tag(v_snd_343_) == 1)
{
lean_object* v_val_345_; lean_object* v_val_346_; uint8_t v___x_347_; 
v_val_345_ = lean_ctor_get(v_snd_341_, 0);
v_val_346_ = lean_ctor_get(v_snd_343_, 0);
v___x_347_ = lean_nat_dec_lt(v_val_345_, v_val_346_);
return v___x_347_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = 0;
return v___x_348_;
}
}
else
{
uint8_t v___x_349_; 
v___x_349_ = 0;
return v___x_349_;
}
}
v___jp_350_:
{
uint8_t v___x_351_; 
v___x_351_ = lean_unbox(v_fst_340_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; 
v___x_352_ = lean_unbox(v_fst_342_);
if (v___x_352_ == 1)
{
uint8_t v___x_353_; 
v___x_353_ = lean_unbox(v_fst_342_);
return v___x_353_;
}
else
{
goto v___jp_344_;
}
}
else
{
uint8_t v___x_354_; 
v___x_354_ = lean_unbox(v_fst_342_);
if (v___x_354_ == 0)
{
uint8_t v___x_355_; 
v___x_355_ = lean_unbox(v_fst_342_);
return v___x_355_;
}
else
{
goto v___jp_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0___boxed(lean_object* v___x_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
uint8_t v___x_2350__boxed_360_; uint8_t v_res_361_; lean_object* v_r_362_; 
v___x_2350__boxed_360_ = lean_unbox(v___x_357_);
v_res_361_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_2350__boxed_360_, v_x_358_, v_x_359_);
lean_dec_ref(v_x_359_);
lean_dec_ref(v_x_358_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(lean_object* v_n_363_, lean_object* v_as_364_, lean_object* v_lo_365_, lean_object* v_hi_366_){
_start:
{
lean_object* v___y_368_; uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_lt(v_lo_365_, v_hi_366_);
if (v___x_378_ == 0)
{
lean_dec(v_lo_365_);
return v_as_364_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_mid_381_; lean_object* v___y_383_; lean_object* v___y_389_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_379_ = lean_nat_add(v_lo_365_, v_hi_366_);
v___x_380_ = lean_unsigned_to_nat(1u);
v_mid_381_ = lean_nat_shiftr(v___x_379_, v___x_380_);
lean_dec(v___x_379_);
v___x_394_ = lean_array_fget_borrowed(v_as_364_, v_mid_381_);
v___x_395_ = lean_array_fget_borrowed(v_as_364_, v_lo_365_);
v___x_396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_378_, v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
v___y_389_ = v_as_364_;
goto v___jp_388_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = lean_array_fswap(v_as_364_, v_lo_365_, v_mid_381_);
v___y_389_ = v___x_397_;
goto v___jp_388_;
}
v___jp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_384_ = lean_array_fget_borrowed(v___y_383_, v_mid_381_);
v___x_385_ = lean_array_fget_borrowed(v___y_383_, v_hi_366_);
v___x_386_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_378_, v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_dec(v_mid_381_);
v___y_368_ = v___y_383_;
goto v___jp_367_;
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_array_fswap(v___y_383_, v_mid_381_, v_hi_366_);
lean_dec(v_mid_381_);
v___y_368_ = v___x_387_;
goto v___jp_367_;
}
}
v___jp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_array_fget_borrowed(v___y_389_, v_hi_366_);
v___x_391_ = lean_array_fget_borrowed(v___y_389_, v_lo_365_);
v___x_392_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_378_, v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
v___y_383_ = v___y_389_;
goto v___jp_382_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_array_fswap(v___y_389_, v_lo_365_, v_hi_366_);
v___y_383_ = v___x_393_;
goto v___jp_382_;
}
}
}
v___jp_367_:
{
lean_object* v_pivot_369_; lean_object* v___x_370_; lean_object* v_fst_371_; lean_object* v_snd_372_; uint8_t v___x_373_; 
v_pivot_369_ = lean_array_fget(v___y_368_, v_hi_366_);
lean_inc_n(v_lo_365_, 2);
v___x_370_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_366_, v_pivot_369_, v___y_368_, v_lo_365_, v_lo_365_);
lean_dec(v_pivot_369_);
v_fst_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_fst_371_);
v_snd_372_ = lean_ctor_get(v___x_370_, 1);
lean_inc(v_snd_372_);
lean_dec_ref(v___x_370_);
v___x_373_ = lean_nat_dec_le(v_hi_366_, v_fst_371_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_363_, v_snd_372_, v_lo_365_, v_fst_371_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_fst_371_, v___x_375_);
lean_dec(v_fst_371_);
v_as_364_ = v___x_374_;
v_lo_365_ = v___x_376_;
goto _start;
}
else
{
lean_dec(v_fst_371_);
lean_dec(v_lo_365_);
return v_snd_372_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(lean_object* v_n_398_, lean_object* v_as_399_, lean_object* v_lo_400_, lean_object* v_hi_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_398_, v_as_399_, v_lo_400_, v_hi_401_);
lean_dec(v_hi_401_);
lean_dec(v_n_398_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
return v_x_403_;
}
else
{
lean_object* v_key_405_; lean_object* v_value_406_; lean_object* v_tail_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_445_; 
v_key_405_ = lean_ctor_get(v_x_404_, 0);
v_value_406_ = lean_ctor_get(v_x_404_, 1);
v_tail_407_ = lean_ctor_get(v_x_404_, 2);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_404_);
if (v_isSharedCheck_445_ == 0)
{
v___x_409_ = v_x_404_;
v_isShared_410_ = v_isSharedCheck_445_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_tail_407_);
lean_inc(v_value_406_);
lean_inc(v_key_405_);
lean_dec(v_x_404_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_445_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_413_; uint64_t v___y_415_; uint64_t v___y_416_; uint64_t v___y_436_; uint8_t v___x_442_; 
v_fst_411_ = lean_ctor_get(v_key_405_, 0);
v_snd_412_ = lean_ctor_get(v_key_405_, 1);
v___x_413_ = lean_array_get_size(v_x_403_);
v___x_442_ = lean_unbox(v_fst_411_);
if (v___x_442_ == 0)
{
uint64_t v___x_443_; 
v___x_443_ = 13ULL;
v___y_436_ = v___x_443_;
goto v___jp_435_;
}
else
{
uint64_t v___x_444_; 
v___x_444_ = 11ULL;
v___y_436_ = v___x_444_;
goto v___jp_435_;
}
v___jp_414_:
{
uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v_fold_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_417_ = lean_uint64_mix_hash(v___y_415_, v___y_416_);
v___x_418_ = 32ULL;
v___x_419_ = lean_uint64_shift_right(v___x_417_, v___x_418_);
v_fold_420_ = lean_uint64_xor(v___x_417_, v___x_419_);
v___x_421_ = 16ULL;
v___x_422_ = lean_uint64_shift_right(v_fold_420_, v___x_421_);
v___x_423_ = lean_uint64_xor(v_fold_420_, v___x_422_);
v___x_424_ = lean_uint64_to_usize(v___x_423_);
v___x_425_ = lean_usize_of_nat(v___x_413_);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_sub(v___x_425_, v___x_426_);
v___x_428_ = lean_usize_land(v___x_424_, v___x_427_);
v___x_429_ = lean_array_uget_borrowed(v_x_403_, v___x_428_);
lean_inc(v___x_429_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 2, v___x_429_);
v___x_431_ = v___x_409_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_key_405_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_value_406_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v___x_429_);
v___x_431_ = v_reuseFailAlloc_434_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_array_uset(v_x_403_, v___x_428_, v___x_431_);
v_x_403_ = v___x_432_;
v_x_404_ = v_tail_407_;
goto _start;
}
}
v___jp_435_:
{
if (lean_obj_tag(v_snd_412_) == 0)
{
uint64_t v___x_437_; 
v___x_437_ = 11ULL;
v___y_415_ = v___y_436_;
v___y_416_ = v___x_437_;
goto v___jp_414_;
}
else
{
lean_object* v_val_438_; uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; 
v_val_438_ = lean_ctor_get(v_snd_412_, 0);
v___x_439_ = l_String_instHashableRaw_hash(v_val_438_);
v___x_440_ = 13ULL;
v___x_441_ = lean_uint64_mix_hash(v___x_439_, v___x_440_);
v___y_415_ = v___y_436_;
v___y_416_ = v___x_441_;
goto v___jp_414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_i_446_, lean_object* v_source_447_, lean_object* v_target_448_){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_array_get_size(v_source_447_);
v___x_450_ = lean_nat_dec_lt(v_i_446_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec_ref(v_source_447_);
lean_dec(v_i_446_);
return v_target_448_;
}
else
{
lean_object* v_es_451_; lean_object* v___x_452_; lean_object* v_source_453_; lean_object* v_target_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_es_451_ = lean_array_fget(v_source_447_, v_i_446_);
v___x_452_ = lean_box(0);
v_source_453_ = lean_array_fset(v_source_447_, v_i_446_, v___x_452_);
v_target_454_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_target_448_, v_es_451_);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v_i_446_, v___x_455_);
lean_dec(v_i_446_);
v_i_446_ = v___x_456_;
v_source_447_ = v_source_453_;
v_target_448_ = v_target_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(lean_object* v_data_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_nbuckets_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_459_ = lean_array_get_size(v_data_458_);
v___x_460_ = lean_unsigned_to_nat(2u);
v_nbuckets_461_ = lean_nat_mul(v___x_459_, v___x_460_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_box(0);
v___x_464_ = lean_mk_array(v_nbuckets_461_, v___x_463_);
v___x_465_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v___x_462_, v_data_458_, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
if (lean_obj_tag(v_x_467_) == 0)
{
uint8_t v___x_468_; 
v___x_468_ = 1;
return v___x_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
}
else
{
if (lean_obj_tag(v_x_467_) == 0)
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
else
{
lean_object* v_val_471_; lean_object* v_val_472_; uint8_t v___x_473_; 
v_val_471_ = lean_ctor_get(v_x_466_, 0);
v_val_472_ = lean_ctor_get(v_x_467_, 0);
v___x_473_ = lean_nat_dec_eq(v_val_471_, v_val_472_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_474_, v_x_475_);
lean_dec(v_x_475_);
lean_dec(v_x_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(lean_object* v_a_478_, lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
uint8_t v___x_480_; 
v___x_480_ = 0;
return v___x_480_;
}
else
{
lean_object* v_key_481_; lean_object* v_tail_482_; lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; uint8_t v___x_490_; 
v_key_481_ = lean_ctor_get(v_x_479_, 0);
v_tail_482_ = lean_ctor_get(v_x_479_, 2);
v_fst_483_ = lean_ctor_get(v_key_481_, 0);
v_snd_484_ = lean_ctor_get(v_key_481_, 1);
v_fst_485_ = lean_ctor_get(v_a_478_, 0);
v_snd_486_ = lean_ctor_get(v_a_478_, 1);
v___x_490_ = lean_unbox(v_fst_483_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
v___x_491_ = lean_unbox(v_fst_485_);
if (v___x_491_ == 0)
{
goto v___jp_487_;
}
else
{
v_x_479_ = v_tail_482_;
goto _start;
}
}
else
{
uint8_t v___x_493_; 
v___x_493_ = lean_unbox(v_fst_485_);
if (v___x_493_ == 0)
{
v_x_479_ = v_tail_482_;
goto _start;
}
else
{
goto v___jp_487_;
}
}
v___jp_487_:
{
uint8_t v___x_488_; 
v___x_488_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_484_, v_snd_486_);
if (v___x_488_ == 0)
{
v_x_479_ = v_tail_482_;
goto _start;
}
else
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_495_, lean_object* v_x_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_495_, v_x_496_);
lean_dec(v_x_496_);
lean_dec_ref(v_a_495_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_a_501_, lean_object* v_x_502_){
_start:
{
lean_object* v___y_504_; 
if (lean_obj_tag(v_x_502_) == 0)
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___y_504_ = v___x_507_;
goto v___jp_503_;
}
else
{
lean_object* v_val_508_; 
v_val_508_ = lean_ctor_get(v_x_502_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v_x_502_, 1);
v___y_504_ = v_val_508_;
goto v___jp_503_;
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_push(v___y_504_, v_a_501_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_511_) == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_val_514_; lean_object* v___x_515_; 
v___x_512_ = lean_box(0);
v___x_513_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_509_, v___x_512_);
v_val_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_514_);
lean_dec(v___x_513_);
v___x_515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_515_, 0, v_a_510_);
lean_ctor_set(v___x_515_, 1, v_val_514_);
lean_ctor_set(v___x_515_, 2, v_x_511_);
return v___x_515_;
}
else
{
lean_object* v_key_516_; lean_object* v_value_517_; lean_object* v_tail_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_540_; 
v_key_516_ = lean_ctor_get(v_x_511_, 0);
v_value_517_ = lean_ctor_get(v_x_511_, 1);
v_tail_518_ = lean_ctor_get(v_x_511_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_540_ == 0)
{
v___x_520_ = v_x_511_;
v_isShared_521_ = v_isSharedCheck_540_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_tail_518_);
lean_inc(v_value_517_);
lean_inc(v_key_516_);
lean_dec(v_x_511_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_540_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; uint8_t v___x_537_; 
v_fst_527_ = lean_ctor_get(v_key_516_, 0);
v_snd_528_ = lean_ctor_get(v_key_516_, 1);
v_fst_529_ = lean_ctor_get(v_a_510_, 0);
v_snd_530_ = lean_ctor_get(v_a_510_, 1);
v___x_537_ = lean_unbox(v_fst_527_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; 
v___x_538_ = lean_unbox(v_fst_529_);
if (v___x_538_ == 0)
{
goto v___jp_531_;
}
else
{
goto v___jp_522_;
}
}
else
{
uint8_t v___x_539_; 
v___x_539_ = lean_unbox(v_fst_529_);
if (v___x_539_ == 0)
{
goto v___jp_522_;
}
else
{
goto v___jp_531_;
}
}
v___jp_522_:
{
lean_object* v_tail_523_; lean_object* v___x_525_; 
v_tail_523_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_509_, v_a_510_, v_tail_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 2, v_tail_523_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_key_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_value_517_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_tail_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
v___jp_531_:
{
uint8_t v___x_532_; 
v___x_532_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_528_, v_snd_530_);
if (v___x_532_ == 0)
{
goto v___jp_522_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_val_535_; lean_object* v___x_536_; 
lean_del_object(v___x_520_);
lean_dec(v_key_516_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_value_517_);
v___x_534_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_509_, v___x_533_);
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec(v___x_534_);
v___x_536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_536_, 0, v_a_510_);
lean_ctor_set(v___x_536_, 1, v_val_535_);
lean_ctor_set(v___x_536_, 2, v_tail_518_);
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(lean_object* v_a_541_, lean_object* v_m_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___y_545_; lean_object* v___y_546_; size_t v___y_547_; lean_object* v___y_548_; lean_object* v_size_551_; lean_object* v_buckets_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_611_; 
v_size_551_ = lean_ctor_get(v_m_542_, 0);
v_buckets_552_ = lean_ctor_get(v_m_542_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_m_542_);
if (v_isSharedCheck_611_ == 0)
{
v___x_554_ = v_m_542_;
v_isShared_555_ = v_isSharedCheck_611_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_buckets_552_);
lean_inc(v_size_551_);
lean_dec(v_m_542_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_611_;
goto v_resetjp_553_;
}
v___jp_544_:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_array_uset(v___y_546_, v___y_547_, v___y_545_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___y_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
return v___x_550_;
}
v_resetjp_553_:
{
lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_558_; uint64_t v___y_560_; uint64_t v___y_561_; uint64_t v___y_602_; uint8_t v___x_608_; 
v_fst_556_ = lean_ctor_get(v_a_543_, 0);
v_snd_557_ = lean_ctor_get(v_a_543_, 1);
v___x_558_ = lean_array_get_size(v_buckets_552_);
v___x_608_ = lean_unbox(v_fst_556_);
if (v___x_608_ == 0)
{
uint64_t v___x_609_; 
v___x_609_ = 13ULL;
v___y_602_ = v___x_609_;
goto v___jp_601_;
}
else
{
uint64_t v___x_610_; 
v___x_610_ = 11ULL;
v___y_602_ = v___x_610_;
goto v___jp_601_;
}
v___jp_559_:
{
uint64_t v___x_562_; uint64_t v___x_563_; uint64_t v___x_564_; uint64_t v_fold_565_; uint64_t v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v_bkt_574_; uint8_t v___x_575_; 
v___x_562_ = lean_uint64_mix_hash(v___y_560_, v___y_561_);
v___x_563_ = 32ULL;
v___x_564_ = lean_uint64_shift_right(v___x_562_, v___x_563_);
v_fold_565_ = lean_uint64_xor(v___x_562_, v___x_564_);
v___x_566_ = 16ULL;
v___x_567_ = lean_uint64_shift_right(v_fold_565_, v___x_566_);
v___x_568_ = lean_uint64_xor(v_fold_565_, v___x_567_);
v___x_569_ = lean_uint64_to_usize(v___x_568_);
v___x_570_ = lean_usize_of_nat(v___x_558_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_sub(v___x_570_, v___x_571_);
v___x_573_ = lean_usize_land(v___x_569_, v___x_572_);
v_bkt_574_ = lean_array_uget_borrowed(v_buckets_552_, v___x_573_);
v___x_575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_543_, v_bkt_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_size_x27_579_; lean_object* v___x_580_; lean_object* v_buckets_x27_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_576_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___x_577_ = lean_array_push(v___x_576_, v_a_541_);
v___x_578_ = lean_unsigned_to_nat(1u);
v_size_x27_579_ = lean_nat_add(v_size_551_, v___x_578_);
lean_dec(v_size_551_);
lean_inc(v_bkt_574_);
v___x_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_580_, 0, v_a_543_);
lean_ctor_set(v___x_580_, 1, v___x_577_);
lean_ctor_set(v___x_580_, 2, v_bkt_574_);
v_buckets_x27_581_ = lean_array_uset(v_buckets_552_, v___x_573_, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(4u);
v___x_583_ = lean_nat_mul(v_size_x27_579_, v___x_582_);
v___x_584_ = lean_unsigned_to_nat(3u);
v___x_585_ = lean_nat_div(v___x_583_, v___x_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_array_get_size(v_buckets_x27_581_);
v___x_587_ = lean_nat_dec_le(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
if (v___x_587_ == 0)
{
lean_object* v_val_588_; lean_object* v___x_590_; 
v_val_588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_buckets_x27_581_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_val_588_);
lean_ctor_set(v___x_554_, 0, v_size_x27_579_);
v___x_590_ = v___x_554_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_size_x27_579_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_val_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_593_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_buckets_x27_581_);
lean_ctor_set(v___x_554_, 0, v_size_x27_579_);
v___x_593_ = v___x_554_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_size_x27_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_buckets_x27_581_);
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
lean_object* v___x_595_; lean_object* v_buckets_x27_596_; lean_object* v_bkt_x27_597_; uint8_t v___x_598_; 
lean_inc(v_bkt_574_);
lean_del_object(v___x_554_);
v___x_595_ = lean_box(0);
v_buckets_x27_596_ = lean_array_uset(v_buckets_552_, v___x_573_, v___x_595_);
lean_inc_ref(v_a_543_);
v_bkt_x27_597_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_541_, v_a_543_, v_bkt_574_);
v___x_598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_543_, v_bkt_x27_597_);
lean_dec_ref(v_a_543_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_sub(v_size_551_, v___x_599_);
lean_dec(v_size_551_);
v___y_545_ = v_bkt_x27_597_;
v___y_546_ = v_buckets_x27_596_;
v___y_547_ = v___x_573_;
v___y_548_ = v___x_600_;
goto v___jp_544_;
}
else
{
v___y_545_ = v_bkt_x27_597_;
v___y_546_ = v_buckets_x27_596_;
v___y_547_ = v___x_573_;
v___y_548_ = v_size_551_;
goto v___jp_544_;
}
}
}
v___jp_601_:
{
if (lean_obj_tag(v_snd_557_) == 0)
{
uint64_t v___x_603_; 
v___x_603_ = 11ULL;
v___y_560_ = v___y_602_;
v___y_561_ = v___x_603_;
goto v___jp_559_;
}
else
{
lean_object* v_val_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; 
v_val_604_ = lean_ctor_get(v_snd_557_, 0);
v___x_605_ = l_String_instHashableRaw_hash(v_val_604_);
v___x_606_ = 13ULL;
v___x_607_ = lean_uint64_mix_hash(v___x_605_, v___x_606_);
v___y_560_ = v___y_602_;
v___y_561_ = v___x_607_;
goto v___jp_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(lean_object* v_key_612_, lean_object* v_as_613_, size_t v_sz_614_, size_t v_i_615_, lean_object* v_b_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_617_ == 0)
{
lean_dec_ref(v_key_612_);
return v_b_616_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; size_t v___x_621_; size_t v___x_622_; 
v_a_618_ = lean_array_uget_borrowed(v_as_613_, v_i_615_);
lean_inc_ref(v_key_612_);
lean_inc_n(v_a_618_, 2);
v___x_619_ = lean_apply_1(v_key_612_, v_a_618_);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_618_, v_b_616_, v___x_619_);
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_add(v_i_615_, v___x_621_);
v_i_615_ = v___x_622_;
v_b_616_ = v___x_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg___boxed(lean_object* v_key_624_, lean_object* v_as_625_, lean_object* v_sz_626_, lean_object* v_i_627_, lean_object* v_b_628_){
_start:
{
size_t v_sz_boxed_629_; size_t v_i_boxed_630_; lean_object* v_res_631_; 
v_sz_boxed_629_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_i_boxed_630_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_624_, v_as_625_, v_sz_boxed_629_, v_i_boxed_630_, v_b_628_);
lean_dec_ref(v_as_625_);
return v_res_631_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_box(0);
v___x_633_ = lean_unsigned_to_nat(16u);
v___x_634_ = lean_mk_array(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_groups_637_; 
v___x_635_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0);
v___x_636_ = lean_unsigned_to_nat(0u);
v_groups_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_637_, 0, v___x_636_);
lean_ctor_set(v_groups_637_, 1, v___x_635_);
return v_groups_637_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(lean_object* v_key_638_, lean_object* v_xs_639_){
_start:
{
lean_object* v_groups_640_; size_t v_sz_641_; size_t v___x_642_; lean_object* v___x_643_; 
v_groups_640_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1);
v_sz_641_ = lean_array_size(v_xs_639_);
v___x_642_ = ((size_t)0ULL);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_638_, v_xs_639_, v_sz_641_, v___x_642_, v_groups_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(lean_object* v_key_644_, lean_object* v_xs_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_644_, v_xs_645_);
lean_dec_ref(v_xs_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object* v_items_648_){
_start:
{
lean_object* v___y_650_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_667_; lean_object* v___f_674_; lean_object* v_partitions_675_; lean_object* v_size_676_; lean_object* v_buckets_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___f_674_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0));
v_partitions_675_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v___f_674_, v_items_648_);
v_size_676_ = lean_ctor_get(v_partitions_675_, 0);
lean_inc(v_size_676_);
v_buckets_677_ = lean_ctor_get(v_partitions_675_, 1);
lean_inc_ref(v_buckets_677_);
lean_dec_ref(v_partitions_675_);
v___x_678_ = lean_mk_empty_array_with_capacity(v_size_676_);
lean_dec(v_size_676_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_array_get_size(v_buckets_677_);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v_buckets_677_);
v___y_667_ = v___x_678_;
goto v___jp_666_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_le(v___x_680_, v___x_680_);
if (v___x_682_ == 0)
{
if (v___x_681_ == 0)
{
lean_dec_ref(v_buckets_677_);
v___y_667_ = v___x_678_;
goto v___jp_666_;
}
else
{
size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; 
v___x_683_ = ((size_t)0ULL);
v___x_684_ = lean_usize_of_nat(v___x_680_);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_677_, v___x_683_, v___x_684_, v___x_678_);
lean_dec_ref(v_buckets_677_);
v___y_667_ = v___x_685_;
goto v___jp_666_;
}
}
else
{
size_t v___x_686_; size_t v___x_687_; lean_object* v___x_688_; 
v___x_686_ = ((size_t)0ULL);
v___x_687_ = lean_usize_of_nat(v___x_680_);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_677_, v___x_686_, v___x_687_, v___x_678_);
lean_dec_ref(v_buckets_677_);
v___y_667_ = v___x_688_;
goto v___jp_666_;
}
}
v___jp_649_:
{
size_t v_sz_651_; size_t v___x_652_; lean_object* v___x_653_; 
v_sz_651_ = lean_array_size(v___y_650_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_651_, v___x_652_, v___y_650_);
return v___x_653_;
}
v___jp_654_:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec(v___y_655_);
v___y_650_ = v___x_659_;
goto v___jp_649_;
}
v___jp_660_:
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_le(v___y_664_, v___y_663_);
if (v___x_665_ == 0)
{
lean_dec(v___y_663_);
lean_inc(v___y_664_);
v___y_655_ = v___y_661_;
v___y_656_ = v___y_662_;
v___y_657_ = v___y_664_;
v___y_658_ = v___y_664_;
goto v___jp_654_;
}
else
{
v___y_655_ = v___y_661_;
v___y_656_ = v___y_662_;
v___y_657_ = v___y_664_;
v___y_658_ = v___y_663_;
goto v___jp_654_;
}
}
v___jp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_668_ = lean_array_get_size(v___y_667_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_nat_dec_eq(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_sub(v___x_668_, v___x_671_);
v___x_673_ = lean_nat_dec_le(v___x_669_, v___x_672_);
if (v___x_673_ == 0)
{
lean_inc(v___x_672_);
v___y_661_ = v___x_668_;
v___y_662_ = v___y_667_;
v___y_663_ = v___x_672_;
v___y_664_ = v___x_672_;
goto v___jp_660_;
}
else
{
v___y_661_ = v___x_668_;
v___y_662_ = v___y_667_;
v___y_663_ = v___x_672_;
v___y_664_ = v___x_669_;
goto v___jp_660_;
}
}
else
{
v___y_650_ = v___y_667_;
goto v___jp_649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object* v_items_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_689_);
lean_dec_ref(v_items_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object* v_n_691_, lean_object* v_as_692_, lean_object* v_lo_693_, lean_object* v_hi_694_, lean_object* v_w_695_, lean_object* v_hlo_696_, lean_object* v_hhi_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_691_, v_as_692_, v_lo_693_, v_hi_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object* v_n_699_, lean_object* v_as_700_, lean_object* v_lo_701_, lean_object* v_hi_702_, lean_object* v_w_703_, lean_object* v_hlo_704_, lean_object* v_hhi_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_n_699_, v_as_700_, v_lo_701_, v_hi_702_, v_w_703_, v_hlo_704_, v_hhi_705_);
lean_dec(v_hi_702_);
lean_dec(v_n_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object* v_00_u03b2_707_, lean_object* v_key_708_, lean_object* v_xs_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_708_, v_xs_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object* v_00_u03b2_711_, lean_object* v_key_712_, lean_object* v_xs_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_00_u03b2_711_, v_key_712_, v_xs_713_);
lean_dec_ref(v_xs_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object* v_n_715_, lean_object* v_lo_716_, lean_object* v_hi_717_, lean_object* v_hhi_718_, lean_object* v_pivot_719_, lean_object* v_as_720_, lean_object* v_i_721_, lean_object* v_k_722_, lean_object* v_ilo_723_, lean_object* v_ik_724_, lean_object* v_w_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_717_, v_pivot_719_, v_as_720_, v_i_721_, v_k_722_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object* v_n_727_, lean_object* v_lo_728_, lean_object* v_hi_729_, lean_object* v_hhi_730_, lean_object* v_pivot_731_, lean_object* v_as_732_, lean_object* v_i_733_, lean_object* v_k_734_, lean_object* v_ilo_735_, lean_object* v_ik_736_, lean_object* v_w_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_n_727_, v_lo_728_, v_hi_729_, v_hhi_730_, v_pivot_731_, v_as_732_, v_i_733_, v_k_734_, v_ilo_735_, v_ik_736_, v_w_737_);
lean_dec_ref(v_pivot_731_);
lean_dec(v_hi_729_);
lean_dec(v_lo_728_);
lean_dec(v_n_727_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(lean_object* v_00_u03b2_739_, lean_object* v_a_740_, lean_object* v_m_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_740_, v_m_741_, v_a_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(lean_object* v_00_u03b2_744_, lean_object* v_key_745_, lean_object* v_as_746_, size_t v_sz_747_, size_t v_i_748_, lean_object* v_b_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_745_, v_as_746_, v_sz_747_, v_i_748_, v_b_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(lean_object* v_00_u03b2_751_, lean_object* v_key_752_, lean_object* v_as_753_, lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_b_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_758_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(v_00_u03b2_751_, v_key_752_, v_as_753_, v_sz_boxed_757_, v_i_boxed_758_, v_b_756_);
lean_dec_ref(v_as_753_);
return v_res_759_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_760_, lean_object* v_a_761_, lean_object* v_x_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_764_, lean_object* v_a_765_, lean_object* v_x_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(v_00_u03b2_764_, v_a_765_, v_x_766_);
lean_dec(v_x_766_);
lean_dec_ref(v_a_765_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_769_, lean_object* v_data_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_data_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_x_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_773_, v_a_774_, v_x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_777_, lean_object* v_i_778_, lean_object* v_source_779_, lean_object* v_target_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v_i_778_, v_source_779_, v_target_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_x_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object* v_fileMap_786_, lean_object* v_hoverPos_787_, lean_object* v_cmdStx_788_, lean_object* v_infoTree_789_){
_start:
{
lean_object* v___x_790_; lean_object* v_fst_791_; lean_object* v_snd_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_802_; 
v___x_790_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_786_, v_hoverPos_787_, v_cmdStx_788_, v_infoTree_789_);
v_fst_791_ = lean_ctor_get(v___x_790_, 0);
v_snd_792_ = lean_ctor_get(v___x_790_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_802_ == 0)
{
v___x_794_ = v___x_790_;
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snd_792_);
lean_inc(v_fst_791_);
lean_dec(v___x_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_partitions_798_; lean_object* v___x_800_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = l_Array_zipIdx___redArg(v_fst_791_, v___x_796_);
v_partitions_798_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_797_);
lean_dec_ref(v___x_797_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v_partitions_798_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_partitions_798_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_snd_792_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
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
