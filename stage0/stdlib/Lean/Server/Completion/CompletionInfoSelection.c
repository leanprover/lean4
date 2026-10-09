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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*);
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
uint8_t l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_x_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
switch(lean_obj_tag(v_a_14_))
{
case 0:
{
if (lean_obj_tag(v_a_15_) == 0)
{
lean_object* v_termInfo_16_; lean_object* v_toElabInfo_17_; lean_object* v_termInfo_18_; lean_object* v_toElabInfo_19_; lean_object* v_expr_20_; lean_object* v_stx_21_; lean_object* v_expr_22_; lean_object* v_stx_23_; uint8_t v___x_24_; 
v_termInfo_16_ = lean_ctor_get(v_a_14_, 0);
lean_inc_ref(v_termInfo_16_);
lean_dec_ref_known(v_a_14_, 2);
v_toElabInfo_17_ = lean_ctor_get(v_termInfo_16_, 0);
lean_inc_ref(v_toElabInfo_17_);
v_termInfo_18_ = lean_ctor_get(v_a_15_, 0);
lean_inc_ref(v_termInfo_18_);
lean_dec_ref_known(v_a_15_, 2);
v_toElabInfo_19_ = lean_ctor_get(v_termInfo_18_, 0);
lean_inc_ref(v_toElabInfo_19_);
v_expr_20_ = lean_ctor_get(v_termInfo_16_, 3);
lean_inc_ref(v_expr_20_);
lean_dec_ref(v_termInfo_16_);
v_stx_21_ = lean_ctor_get(v_toElabInfo_17_, 1);
lean_inc(v_stx_21_);
lean_dec_ref(v_toElabInfo_17_);
v_expr_22_ = lean_ctor_get(v_termInfo_18_, 3);
lean_inc_ref(v_expr_22_);
lean_dec_ref(v_termInfo_18_);
v_stx_23_ = lean_ctor_get(v_toElabInfo_19_, 1);
lean_inc(v_stx_23_);
lean_dec_ref(v_toElabInfo_19_);
v___x_24_ = l_Lean_Syntax_eqWithInfo(v_stx_21_, v_stx_23_);
if (v___x_24_ == 0)
{
lean_dec_ref(v_expr_22_);
lean_dec_ref(v_expr_20_);
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = lean_expr_eqv(v_expr_20_, v_expr_22_);
lean_dec_ref(v_expr_22_);
lean_dec_ref(v_expr_20_);
return v___x_25_;
}
}
else
{
uint8_t v___x_26_; 
lean_dec_ref_known(v_a_14_, 2);
lean_dec_ref(v_a_15_);
v___x_26_ = 0;
return v___x_26_;
}
}
case 3:
{
if (lean_obj_tag(v_a_15_) == 3)
{
lean_object* v_stx_27_; lean_object* v_id_28_; lean_object* v_structName_29_; lean_object* v_stx_30_; lean_object* v_id_31_; lean_object* v_structName_32_; uint8_t v___y_34_; uint8_t v___x_36_; 
v_stx_27_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_27_);
v_id_28_ = lean_ctor_get(v_a_14_, 1);
lean_inc(v_id_28_);
v_structName_29_ = lean_ctor_get(v_a_14_, 3);
lean_inc(v_structName_29_);
lean_dec_ref_known(v_a_14_, 4);
v_stx_30_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_stx_30_);
v_id_31_ = lean_ctor_get(v_a_15_, 1);
lean_inc(v_id_31_);
v_structName_32_ = lean_ctor_get(v_a_15_, 3);
lean_inc(v_structName_32_);
lean_dec_ref_known(v_a_15_, 4);
v___x_36_ = l_Lean_Syntax_eqWithInfo(v_stx_27_, v_stx_30_);
if (v___x_36_ == 0)
{
lean_dec(v_id_31_);
lean_dec(v_id_28_);
v___y_34_ = v___x_36_;
goto v___jp_33_;
}
else
{
uint8_t v___x_37_; 
v___x_37_ = l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_id_28_, v_id_31_);
lean_dec(v_id_31_);
lean_dec(v_id_28_);
v___y_34_ = v___x_37_;
goto v___jp_33_;
}
v___jp_33_:
{
if (v___y_34_ == 0)
{
lean_dec(v_structName_32_);
lean_dec(v_structName_29_);
return v___y_34_;
}
else
{
uint8_t v___x_35_; 
v___x_35_ = lean_name_eq(v_structName_29_, v_structName_32_);
lean_dec(v_structName_32_);
lean_dec(v_structName_29_);
return v___x_35_;
}
}
}
else
{
uint8_t v___x_38_; 
lean_dec_ref_known(v_a_14_, 4);
lean_dec_ref(v_a_15_);
v___x_38_ = 0;
return v___x_38_;
}
}
case 4:
{
if (lean_obj_tag(v_a_15_) == 4)
{
lean_object* v_stx_39_; lean_object* v_stx_40_; uint8_t v___x_41_; 
v_stx_39_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_39_);
lean_dec_ref_known(v_a_14_, 1);
v_stx_40_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_stx_40_);
lean_dec_ref_known(v_a_15_, 1);
v___x_41_ = l_Lean_Syntax_eqWithInfo(v_stx_39_, v_stx_40_);
return v___x_41_;
}
else
{
uint8_t v___x_42_; 
lean_dec_ref_known(v_a_14_, 1);
lean_dec_ref(v_a_15_);
v___x_42_ = 0;
return v___x_42_;
}
}
case 5:
{
if (lean_obj_tag(v_a_15_) == 5)
{
lean_object* v_stx_43_; lean_object* v_stx_44_; uint8_t v___x_45_; 
v_stx_43_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_43_);
lean_dec_ref_known(v_a_14_, 1);
v_stx_44_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_stx_44_);
lean_dec_ref_known(v_a_15_, 1);
v___x_45_ = l_Lean_Syntax_eqWithInfo(v_stx_43_, v_stx_44_);
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
lean_dec_ref_known(v_a_14_, 1);
lean_dec_ref(v_a_15_);
v___x_46_ = 0;
return v___x_46_;
}
}
case 6:
{
if (lean_obj_tag(v_a_15_) == 6)
{
lean_object* v_stx_47_; lean_object* v_stx_48_; uint8_t v___x_49_; 
v_stx_47_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_47_);
lean_dec_ref_known(v_a_14_, 2);
v_stx_48_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_stx_48_);
lean_dec_ref_known(v_a_15_, 2);
v___x_49_ = l_Lean_Syntax_eqWithInfo(v_stx_47_, v_stx_48_);
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
lean_dec_ref_known(v_a_14_, 2);
lean_dec_ref(v_a_15_);
v___x_50_ = 0;
return v___x_50_;
}
}
case 7:
{
if (lean_obj_tag(v_a_15_) == 7)
{
lean_object* v_stx_51_; lean_object* v_stx_52_; uint8_t v___x_53_; 
v_stx_51_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_51_);
lean_dec_ref_known(v_a_14_, 3);
v_stx_52_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_stx_52_);
lean_dec_ref_known(v_a_15_, 3);
v___x_53_ = l_Lean_Syntax_eqWithInfo(v_stx_51_, v_stx_52_);
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
lean_dec_ref_known(v_a_14_, 3);
lean_dec_ref(v_a_15_);
v___x_54_ = 0;
return v___x_54_;
}
}
case 8:
{
if (lean_obj_tag(v_a_15_) == 8)
{
lean_object* v_stx_55_; lean_object* v_stx_56_; uint8_t v___x_57_; 
v_stx_55_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_55_);
lean_dec_ref_known(v_a_14_, 1);
v_stx_56_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_stx_56_);
lean_dec_ref_known(v_a_15_, 1);
v___x_57_ = l_Lean_Syntax_eqWithInfo(v_stx_55_, v_stx_56_);
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
lean_dec_ref_known(v_a_14_, 1);
lean_dec_ref(v_a_15_);
v___x_58_ = 0;
return v___x_58_;
}
}
default: 
{
if (lean_obj_tag(v_a_15_) == 1)
{
lean_object* v_stx_59_; lean_object* v_id_60_; lean_object* v_stx_61_; lean_object* v_id_62_; uint8_t v___x_63_; 
v_stx_59_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_59_);
v_id_60_ = lean_ctor_get(v_a_14_, 1);
lean_inc(v_id_60_);
lean_dec_ref(v_a_14_);
v_stx_61_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_stx_61_);
v_id_62_ = lean_ctor_get(v_a_15_, 1);
lean_inc(v_id_62_);
lean_dec_ref_known(v_a_15_, 4);
v___x_63_ = l_Lean_Syntax_eqWithInfo(v_stx_59_, v_stx_61_);
if (v___x_63_ == 0)
{
lean_dec(v_id_62_);
lean_dec(v_id_60_);
return v___x_63_;
}
else
{
uint8_t v___x_64_; 
v___x_64_ = lean_name_eq(v_id_60_, v_id_62_);
lean_dec(v_id_62_);
lean_dec(v_id_60_);
return v___x_64_;
}
}
else
{
uint8_t v___x_65_; 
lean_dec_ref(v_a_15_);
lean_dec_ref(v_a_14_);
v___x_65_ = 0;
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_14_ = stack[0].m_obj;
lean_object* v_a_15_ = stack[1].m_obj;
uint8_t v_res_66_;
v_res_66_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_a_14_, v_a_15_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq___boxed(lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_a_67_, v_a_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(lean_object* v_a_71_, lean_object* v_as_72_, size_t v_i_73_, size_t v_stop_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = lean_usize_dec_eq(v_i_73_, v_stop_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v_info_77_; lean_object* v_info_78_; uint8_t v___x_79_; 
v___x_76_ = lean_array_uget_borrowed(v_as_72_, v_i_73_);
v_info_77_ = lean_ctor_get(v___x_76_, 2);
v_info_78_ = lean_ctor_get(v_a_71_, 2);
lean_inc_ref(v_info_78_);
lean_inc_ref(v_info_77_);
v___x_79_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_info_77_, v_info_78_);
if (v___x_79_ == 0)
{
size_t v___x_80_; size_t v___x_81_; 
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_add(v_i_73_, v___x_80_);
v_i_73_ = v___x_81_;
goto _start;
}
else
{
lean_dec_ref(v_a_71_);
return v___x_79_;
}
}
else
{
uint8_t v___x_83_; 
lean_dec_ref(v_a_71_);
v___x_83_ = 0;
return v___x_83_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_71_ = stack[0].m_obj;
lean_object* v_as_72_ = stack[1].m_obj;
size_t v_i_73_ = stack[2].m_num;
size_t v_stop_74_ = stack[3].m_num;
uint8_t v_res_84_;
v_res_84_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_71_, v_as_72_, v_i_73_, v_stop_74_);
stack->m_num = v_res_84_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0___boxed(lean_object* v_a_85_, lean_object* v_as_86_, lean_object* v_i_87_, lean_object* v_stop_88_){
_start:
{
size_t v_i_boxed_89_; size_t v_stop_boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_i_boxed_89_ = lean_unbox_usize(v_i_87_);
lean_dec(v_i_87_);
v_stop_boxed_90_ = lean_unbox_usize(v_stop_88_);
lean_dec(v_stop_88_);
v_res_91_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_85_, v_as_86_, v_i_boxed_89_, v_stop_boxed_90_);
lean_dec_ref(v_as_86_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(lean_object* v_as_93_, size_t v_sz_94_, size_t v_i_95_, lean_object* v_b_96_){
_start:
{
lean_object* v_a_98_; uint8_t v___x_102_; 
v___x_102_ = lean_usize_dec_lt(v_i_95_, v_sz_94_);
if (v___x_102_ == 0)
{
return v_b_96_;
}
else
{
lean_object* v_a_103_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_a_103_ = lean_array_uget_borrowed(v_as_93_, v_i_95_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_array_get_size(v_b_96_);
v___x_108_ = lean_nat_dec_lt(v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
goto v___jp_104_;
}
else
{
if (v___x_108_ == 0)
{
goto v___jp_104_;
}
else
{
size_t v___x_109_; size_t v___x_110_; uint8_t v___x_111_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_107_);
lean_inc(v_a_103_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_103_, v_b_96_, v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
goto v___jp_104_;
}
else
{
v_a_98_ = v_b_96_;
goto v___jp_97_;
}
}
}
v___jp_104_:
{
lean_object* v___x_105_; 
lean_inc(v_a_103_);
v___x_105_ = lean_array_push(v_b_96_, v_a_103_);
v_a_98_ = v___x_105_;
goto v___jp_97_;
}
}
v___jp_97_:
{
size_t v___x_99_; size_t v___x_100_; 
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_add(v_i_95_, v___x_99_);
v_i_95_ = v___x_100_;
v_b_96_ = v_a_98_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_93_ = stack[0].m_obj;
size_t v_sz_94_ = stack[1].m_num;
size_t v_i_95_ = stack[2].m_num;
lean_object* v_b_96_ = stack[3].m_obj;
lean_object* v_res_112_;
v_res_112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_as_93_, v_sz_94_, v_i_95_, v_b_96_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1___boxed(lean_object* v_as_113_, lean_object* v_sz_114_, lean_object* v_i_115_, lean_object* v_b_116_){
_start:
{
size_t v_sz_boxed_117_; size_t v_i_boxed_118_; lean_object* v_res_119_; 
v_sz_boxed_117_ = lean_unbox_usize(v_sz_114_);
lean_dec(v_sz_114_);
v_i_boxed_118_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_res_119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_as_113_, v_sz_boxed_117_, v_i_boxed_118_, v_b_116_);
lean_dec_ref(v_as_113_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(lean_object* v_infos_122_){
_start:
{
lean_object* v_deduplicatedInfos_123_; size_t v_sz_124_; size_t v___x_125_; lean_object* v___x_126_; 
v_deduplicatedInfos_123_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
v_sz_124_ = lean_array_size(v_infos_122_);
v___x_125_ = ((size_t)0ULL);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_infos_122_, v_sz_124_, v___x_125_, v_deduplicatedInfos_123_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___boxed(lean_object* v_infos_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_infos_127_);
lean_dec_ref(v_infos_127_);
return v_res_128_;
}
}
uint8_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(lean_object* v_hoverPos_129_, lean_object* v_i_130_){
_start:
{
if (lean_obj_tag(v_i_130_) == 5)
{
lean_object* v_stx_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_stx_143_ = lean_ctor_get(v_i_130_, 0);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Lean_Syntax_getArg(v_stx_143_, v___x_144_);
v___x_146_ = l_Lean_Syntax_isMissing(v___x_145_);
lean_dec(v___x_145_);
if (v___x_146_ == 0)
{
goto v___jp_134_;
}
else
{
lean_object* v___x_147_; 
lean_inc(v_stx_143_);
lean_dec_ref_known(v_i_130_, 1);
v___x_147_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_143_, v___x_146_);
lean_dec(v_stx_143_);
if (lean_obj_tag(v___x_147_) == 1)
{
lean_object* v_val_148_; uint8_t v___x_149_; uint8_t v___x_150_; 
v_val_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = 0;
v___x_150_ = l_Lean_Syntax_Range_contains(v_val_148_, v_hoverPos_129_, v___x_149_);
lean_dec(v_val_148_);
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
lean_dec(v___x_147_);
v___x_151_ = 0;
return v___x_151_;
}
}
}
else
{
goto v___jp_134_;
}
v___jp_131_:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_132_, 0, v_i_130_);
v___x_133_ = l_Lean_Elab_Info_occursInOrOnBoundary(v___x_132_, v_hoverPos_129_);
lean_dec_ref_known(v___x_132_, 1);
return v___x_133_;
}
v___jp_134_:
{
if (lean_obj_tag(v_i_130_) == 7)
{
lean_object* v_id_x3f_135_; 
v_id_x3f_135_ = lean_ctor_get(v_i_130_, 1);
if (lean_obj_tag(v_id_x3f_135_) == 0)
{
lean_object* v_stx_136_; uint8_t v___x_137_; lean_object* v___x_138_; 
v_stx_136_ = lean_ctor_get(v_i_130_, 0);
lean_inc(v_stx_136_);
lean_dec_ref_known(v_i_130_, 3);
v___x_137_ = 1;
v___x_138_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_136_, v___x_137_);
lean_dec(v_stx_136_);
if (lean_obj_tag(v___x_138_) == 1)
{
lean_object* v_val_139_; uint8_t v___x_140_; uint8_t v___x_141_; 
v_val_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = 0;
v___x_141_ = l_Lean_Syntax_Range_contains(v_val_139_, v_hoverPos_129_, v___x_140_);
lean_dec(v_val_139_);
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
lean_dec(v___x_138_);
v___x_142_ = 0;
return v___x_142_;
}
}
else
{
goto v___jp_131_;
}
}
else
{
goto v___jp_131_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_129_ = stack[0].m_obj;
lean_object* v_i_130_ = stack[1].m_obj;
uint8_t v_res_152_;
v_res_152_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_129_, v_i_130_);
stack->m_num = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos___boxed(lean_object* v_hoverPos_153_, lean_object* v_i_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_153_, v_i_154_);
lean_dec(v_hoverPos_153_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(lean_object* v_msg_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_panic_fn_borrowed(v___x_158_, v_msg_157_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2));
v___x_164_ = lean_unsigned_to_nat(14u);
v___x_165_ = lean_unsigned_to_nat(22u);
v___x_166_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1));
v___x_167_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0));
v___x_168_ = l_mkPanicMessageWithDecl(v___x_167_, v___x_166_, v___x_165_, v___x_164_, v___x_163_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(lean_object* v_fileMap_169_, lean_object* v_hoverPos_170_, lean_object* v_hoverLine_171_, lean_object* v_ctx_172_, lean_object* v_info_173_, lean_object* v_best_174_){
_start:
{
if (lean_obj_tag(v_info_173_) == 8)
{
lean_object* v_i_175_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_198_; uint8_t v___x_203_; 
v_i_175_ = lean_ctor_get(v_info_173_, 0);
lean_inc_ref_n(v_i_175_, 2);
v___x_203_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_170_, v_i_175_);
if (v___x_203_ == 0)
{
lean_dec_ref(v_i_175_);
lean_dec_ref_known(v_info_173_, 1);
lean_dec_ref(v_ctx_172_);
lean_dec_ref(v_fileMap_169_);
return v_best_174_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_Info_pos_x3f(v_info_173_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_206_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_205_);
v___y_198_ = v___x_206_;
goto v___jp_197_;
}
else
{
lean_object* v_val_207_; 
v_val_207_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_204_, 1);
v___y_198_ = v_val_207_;
goto v___jp_197_;
}
}
v___jp_176_:
{
lean_object* v___x_180_; lean_object* v_line_181_; lean_object* v___x_182_; lean_object* v_line_183_; uint8_t v___x_184_; 
lean_inc_ref(v_fileMap_169_);
v___x_180_ = l_Lean_FileMap_toPosition(v_fileMap_169_, v___y_178_);
lean_dec(v___y_178_);
v_line_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_line_181_);
lean_dec_ref(v___x_180_);
v___x_182_ = l_Lean_FileMap_toPosition(v_fileMap_169_, v___y_177_);
lean_dec(v___y_177_);
v_line_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_line_183_);
lean_dec_ref(v___x_182_);
v___x_184_ = lean_nat_dec_eq(v_line_181_, v_hoverLine_171_);
if (v___x_184_ == 0)
{
lean_dec(v_line_183_);
lean_dec(v_line_181_);
lean_dec(v___y_179_);
lean_dec_ref(v_i_175_);
lean_dec_ref(v_ctx_172_);
return v_best_174_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = lean_nat_dec_eq(v_line_181_, v_line_183_);
lean_dec(v_line_183_);
lean_dec(v_line_181_);
if (v___x_185_ == 0)
{
lean_dec(v___y_179_);
lean_dec_ref(v_i_175_);
lean_dec_ref(v_ctx_172_);
return v_best_174_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___y_179_);
lean_ctor_set(v___x_186_, 1, v_ctx_172_);
lean_ctor_set(v___x_186_, 2, v_i_175_);
v___x_187_ = lean_array_push(v_best_174_, v___x_186_);
return v___x_187_;
}
}
}
v___jp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_hoverPos_170_, v___x_191_);
v___x_193_ = lean_nat_dec_le(v___x_192_, v___y_190_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
v___y_177_ = v___y_190_;
v___y_178_ = v___y_189_;
v___y_179_ = v___x_194_;
goto v___jp_176_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_nat_sub(v_hoverPos_170_, v___y_189_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
v___y_177_ = v___y_190_;
v___y_178_ = v___y_189_;
v___y_179_ = v___x_196_;
goto v___jp_176_;
}
}
v___jp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_Info_tailPos_x3f(v_info_173_);
lean_dec_ref_known(v_info_173_, 1);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_201_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_200_);
v___y_189_ = v___y_198_;
v___y_190_ = v___x_201_;
goto v___jp_188_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_199_, 1);
v___y_189_ = v___y_198_;
v___y_190_ = v_val_202_;
goto v___jp_188_;
}
}
}
else
{
lean_dec_ref(v_info_173_);
lean_dec_ref(v_ctx_172_);
lean_dec_ref(v_fileMap_169_);
return v_best_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed(lean_object* v_fileMap_208_, lean_object* v_hoverPos_209_, lean_object* v_hoverLine_210_, lean_object* v_ctx_211_, lean_object* v_info_212_, lean_object* v_best_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(v_fileMap_208_, v_hoverPos_209_, v_hoverLine_210_, v_ctx_211_, v_info_212_, v_best_213_);
lean_dec(v_hoverLine_210_);
lean_dec(v_hoverPos_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object* v_fileMap_215_, lean_object* v_hoverPos_216_, lean_object* v_cmdStx_217_, lean_object* v_infoTree_218_){
_start:
{
uint8_t v_isComplete_220_; lean_object* v_completionInfoCandidates_221_; lean_object* v___x_225_; lean_object* v_line_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_completionInfoCandidates_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
lean_inc_ref_n(v_fileMap_215_, 2);
v___x_225_ = l_Lean_FileMap_toPosition(v_fileMap_215_, v_hoverPos_216_);
v_line_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_line_226_);
lean_dec_ref(v___x_225_);
lean_inc(v_hoverPos_216_);
v___x_227_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed), 6, 3);
lean_closure_set(v___x_227_, 0, v_fileMap_215_);
lean_closure_set(v___x_227_, 1, v_hoverPos_216_);
lean_closure_set(v___x_227_, 2, v_line_226_);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
lean_inc_ref(v_infoTree_218_);
v_completionInfoCandidates_230_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___x_227_, v___x_229_, v_infoTree_218_);
v___x_231_ = lean_array_get_size(v_completionInfoCandidates_230_);
v___x_232_ = lean_nat_dec_eq(v___x_231_, v___x_228_);
if (v___x_232_ == 0)
{
uint8_t v_isComplete_233_; 
lean_dec_ref(v_infoTree_218_);
lean_dec(v_cmdStx_217_);
lean_dec(v_hoverPos_216_);
lean_dec_ref(v_fileMap_215_);
v_isComplete_233_ = 1;
v_isComplete_220_ = v_isComplete_233_;
v_completionInfoCandidates_221_ = v_completionInfoCandidates_230_;
goto v___jp_219_;
}
else
{
lean_object* v_completionInfoCandidates_234_; uint8_t v_isComplete_235_; 
lean_dec(v_completionInfoCandidates_230_);
v_completionInfoCandidates_234_ = l_Lean_Server_Completion_findSyntheticCompletions(v_fileMap_215_, v_hoverPos_216_, v_cmdStx_217_, v_infoTree_218_);
v_isComplete_235_ = 0;
v_isComplete_220_ = v_isComplete_235_;
v_completionInfoCandidates_221_ = v_completionInfoCandidates_234_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_completionInfoCandidates_221_);
lean_dec_ref(v_completionInfoCandidates_221_);
v___x_223_ = lean_box(v_isComplete_220_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(lean_object* v_x_236_){
_start:
{
lean_object* v_fst_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_252_; 
v_fst_237_ = lean_ctor_get(v_x_236_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_x_236_, 1);
lean_dec(v_unused_253_);
v___x_239_ = v_x_236_;
v_isShared_240_ = v_isSharedCheck_252_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_fst_237_);
lean_dec(v_x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_252_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_info_241_; uint8_t v___y_243_; 
v_info_241_ = lean_ctor_get(v_fst_237_, 2);
lean_inc_ref(v_info_241_);
lean_dec(v_fst_237_);
if (lean_obj_tag(v_info_241_) == 1)
{
uint8_t v___x_250_; 
v___x_250_ = 1;
v___y_243_ = v___x_250_;
goto v___jp_242_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = 0;
v___y_243_ = v___x_251_;
goto v___jp_242_;
}
v___jp_242_:
{
lean_object* v___x_244_; lean_object* v_size_x3f_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_244_, 0, v_info_241_);
v_size_x3f_245_ = l_Lean_Elab_Info_size_x3f(v___x_244_);
lean_dec_ref_known(v___x_244_, 1);
v___x_246_ = lean_box(v___y_243_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v_size_x3f_245_);
lean_ctor_set(v___x_239_, 0, v___x_246_);
v___x_248_ = v___x_239_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_size_x3f_245_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
return v_x_254_;
}
else
{
lean_object* v_key_256_; lean_object* v_value_257_; lean_object* v_tail_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_key_256_ = lean_ctor_get(v_x_255_, 0);
v_value_257_ = lean_ctor_get(v_x_255_, 1);
v_tail_258_ = lean_ctor_get(v_x_255_, 2);
lean_inc(v_value_257_);
lean_inc(v_key_256_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_key_256_);
lean_ctor_set(v___x_259_, 1, v_value_257_);
v___x_260_ = lean_array_push(v_x_254_, v___x_259_);
v_x_254_ = v___x_260_;
v_x_255_ = v_tail_258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_x_262_, v_x_263_);
lean_dec(v_x_263_);
return v_res_264_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(lean_object* v_as_265_, size_t v_i_266_, size_t v_stop_267_, lean_object* v_b_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_usize_dec_eq(v_i_266_, v_stop_267_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; size_t v___x_272_; size_t v___x_273_; 
v___x_270_ = lean_array_uget_borrowed(v_as_265_, v_i_266_);
v___x_271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_b_268_, v___x_270_);
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_add(v_i_266_, v___x_272_);
v_i_266_ = v___x_273_;
v_b_268_ = v___x_271_;
goto _start;
}
else
{
return v_b_268_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_265_ = stack[0].m_obj;
size_t v_i_266_ = stack[1].m_num;
size_t v_stop_267_ = stack[2].m_num;
lean_object* v_b_268_ = stack[3].m_obj;
lean_object* v_res_275_;
v_res_275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_265_, v_i_266_, v_stop_267_, v_b_268_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4___boxed(lean_object* v_as_276_, lean_object* v_i_277_, lean_object* v_stop_278_, lean_object* v_b_279_){
_start:
{
size_t v_i_boxed_280_; size_t v_stop_boxed_281_; lean_object* v_res_282_; 
v_i_boxed_280_ = lean_unbox_usize(v_i_277_);
lean_dec(v_i_277_);
v_stop_boxed_281_ = lean_unbox_usize(v_stop_278_);
lean_dec(v_stop_278_);
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_276_, v_i_boxed_280_, v_stop_boxed_281_, v_b_279_);
lean_dec_ref(v_as_276_);
return v_res_282_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t v_sz_283_, size_t v_i_284_, lean_object* v_bs_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = lean_usize_dec_lt(v_i_284_, v_sz_283_);
if (v___x_286_ == 0)
{
return v_bs_285_;
}
else
{
lean_object* v_v_287_; lean_object* v_snd_288_; lean_object* v___x_289_; lean_object* v_bs_x27_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v___x_293_; 
v_v_287_ = lean_array_uget_borrowed(v_bs_285_, v_i_284_);
v_snd_288_ = lean_ctor_get(v_v_287_, 1);
lean_inc(v_snd_288_);
v___x_289_ = lean_unsigned_to_nat(0u);
v_bs_x27_290_ = lean_array_uset(v_bs_285_, v_i_284_, v___x_289_);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_284_, v___x_291_);
v___x_293_ = lean_array_uset(v_bs_x27_290_, v_i_284_, v_snd_288_);
v_i_284_ = v___x_292_;
v_bs_285_ = v___x_293_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_283_ = stack[0].m_num;
size_t v_i_284_ = stack[1].m_num;
lean_object* v_bs_285_ = stack[2].m_obj;
lean_object* v_res_295_;
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_283_, v_i_284_, v_bs_285_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object* v_sz_296_, lean_object* v_i_297_, lean_object* v_bs_298_){
_start:
{
size_t v_sz_boxed_299_; size_t v_i_boxed_300_; lean_object* v_res_301_; 
v_sz_boxed_299_ = lean_unbox_usize(v_sz_296_);
lean_dec(v_sz_296_);
v_i_boxed_300_ = lean_unbox_usize(v_i_297_);
lean_dec(v_i_297_);
v_res_301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_299_, v_i_boxed_300_, v_bs_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object* v_hi_302_, lean_object* v_pivot_303_, lean_object* v_as_304_, lean_object* v_i_305_, lean_object* v_k_306_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = lean_nat_dec_lt(v_k_306_, v_hi_302_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_k_306_);
v___x_318_ = lean_array_fswap(v_as_304_, v_i_305_, v_hi_302_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_i_305_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v_fst_321_; lean_object* v_fst_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v_fst_325_; lean_object* v_snd_326_; 
v___x_320_ = lean_array_fget_borrowed(v_as_304_, v_k_306_);
v_fst_321_ = lean_ctor_get(v___x_320_, 0);
v_fst_322_ = lean_ctor_get(v_pivot_303_, 0);
v_fst_323_ = lean_ctor_get(v_fst_321_, 0);
v_snd_324_ = lean_ctor_get(v_fst_321_, 1);
v_fst_325_ = lean_ctor_get(v_fst_322_, 0);
v_snd_326_ = lean_ctor_get(v_fst_322_, 1);
if (lean_obj_tag(v_snd_324_) == 0)
{
if (lean_obj_tag(v_snd_326_) == 1)
{
goto v___jp_307_;
}
else
{
goto v___jp_333_;
}
}
else
{
if (lean_obj_tag(v_snd_326_) == 0)
{
goto v___jp_311_;
}
else
{
goto v___jp_333_;
}
}
v___jp_327_:
{
if (lean_obj_tag(v_snd_324_) == 1)
{
if (lean_obj_tag(v_snd_326_) == 1)
{
lean_object* v_val_328_; lean_object* v_val_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_val_328_ = lean_ctor_get(v_snd_324_, 0);
v_val_329_ = lean_ctor_get(v_snd_326_, 0);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_val_328_, v___x_330_);
v___x_332_ = lean_nat_dec_le(v___x_331_, v_val_329_);
lean_dec(v___x_331_);
if (v___x_332_ == 0)
{
goto v___jp_307_;
}
else
{
goto v___jp_311_;
}
}
else
{
goto v___jp_307_;
}
}
else
{
goto v___jp_307_;
}
}
v___jp_333_:
{
uint8_t v___x_334_; 
v___x_334_ = lean_unbox(v_fst_323_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = lean_unbox(v_fst_325_);
if (v___x_335_ == 1)
{
goto v___jp_311_;
}
else
{
goto v___jp_327_;
}
}
else
{
uint8_t v___x_336_; 
v___x_336_ = lean_unbox(v_fst_325_);
if (v___x_336_ == 0)
{
goto v___jp_307_;
}
else
{
goto v___jp_327_;
}
}
}
}
v___jp_307_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_k_306_, v___x_308_);
lean_dec(v_k_306_);
v_k_306_ = v___x_309_;
goto _start;
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_array_fswap(v_as_304_, v_i_305_, v_k_306_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_i_305_, v___x_313_);
lean_dec(v_i_305_);
v___x_315_ = lean_nat_add(v_k_306_, v___x_313_);
lean_dec(v_k_306_);
v_as_304_ = v___x_312_;
v_i_305_ = v___x_314_;
v_k_306_ = v___x_315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(lean_object* v_hi_337_, lean_object* v_pivot_338_, lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_k_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_337_, v_pivot_338_, v_as_339_, v_i_340_, v_k_341_);
lean_dec_ref(v_pivot_338_);
lean_dec(v_hi_337_);
return v_res_342_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(uint8_t v___x_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_fst_346_; lean_object* v_fst_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; 
v_fst_346_ = lean_ctor_get(v_x_344_, 0);
v_fst_347_ = lean_ctor_get(v_x_345_, 0);
v_fst_348_ = lean_ctor_get(v_fst_346_, 0);
v_snd_349_ = lean_ctor_get(v_fst_346_, 1);
v_fst_350_ = lean_ctor_get(v_fst_347_, 0);
v_snd_351_ = lean_ctor_get(v_fst_347_, 1);
if (lean_obj_tag(v_snd_349_) == 0)
{
if (lean_obj_tag(v_snd_351_) == 1)
{
uint8_t v___x_366_; 
v___x_366_ = 0;
return v___x_366_;
}
else
{
goto v___jp_360_;
}
}
else
{
if (lean_obj_tag(v_snd_351_) == 0)
{
return v___x_343_;
}
else
{
goto v___jp_360_;
}
}
v___jp_352_:
{
if (lean_obj_tag(v_snd_349_) == 1)
{
if (lean_obj_tag(v_snd_351_) == 1)
{
lean_object* v_val_353_; lean_object* v_val_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_val_353_ = lean_ctor_get(v_snd_349_, 0);
v_val_354_ = lean_ctor_get(v_snd_351_, 0);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_val_353_, v___x_355_);
v___x_357_ = lean_nat_dec_le(v___x_356_, v_val_354_);
lean_dec(v___x_356_);
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
}
else
{
uint8_t v___x_359_; 
v___x_359_ = 0;
return v___x_359_;
}
}
v___jp_360_:
{
uint8_t v___x_361_; 
v___x_361_ = lean_unbox(v_fst_348_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
v___x_362_ = lean_unbox(v_fst_350_);
if (v___x_362_ == 1)
{
uint8_t v___x_363_; 
v___x_363_ = lean_unbox(v_fst_350_);
return v___x_363_;
}
else
{
goto v___jp_352_;
}
}
else
{
uint8_t v___x_364_; 
v___x_364_ = lean_unbox(v_fst_350_);
if (v___x_364_ == 0)
{
uint8_t v___x_365_; 
v___x_365_ = lean_unbox(v_fst_350_);
return v___x_365_;
}
else
{
goto v___jp_352_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_343_ = stack[0].m_num;
lean_object* v_x_344_ = stack[1].m_obj;
lean_object* v_x_345_ = stack[2].m_obj;
uint8_t v_res_367_;
v_res_367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_343_, v_x_344_, v_x_345_);
stack->m_num = v_res_367_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0___boxed(lean_object* v___x_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
uint8_t v___x_2449__boxed_371_; uint8_t v_res_372_; lean_object* v_r_373_; 
v___x_2449__boxed_371_ = lean_unbox(v___x_368_);
v_res_372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_2449__boxed_371_, v_x_369_, v_x_370_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_x_369_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(lean_object* v_n_374_, lean_object* v_as_375_, lean_object* v_lo_376_, lean_object* v_hi_377_){
_start:
{
lean_object* v___y_379_; uint8_t v___x_389_; 
v___x_389_ = lean_nat_dec_lt(v_lo_376_, v_hi_377_);
if (v___x_389_ == 0)
{
lean_dec(v_lo_376_);
return v_as_375_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_mid_392_; lean_object* v___y_394_; lean_object* v___y_400_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_390_ = lean_nat_add(v_lo_376_, v_hi_377_);
v___x_391_ = lean_unsigned_to_nat(1u);
v_mid_392_ = lean_nat_shiftr(v___x_390_, v___x_391_);
lean_dec(v___x_390_);
v___x_405_ = lean_array_fget_borrowed(v_as_375_, v_mid_392_);
v___x_406_ = lean_array_fget_borrowed(v_as_375_, v_lo_376_);
v___x_407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_389_, v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
v___y_400_ = v_as_375_;
goto v___jp_399_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_array_fswap(v_as_375_, v_lo_376_, v_mid_392_);
v___y_400_ = v___x_408_;
goto v___jp_399_;
}
v___jp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = lean_array_fget_borrowed(v___y_394_, v_mid_392_);
v___x_396_ = lean_array_fget_borrowed(v___y_394_, v_hi_377_);
v___x_397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_389_, v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v_mid_392_);
v___y_379_ = v___y_394_;
goto v___jp_378_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_array_fswap(v___y_394_, v_mid_392_, v_hi_377_);
lean_dec(v_mid_392_);
v___y_379_ = v___x_398_;
goto v___jp_378_;
}
}
v___jp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_401_ = lean_array_fget_borrowed(v___y_400_, v_hi_377_);
v___x_402_ = lean_array_fget_borrowed(v___y_400_, v_lo_376_);
v___x_403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_389_, v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
v___y_394_ = v___y_400_;
goto v___jp_393_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_array_fswap(v___y_400_, v_lo_376_, v_hi_377_);
v___y_394_ = v___x_404_;
goto v___jp_393_;
}
}
}
v___jp_378_:
{
lean_object* v_pivot_380_; lean_object* v___x_381_; lean_object* v_fst_382_; lean_object* v_snd_383_; uint8_t v___x_384_; 
v_pivot_380_ = lean_array_fget(v___y_379_, v_hi_377_);
lean_inc_n(v_lo_376_, 2);
v___x_381_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_377_, v_pivot_380_, v___y_379_, v_lo_376_, v_lo_376_);
lean_dec(v_pivot_380_);
v_fst_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_fst_382_);
v_snd_383_ = lean_ctor_get(v___x_381_, 1);
lean_inc(v_snd_383_);
lean_dec_ref(v___x_381_);
v___x_384_ = lean_nat_dec_le(v_hi_377_, v_fst_382_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_374_, v_snd_383_, v_lo_376_, v_fst_382_);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_fst_382_, v___x_386_);
lean_dec(v_fst_382_);
v_as_375_ = v___x_385_;
v_lo_376_ = v___x_387_;
goto _start;
}
else
{
lean_dec(v_fst_382_);
lean_dec(v_lo_376_);
return v_snd_383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(lean_object* v_n_409_, lean_object* v_as_410_, lean_object* v_lo_411_, lean_object* v_hi_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_409_, v_as_410_, v_lo_411_, v_hi_412_);
lean_dec(v_hi_412_);
lean_dec(v_n_409_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
return v_x_414_;
}
else
{
lean_object* v_key_416_; lean_object* v_value_417_; lean_object* v_tail_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_456_; 
v_key_416_ = lean_ctor_get(v_x_415_, 0);
v_value_417_ = lean_ctor_get(v_x_415_, 1);
v_tail_418_ = lean_ctor_get(v_x_415_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_456_ == 0)
{
v___x_420_ = v_x_415_;
v_isShared_421_ = v_isSharedCheck_456_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_tail_418_);
lean_inc(v_value_417_);
lean_inc(v_key_416_);
lean_dec(v_x_415_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_456_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_424_; uint64_t v___y_426_; uint64_t v___y_427_; uint64_t v___y_447_; uint8_t v___x_453_; 
v_fst_422_ = lean_ctor_get(v_key_416_, 0);
v_snd_423_ = lean_ctor_get(v_key_416_, 1);
v___x_424_ = lean_array_get_size(v_x_414_);
v___x_453_ = lean_unbox(v_fst_422_);
if (v___x_453_ == 0)
{
uint64_t v___x_454_; 
v___x_454_ = 13ULL;
v___y_447_ = v___x_454_;
goto v___jp_446_;
}
else
{
uint64_t v___x_455_; 
v___x_455_ = 11ULL;
v___y_447_ = v___x_455_;
goto v___jp_446_;
}
v___jp_425_:
{
uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v_fold_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_428_ = lean_uint64_mix_hash(v___y_426_, v___y_427_);
v___x_429_ = 32ULL;
v___x_430_ = lean_uint64_shift_right(v___x_428_, v___x_429_);
v_fold_431_ = lean_uint64_xor(v___x_428_, v___x_430_);
v___x_432_ = 16ULL;
v___x_433_ = lean_uint64_shift_right(v_fold_431_, v___x_432_);
v___x_434_ = lean_uint64_xor(v_fold_431_, v___x_433_);
v___x_435_ = lean_uint64_to_usize(v___x_434_);
v___x_436_ = lean_usize_of_nat(v___x_424_);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_sub(v___x_436_, v___x_437_);
v___x_439_ = lean_usize_land(v___x_435_, v___x_438_);
v___x_440_ = lean_array_uget_borrowed(v_x_414_, v___x_439_);
lean_inc(v___x_440_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 2, v___x_440_);
v___x_442_ = v___x_420_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_key_416_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_value_417_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v___x_440_);
v___x_442_ = v_reuseFailAlloc_445_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; 
v___x_443_ = lean_array_uset(v_x_414_, v___x_439_, v___x_442_);
v_x_414_ = v___x_443_;
v_x_415_ = v_tail_418_;
goto _start;
}
}
v___jp_446_:
{
if (lean_obj_tag(v_snd_423_) == 0)
{
uint64_t v___x_448_; 
v___x_448_ = 11ULL;
v___y_426_ = v___y_447_;
v___y_427_ = v___x_448_;
goto v___jp_425_;
}
else
{
lean_object* v_val_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; 
v_val_449_ = lean_ctor_get(v_snd_423_, 0);
v___x_450_ = l_String_instHashableRaw_hash(v_val_449_);
v___x_451_ = 13ULL;
v___x_452_ = lean_uint64_mix_hash(v___x_450_, v___x_451_);
v___y_426_ = v___y_447_;
v___y_427_ = v___x_452_;
goto v___jp_425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_i_457_, lean_object* v_source_458_, lean_object* v_target_459_){
_start:
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_array_get_size(v_source_458_);
v___x_461_ = lean_nat_dec_lt(v_i_457_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec_ref(v_source_458_);
lean_dec(v_i_457_);
return v_target_459_;
}
else
{
lean_object* v_es_462_; lean_object* v___x_463_; lean_object* v_source_464_; lean_object* v_target_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_es_462_ = lean_array_fget(v_source_458_, v_i_457_);
v___x_463_ = lean_box(0);
v_source_464_ = lean_array_fset(v_source_458_, v_i_457_, v___x_463_);
v_target_465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_target_459_, v_es_462_);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_i_457_, v___x_466_);
lean_dec(v_i_457_);
v_i_457_ = v___x_467_;
v_source_458_ = v_source_464_;
v_target_459_ = v_target_465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(lean_object* v_data_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_nbuckets_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_470_ = lean_array_get_size(v_data_469_);
v___x_471_ = lean_unsigned_to_nat(2u);
v_nbuckets_472_ = lean_nat_mul(v___x_470_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_box(0);
v___x_475_ = lean_mk_array(v_nbuckets_472_, v___x_474_);
v___x_476_ = lean_array_propagate_mark(v_data_469_, v___x_475_);
v___x_477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v___x_473_, v_data_469_, v___x_476_);
return v___x_477_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
if (lean_obj_tag(v_x_479_) == 0)
{
uint8_t v___x_480_; 
v___x_480_ = 1;
return v___x_480_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
}
else
{
if (lean_obj_tag(v_x_479_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
else
{
lean_object* v_val_483_; lean_object* v_val_484_; uint8_t v_decide_485_; 
v_val_483_ = lean_ctor_get(v_x_478_, 0);
v_val_484_ = lean_ctor_get(v_x_479_, 0);
v_decide_485_ = lean_nat_dec_eq(v_val_483_, v_val_484_);
return v_decide_485_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_478_ = stack[0].m_obj;
lean_object* v_x_479_ = stack[1].m_obj;
uint8_t v_res_486_;
v_res_486_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_478_, v_x_479_);
stack->m_num = v_res_486_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_487_, v_x_488_);
lean_dec(v_x_488_);
lean_dec(v_x_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(lean_object* v_a_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
uint8_t v___x_493_; 
v___x_493_ = 0;
return v___x_493_;
}
else
{
lean_object* v_key_494_; lean_object* v_tail_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; uint8_t v___x_503_; 
v_key_494_ = lean_ctor_get(v_x_492_, 0);
v_tail_495_ = lean_ctor_get(v_x_492_, 2);
v_fst_496_ = lean_ctor_get(v_key_494_, 0);
v_snd_497_ = lean_ctor_get(v_key_494_, 1);
v_fst_498_ = lean_ctor_get(v_a_491_, 0);
v_snd_499_ = lean_ctor_get(v_a_491_, 1);
v___x_503_ = lean_unbox(v_fst_498_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = lean_unbox(v_fst_496_);
if (v___x_504_ == 0)
{
goto v___jp_500_;
}
else
{
v_x_492_ = v_tail_495_;
goto _start;
}
}
else
{
uint8_t v___x_506_; 
v___x_506_ = lean_unbox(v_fst_496_);
if (v___x_506_ == 0)
{
v_x_492_ = v_tail_495_;
goto _start;
}
else
{
goto v___jp_500_;
}
}
v___jp_500_:
{
uint8_t v___x_501_; 
v___x_501_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_497_, v_snd_499_);
if (v___x_501_ == 0)
{
v_x_492_ = v_tail_495_;
goto _start;
}
else
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_491_ = stack[0].m_obj;
lean_object* v_x_492_ = stack[1].m_obj;
uint8_t v_res_508_;
v_res_508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_491_, v_x_492_);
stack->m_num = v_res_508_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_509_, v_x_510_);
lean_dec(v_x_510_);
lean_dec_ref(v_a_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___y_518_; 
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v___x_521_; 
v___x_521_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___y_518_ = v___x_521_;
goto v___jp_517_;
}
else
{
lean_object* v_val_522_; 
v_val_522_ = lean_ctor_get(v_x_516_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_x_516_, 1);
v___y_518_ = v_val_522_;
goto v___jp_517_;
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_array_push(v___y_518_, v_a_515_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
if (lean_obj_tag(v_x_525_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_val_528_; lean_object* v___x_529_; 
v___x_526_ = lean_box(0);
v___x_527_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_523_, v___x_526_);
v_val_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_val_528_);
lean_dec(v___x_527_);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v_a_524_);
lean_ctor_set(v___x_529_, 1, v_val_528_);
lean_ctor_set(v___x_529_, 2, v_x_525_);
return v___x_529_;
}
else
{
lean_object* v_key_530_; lean_object* v_value_531_; lean_object* v_tail_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_554_; 
v_key_530_ = lean_ctor_get(v_x_525_, 0);
v_value_531_ = lean_ctor_get(v_x_525_, 1);
v_tail_532_ = lean_ctor_get(v_x_525_, 2);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_525_);
if (v_isSharedCheck_554_ == 0)
{
v___x_534_ = v_x_525_;
v_isShared_535_ = v_isSharedCheck_554_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_tail_532_);
lean_inc(v_value_531_);
lean_inc(v_key_530_);
lean_dec(v_x_525_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_554_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v_fst_543_; lean_object* v_snd_544_; uint8_t v___x_551_; 
v_fst_541_ = lean_ctor_get(v_key_530_, 0);
v_snd_542_ = lean_ctor_get(v_key_530_, 1);
v_fst_543_ = lean_ctor_get(v_a_524_, 0);
v_snd_544_ = lean_ctor_get(v_a_524_, 1);
v___x_551_ = lean_unbox(v_fst_543_);
if (v___x_551_ == 0)
{
uint8_t v___x_552_; 
v___x_552_ = lean_unbox(v_fst_541_);
if (v___x_552_ == 0)
{
goto v___jp_545_;
}
else
{
goto v___jp_536_;
}
}
else
{
uint8_t v___x_553_; 
v___x_553_ = lean_unbox(v_fst_541_);
if (v___x_553_ == 0)
{
goto v___jp_536_;
}
else
{
goto v___jp_545_;
}
}
v___jp_536_:
{
lean_object* v_tail_537_; lean_object* v___x_539_; 
v_tail_537_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_523_, v_a_524_, v_tail_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 2, v_tail_537_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_key_530_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_value_531_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_tail_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
v___jp_545_:
{
uint8_t v___x_546_; 
v___x_546_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_542_, v_snd_544_);
if (v___x_546_ == 0)
{
goto v___jp_536_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_val_549_; lean_object* v___x_550_; 
lean_del_object(v___x_534_);
lean_dec(v_key_530_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v_value_531_);
v___x_548_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_523_, v___x_547_);
v_val_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_549_);
lean_dec(v___x_548_);
v___x_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_550_, 0, v_a_524_);
lean_ctor_set(v___x_550_, 1, v_val_549_);
lean_ctor_set(v___x_550_, 2, v_tail_532_);
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(lean_object* v_a_555_, lean_object* v_m_556_, lean_object* v_a_557_){
_start:
{
size_t v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v_size_565_; lean_object* v_buckets_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_625_; 
v_size_565_ = lean_ctor_get(v_m_556_, 0);
v_buckets_566_ = lean_ctor_get(v_m_556_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_m_556_);
if (v_isSharedCheck_625_ == 0)
{
v___x_568_ = v_m_556_;
v_isShared_569_ = v_isSharedCheck_625_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_buckets_566_);
lean_inc(v_size_565_);
lean_dec(v_m_556_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_625_;
goto v_resetjp_567_;
}
v___jp_558_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_array_uset(v___y_561_, v___y_559_, v___y_560_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___y_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
return v___x_564_;
}
v_resetjp_567_:
{
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; uint64_t v___y_574_; uint64_t v___y_575_; uint64_t v___y_616_; uint8_t v___x_622_; 
v_fst_570_ = lean_ctor_get(v_a_557_, 0);
v_snd_571_ = lean_ctor_get(v_a_557_, 1);
v___x_572_ = lean_array_get_size(v_buckets_566_);
v___x_622_ = lean_unbox(v_fst_570_);
if (v___x_622_ == 0)
{
uint64_t v___x_623_; 
v___x_623_ = 13ULL;
v___y_616_ = v___x_623_;
goto v___jp_615_;
}
else
{
uint64_t v___x_624_; 
v___x_624_ = 11ULL;
v___y_616_ = v___x_624_;
goto v___jp_615_;
}
v___jp_573_:
{
uint64_t v___x_576_; uint64_t v___x_577_; uint64_t v___x_578_; uint64_t v_fold_579_; uint64_t v___x_580_; uint64_t v___x_581_; uint64_t v___x_582_; size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; lean_object* v_bkt_588_; uint8_t v___x_589_; 
v___x_576_ = lean_uint64_mix_hash(v___y_574_, v___y_575_);
v___x_577_ = 32ULL;
v___x_578_ = lean_uint64_shift_right(v___x_576_, v___x_577_);
v_fold_579_ = lean_uint64_xor(v___x_576_, v___x_578_);
v___x_580_ = 16ULL;
v___x_581_ = lean_uint64_shift_right(v_fold_579_, v___x_580_);
v___x_582_ = lean_uint64_xor(v_fold_579_, v___x_581_);
v___x_583_ = lean_uint64_to_usize(v___x_582_);
v___x_584_ = lean_usize_of_nat(v___x_572_);
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_sub(v___x_584_, v___x_585_);
v___x_587_ = lean_usize_land(v___x_583_, v___x_586_);
v_bkt_588_ = lean_array_uget_borrowed(v_buckets_566_, v___x_587_);
v___x_589_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_557_, v_bkt_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_size_x27_593_; lean_object* v___x_594_; lean_object* v_buckets_x27_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_590_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___x_591_ = lean_array_push(v___x_590_, v_a_555_);
v___x_592_ = lean_unsigned_to_nat(1u);
v_size_x27_593_ = lean_nat_add(v_size_565_, v___x_592_);
lean_dec(v_size_565_);
lean_inc(v_bkt_588_);
v___x_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_594_, 0, v_a_557_);
lean_ctor_set(v___x_594_, 1, v___x_591_);
lean_ctor_set(v___x_594_, 2, v_bkt_588_);
v_buckets_x27_595_ = lean_array_uset(v_buckets_566_, v___x_587_, v___x_594_);
v___x_596_ = lean_unsigned_to_nat(4u);
v___x_597_ = lean_nat_mul(v_size_x27_593_, v___x_596_);
v___x_598_ = lean_unsigned_to_nat(3u);
v___x_599_ = lean_nat_div(v___x_597_, v___x_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_array_get_size(v_buckets_x27_595_);
v___x_601_ = lean_nat_dec_le(v___x_599_, v___x_600_);
lean_dec(v___x_599_);
if (v___x_601_ == 0)
{
lean_object* v_val_602_; lean_object* v___x_604_; 
v_val_602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_buckets_x27_595_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v_val_602_);
lean_ctor_set(v___x_568_, 0, v_size_x27_593_);
v___x_604_ = v___x_568_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_size_x27_593_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_val_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
lean_object* v___x_607_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v_buckets_x27_595_);
lean_ctor_set(v___x_568_, 0, v_size_x27_593_);
v___x_607_ = v___x_568_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_size_x27_593_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_buckets_x27_595_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v___x_609_; lean_object* v_buckets_x27_610_; lean_object* v_bkt_x27_611_; uint8_t v___x_612_; 
lean_inc(v_bkt_588_);
lean_del_object(v___x_568_);
v___x_609_ = lean_box(0);
v_buckets_x27_610_ = lean_array_uset(v_buckets_566_, v___x_587_, v___x_609_);
lean_inc_ref(v_a_557_);
v_bkt_x27_611_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_555_, v_a_557_, v_bkt_588_);
v___x_612_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_557_, v_bkt_x27_611_);
lean_dec_ref(v_a_557_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_sub(v_size_565_, v___x_613_);
lean_dec(v_size_565_);
v___y_559_ = v___x_587_;
v___y_560_ = v_bkt_x27_611_;
v___y_561_ = v_buckets_x27_610_;
v___y_562_ = v___x_614_;
goto v___jp_558_;
}
else
{
v___y_559_ = v___x_587_;
v___y_560_ = v_bkt_x27_611_;
v___y_561_ = v_buckets_x27_610_;
v___y_562_ = v_size_565_;
goto v___jp_558_;
}
}
}
v___jp_615_:
{
if (lean_obj_tag(v_snd_571_) == 0)
{
uint64_t v___x_617_; 
v___x_617_ = 11ULL;
v___y_574_ = v___y_616_;
v___y_575_ = v___x_617_;
goto v___jp_573_;
}
else
{
lean_object* v_val_618_; uint64_t v___x_619_; uint64_t v___x_620_; uint64_t v___x_621_; 
v_val_618_ = lean_ctor_get(v_snd_571_, 0);
v___x_619_ = l_String_instHashableRaw_hash(v_val_618_);
v___x_620_ = 13ULL;
v___x_621_ = lean_uint64_mix_hash(v___x_619_, v___x_620_);
v___y_574_ = v___y_616_;
v___y_575_ = v___x_621_;
goto v___jp_573_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(lean_object* v_key_626_, lean_object* v_as_627_, size_t v_sz_628_, size_t v_i_629_, lean_object* v_b_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_lt(v_i_629_, v_sz_628_);
if (v___x_631_ == 0)
{
lean_dec_ref(v_key_626_);
return v_b_630_;
}
else
{
lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; size_t v___x_635_; size_t v___x_636_; 
v_a_632_ = lean_array_uget_borrowed(v_as_627_, v_i_629_);
lean_inc_ref(v_key_626_);
lean_inc_n(v_a_632_, 2);
v___x_633_ = lean_apply_1(v_key_626_, v_a_632_);
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_632_, v_b_630_, v___x_633_);
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_add(v_i_629_, v___x_635_);
v_i_629_ = v___x_636_;
v_b_630_ = v___x_634_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_626_ = stack[0].m_obj;
lean_object* v_as_627_ = stack[1].m_obj;
size_t v_sz_628_ = stack[2].m_num;
size_t v_i_629_ = stack[3].m_num;
lean_object* v_b_630_ = stack[4].m_obj;
lean_object* v_res_638_;
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_626_, v_as_627_, v_sz_628_, v_i_629_, v_b_630_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg___boxed(lean_object* v_key_639_, lean_object* v_as_640_, lean_object* v_sz_641_, lean_object* v_i_642_, lean_object* v_b_643_){
_start:
{
size_t v_sz_boxed_644_; size_t v_i_boxed_645_; lean_object* v_res_646_; 
v_sz_boxed_644_ = lean_unbox_usize(v_sz_641_);
lean_dec(v_sz_641_);
v_i_boxed_645_ = lean_unbox_usize(v_i_642_);
lean_dec(v_i_642_);
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_639_, v_as_640_, v_sz_boxed_644_, v_i_boxed_645_, v_b_643_);
lean_dec_ref(v_as_640_);
return v_res_646_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_box(0);
v___x_648_ = lean_unsigned_to_nat(16u);
v___x_649_ = lean_mk_array(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_groups_652_; 
v___x_650_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0);
v___x_651_ = lean_unsigned_to_nat(0u);
v_groups_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_652_, 0, v___x_651_);
lean_ctor_set(v_groups_652_, 1, v___x_650_);
return v_groups_652_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(lean_object* v_key_653_, lean_object* v_xs_654_){
_start:
{
lean_object* v_groups_655_; size_t v_sz_656_; size_t v___x_657_; lean_object* v___x_658_; 
v_groups_655_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1);
v_sz_656_ = lean_array_size(v_xs_654_);
v___x_657_ = ((size_t)0ULL);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_653_, v_xs_654_, v_sz_656_, v___x_657_, v_groups_655_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(lean_object* v_key_659_, lean_object* v_xs_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_659_, v_xs_660_);
lean_dec_ref(v_xs_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object* v_items_663_){
_start:
{
lean_object* v___y_665_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_682_; lean_object* v___f_689_; lean_object* v_partitions_690_; lean_object* v_size_691_; lean_object* v_buckets_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___f_689_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0));
v_partitions_690_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v___f_689_, v_items_663_);
v_size_691_ = lean_ctor_get(v_partitions_690_, 0);
lean_inc(v_size_691_);
v_buckets_692_ = lean_ctor_get(v_partitions_690_, 1);
lean_inc_ref(v_buckets_692_);
lean_dec_ref(v_partitions_690_);
v___x_693_ = lean_mk_empty_array_with_capacity(v_size_691_);
lean_dec(v_size_691_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_array_get_size(v_buckets_692_);
v___x_696_ = lean_nat_dec_lt(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec_ref(v_buckets_692_);
v___y_682_ = v___x_693_;
goto v___jp_681_;
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_695_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_692_, v___x_697_, v___x_698_, v___x_693_);
lean_dec_ref(v_buckets_692_);
v___y_682_ = v___x_699_;
goto v___jp_681_;
}
v___jp_664_:
{
size_t v_sz_666_; size_t v___x_667_; lean_object* v___x_668_; 
v_sz_666_ = lean_array_size(v___y_665_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_666_, v___x_667_, v___y_665_);
return v___x_668_;
}
v___jp_669_:
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v___y_672_, v___y_670_, v___y_671_, v___y_673_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
v___y_665_ = v___x_674_;
goto v___jp_664_;
}
v___jp_675_:
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_le(v___y_679_, v___y_677_);
if (v___x_680_ == 0)
{
lean_dec(v___y_677_);
lean_inc(v___y_679_);
v___y_670_ = v___y_676_;
v___y_671_ = v___y_679_;
v___y_672_ = v___y_678_;
v___y_673_ = v___y_679_;
goto v___jp_669_;
}
else
{
v___y_670_ = v___y_676_;
v___y_671_ = v___y_679_;
v___y_672_ = v___y_678_;
v___y_673_ = v___y_677_;
goto v___jp_669_;
}
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_array_get_size(v___y_682_);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_nat_dec_eq(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_sub(v___x_683_, v___x_686_);
v___x_688_ = lean_nat_dec_le(v___x_684_, v___x_687_);
if (v___x_688_ == 0)
{
lean_inc(v___x_687_);
v___y_676_ = v___y_682_;
v___y_677_ = v___x_687_;
v___y_678_ = v___x_683_;
v___y_679_ = v___x_687_;
goto v___jp_675_;
}
else
{
v___y_676_ = v___y_682_;
v___y_677_ = v___x_687_;
v___y_678_ = v___x_683_;
v___y_679_ = v___x_684_;
goto v___jp_675_;
}
}
else
{
v___y_665_ = v___y_682_;
goto v___jp_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object* v_items_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_700_);
lean_dec_ref(v_items_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object* v_n_702_, lean_object* v_as_703_, lean_object* v_lo_704_, lean_object* v_hi_705_, lean_object* v_w_706_, lean_object* v_hlo_707_, lean_object* v_hhi_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_702_, v_as_703_, v_lo_704_, v_hi_705_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object* v_n_710_, lean_object* v_as_711_, lean_object* v_lo_712_, lean_object* v_hi_713_, lean_object* v_w_714_, lean_object* v_hlo_715_, lean_object* v_hhi_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_n_710_, v_as_711_, v_lo_712_, v_hi_713_, v_w_714_, v_hlo_715_, v_hhi_716_);
lean_dec(v_hi_713_);
lean_dec(v_n_710_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object* v_00_u03b2_718_, lean_object* v_key_719_, lean_object* v_xs_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_719_, v_xs_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object* v_00_u03b2_722_, lean_object* v_key_723_, lean_object* v_xs_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_00_u03b2_722_, v_key_723_, v_xs_724_);
lean_dec_ref(v_xs_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object* v_n_726_, lean_object* v_lo_727_, lean_object* v_hi_728_, lean_object* v_hhi_729_, lean_object* v_pivot_730_, lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_k_733_, lean_object* v_ilo_734_, lean_object* v_ik_735_, lean_object* v_w_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_728_, v_pivot_730_, v_as_731_, v_i_732_, v_k_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object* v_n_738_, lean_object* v_lo_739_, lean_object* v_hi_740_, lean_object* v_hhi_741_, lean_object* v_pivot_742_, lean_object* v_as_743_, lean_object* v_i_744_, lean_object* v_k_745_, lean_object* v_ilo_746_, lean_object* v_ik_747_, lean_object* v_w_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_n_738_, v_lo_739_, v_hi_740_, v_hhi_741_, v_pivot_742_, v_as_743_, v_i_744_, v_k_745_, v_ilo_746_, v_ik_747_, v_w_748_);
lean_dec_ref(v_pivot_742_);
lean_dec(v_hi_740_);
lean_dec(v_lo_739_);
lean_dec(v_n_738_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(lean_object* v_00_u03b2_750_, lean_object* v_a_751_, lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_751_, v_m_752_, v_a_753_);
return v___x_754_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(lean_object* v_00_u03b2_755_, lean_object* v_key_756_, lean_object* v_as_757_, size_t v_sz_758_, size_t v_i_759_, lean_object* v_b_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_756_, v_as_757_, v_sz_758_, v_i_759_, v_b_760_);
return v___x_761_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_756_ = stack[1].m_obj;
lean_object* v_as_757_ = stack[2].m_obj;
size_t v_sz_758_ = stack[3].m_num;
size_t v_i_759_ = stack[4].m_num;
lean_object* v_b_760_ = stack[5].m_obj;
lean_object* v_res_762_;
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(lean_box(0), v_key_756_, v_as_757_, v_sz_758_, v_i_759_, v_b_760_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(lean_object* v_00_u03b2_763_, lean_object* v_key_764_, lean_object* v_as_765_, lean_object* v_sz_766_, lean_object* v_i_767_, lean_object* v_b_768_){
_start:
{
size_t v_sz_boxed_769_; size_t v_i_boxed_770_; lean_object* v_res_771_; 
v_sz_boxed_769_ = lean_unbox_usize(v_sz_766_);
lean_dec(v_sz_766_);
v_i_boxed_770_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(v_00_u03b2_763_, v_key_764_, v_as_765_, v_sz_boxed_769_, v_i_boxed_770_, v_b_768_);
lean_dec_ref(v_as_765_);
return v_res_771_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_772_, lean_object* v_a_773_, lean_object* v_x_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_773_, v_x_774_);
return v___x_775_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_773_ = stack[1].m_obj;
lean_object* v_x_774_ = stack[2].m_obj;
uint8_t v_res_776_;
v_res_776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(lean_box(0), v_a_773_, v_x_774_);
stack->m_num = v_res_776_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_777_, lean_object* v_a_778_, lean_object* v_x_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(v_00_u03b2_777_, v_a_778_, v_x_779_);
lean_dec(v_x_779_);
lean_dec_ref(v_a_778_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_782_, lean_object* v_data_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_data_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_786_, v_a_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_790_, lean_object* v_i_791_, lean_object* v_source_792_, lean_object* v_target_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v_i_791_, v_source_792_, v_target_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_x_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object* v_fileMap_799_, lean_object* v_hoverPos_800_, lean_object* v_cmdStx_801_, lean_object* v_infoTree_802_){
_start:
{
lean_object* v___x_803_; lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v___x_803_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_799_, v_hoverPos_800_, v_cmdStx_801_, v_infoTree_802_);
v_fst_804_ = lean_ctor_get(v___x_803_, 0);
v_snd_805_ = lean_ctor_get(v___x_803_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v___x_803_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_inc(v_fst_804_);
lean_dec(v___x_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_partitions_811_; lean_object* v___x_813_; 
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = l_Array_zipIdx___redArg(v_fst_804_, v___x_809_);
v_partitions_811_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_810_);
lean_dec_ref(v___x_810_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v_partitions_811_);
v___x_813_ = v___x_807_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_partitions_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_snd_805_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
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
