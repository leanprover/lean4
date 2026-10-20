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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_x_9_, v_x_10_);
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
lean_object* v_stx_26_; lean_object* v_id_27_; lean_object* v_structName_28_; lean_object* v_stx_29_; lean_object* v_id_30_; lean_object* v_structName_31_; uint8_t v___x_32_; 
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
v___x_32_ = l_Lean_Syntax_eqWithInfo(v_stx_26_, v_stx_29_);
if (v___x_32_ == 0)
{
lean_dec(v_structName_31_);
lean_dec(v_id_30_);
lean_dec(v_structName_28_);
lean_dec(v_id_27_);
return v___x_32_;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = l_instBEqOption_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_id_27_, v_id_30_);
lean_dec(v_id_30_);
lean_dec(v_id_27_);
if (v___x_33_ == 0)
{
lean_dec(v_structName_31_);
lean_dec(v_structName_28_);
return v___x_33_;
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
uint8_t v___x_35_; 
lean_dec_ref_known(v_a_13_, 4);
lean_dec_ref(v_a_14_);
v___x_35_ = 0;
return v___x_35_;
}
}
case 4:
{
if (lean_obj_tag(v_a_14_) == 4)
{
lean_object* v_stx_36_; lean_object* v_stx_37_; uint8_t v___x_38_; 
v_stx_36_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_36_);
lean_dec_ref_known(v_a_13_, 1);
v_stx_37_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_37_);
lean_dec_ref_known(v_a_14_, 1);
v___x_38_ = l_Lean_Syntax_eqWithInfo(v_stx_36_, v_stx_37_);
return v___x_38_;
}
else
{
uint8_t v___x_39_; 
lean_dec_ref_known(v_a_13_, 1);
lean_dec_ref(v_a_14_);
v___x_39_ = 0;
return v___x_39_;
}
}
case 5:
{
if (lean_obj_tag(v_a_14_) == 5)
{
lean_object* v_stx_40_; lean_object* v_stx_41_; uint8_t v___x_42_; 
v_stx_40_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_40_);
lean_dec_ref_known(v_a_13_, 1);
v_stx_41_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_41_);
lean_dec_ref_known(v_a_14_, 1);
v___x_42_ = l_Lean_Syntax_eqWithInfo(v_stx_40_, v_stx_41_);
return v___x_42_;
}
else
{
uint8_t v___x_43_; 
lean_dec_ref_known(v_a_13_, 1);
lean_dec_ref(v_a_14_);
v___x_43_ = 0;
return v___x_43_;
}
}
case 6:
{
if (lean_obj_tag(v_a_14_) == 6)
{
lean_object* v_stx_44_; lean_object* v_stx_45_; uint8_t v___x_46_; 
v_stx_44_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_44_);
lean_dec_ref_known(v_a_13_, 2);
v_stx_45_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_45_);
lean_dec_ref_known(v_a_14_, 2);
v___x_46_ = l_Lean_Syntax_eqWithInfo(v_stx_44_, v_stx_45_);
return v___x_46_;
}
else
{
uint8_t v___x_47_; 
lean_dec_ref_known(v_a_13_, 2);
lean_dec_ref(v_a_14_);
v___x_47_ = 0;
return v___x_47_;
}
}
case 7:
{
if (lean_obj_tag(v_a_14_) == 7)
{
lean_object* v_stx_48_; lean_object* v_stx_49_; uint8_t v___x_50_; 
v_stx_48_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_48_);
lean_dec_ref_known(v_a_13_, 3);
v_stx_49_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_49_);
lean_dec_ref_known(v_a_14_, 3);
v___x_50_ = l_Lean_Syntax_eqWithInfo(v_stx_48_, v_stx_49_);
return v___x_50_;
}
else
{
uint8_t v___x_51_; 
lean_dec_ref_known(v_a_13_, 3);
lean_dec_ref(v_a_14_);
v___x_51_ = 0;
return v___x_51_;
}
}
case 8:
{
if (lean_obj_tag(v_a_14_) == 8)
{
lean_object* v_stx_52_; lean_object* v_stx_53_; uint8_t v___x_54_; 
v_stx_52_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_52_);
lean_dec_ref_known(v_a_13_, 1);
v_stx_53_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_53_);
lean_dec_ref_known(v_a_14_, 1);
v___x_54_ = l_Lean_Syntax_eqWithInfo(v_stx_52_, v_stx_53_);
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
lean_dec_ref_known(v_a_13_, 1);
lean_dec_ref(v_a_14_);
v___x_55_ = 0;
return v___x_55_;
}
}
default: 
{
if (lean_obj_tag(v_a_14_) == 1)
{
lean_object* v_stx_56_; lean_object* v_id_57_; lean_object* v_stx_58_; lean_object* v_id_59_; uint8_t v___x_60_; 
v_stx_56_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_stx_56_);
v_id_57_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_id_57_);
lean_dec_ref(v_a_13_);
v_stx_58_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_stx_58_);
v_id_59_ = lean_ctor_get(v_a_14_, 1);
lean_inc(v_id_59_);
lean_dec_ref_known(v_a_14_, 4);
v___x_60_ = l_Lean_Syntax_eqWithInfo(v_stx_56_, v_stx_58_);
if (v___x_60_ == 0)
{
lean_dec(v_id_59_);
lean_dec(v_id_57_);
return v___x_60_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = lean_name_eq(v_id_57_, v_id_59_);
lean_dec(v_id_59_);
lean_dec(v_id_57_);
return v___x_61_;
}
}
else
{
uint8_t v___x_62_; 
lean_dec_ref(v_a_14_);
lean_dec_ref(v_a_13_);
v___x_62_ = 0;
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq___boxed(lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_a_63_, v_a_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(lean_object* v_a_67_, lean_object* v_as_68_, size_t v_i_69_, size_t v_stop_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = lean_usize_dec_eq(v_i_69_, v_stop_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v_info_73_; lean_object* v_info_74_; uint8_t v___x_75_; 
v___x_72_ = lean_array_uget_borrowed(v_as_68_, v_i_69_);
v_info_73_ = lean_ctor_get(v___x_72_, 2);
v_info_74_ = lean_ctor_get(v_a_67_, 2);
lean_inc_ref(v_info_74_);
lean_inc_ref(v_info_73_);
v___x_75_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_info_73_, v_info_74_);
if (v___x_75_ == 0)
{
size_t v___x_76_; size_t v___x_77_; 
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_add(v_i_69_, v___x_76_);
v_i_69_ = v___x_77_;
goto _start;
}
else
{
lean_dec_ref(v_a_67_);
return v___x_75_;
}
}
else
{
uint8_t v___x_79_; 
lean_dec_ref(v_a_67_);
v___x_79_ = 0;
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0___boxed(lean_object* v_a_80_, lean_object* v_as_81_, lean_object* v_i_82_, lean_object* v_stop_83_){
_start:
{
size_t v_i_boxed_84_; size_t v_stop_boxed_85_; uint8_t v_res_86_; lean_object* v_r_87_; 
v_i_boxed_84_ = lean_unbox_usize(v_i_82_);
lean_dec(v_i_82_);
v_stop_boxed_85_ = lean_unbox_usize(v_stop_83_);
lean_dec(v_stop_83_);
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_80_, v_as_81_, v_i_boxed_84_, v_stop_boxed_85_);
lean_dec_ref(v_as_81_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(lean_object* v_as_88_, size_t v_sz_89_, size_t v_i_90_, lean_object* v_b_91_){
_start:
{
lean_object* v_a_93_; uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_lt(v_i_90_, v_sz_89_);
if (v___x_97_ == 0)
{
return v_b_91_;
}
else
{
lean_object* v_a_98_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_a_98_ = lean_array_uget_borrowed(v_as_88_, v_i_90_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v_b_91_);
v___x_103_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
goto v___jp_99_;
}
else
{
if (v___x_103_ == 0)
{
goto v___jp_99_;
}
else
{
size_t v___x_104_; size_t v___x_105_; uint8_t v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_102_);
lean_inc(v_a_98_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_98_, v_b_91_, v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
goto v___jp_99_;
}
else
{
v_a_93_ = v_b_91_;
goto v___jp_92_;
}
}
}
v___jp_99_:
{
lean_object* v___x_100_; 
lean_inc(v_a_98_);
v___x_100_ = lean_array_push(v_b_91_, v_a_98_);
v_a_93_ = v___x_100_;
goto v___jp_92_;
}
}
v___jp_92_:
{
size_t v___x_94_; size_t v___x_95_; 
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_add(v_i_90_, v___x_94_);
v_i_90_ = v___x_95_;
v_b_91_ = v_a_93_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1___boxed(lean_object* v_as_107_, lean_object* v_sz_108_, lean_object* v_i_109_, lean_object* v_b_110_){
_start:
{
size_t v_sz_boxed_111_; size_t v_i_boxed_112_; lean_object* v_res_113_; 
v_sz_boxed_111_ = lean_unbox_usize(v_sz_108_);
lean_dec(v_sz_108_);
v_i_boxed_112_ = lean_unbox_usize(v_i_109_);
lean_dec(v_i_109_);
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_as_107_, v_sz_boxed_111_, v_i_boxed_112_, v_b_110_);
lean_dec_ref(v_as_107_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(lean_object* v_infos_116_){
_start:
{
lean_object* v_deduplicatedInfos_117_; size_t v_sz_118_; size_t v___x_119_; lean_object* v___x_120_; 
v_deduplicatedInfos_117_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
v_sz_118_ = lean_array_size(v_infos_116_);
v___x_119_ = ((size_t)0ULL);
v___x_120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_infos_116_, v_sz_118_, v___x_119_, v_deduplicatedInfos_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___boxed(lean_object* v_infos_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_infos_121_);
lean_dec_ref(v_infos_121_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(lean_object* v_hoverPos_123_, lean_object* v_i_124_){
_start:
{
if (lean_obj_tag(v_i_124_) == 5)
{
lean_object* v_stx_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_stx_137_ = lean_ctor_get(v_i_124_, 0);
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = l_Lean_Syntax_getArg(v_stx_137_, v___x_138_);
v___x_140_ = l_Lean_Syntax_isMissing(v___x_139_);
lean_dec(v___x_139_);
if (v___x_140_ == 0)
{
goto v___jp_128_;
}
else
{
lean_object* v___x_141_; 
lean_inc(v_stx_137_);
lean_dec_ref_known(v_i_124_, 1);
v___x_141_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_137_, v___x_140_);
lean_dec(v_stx_137_);
if (lean_obj_tag(v___x_141_) == 1)
{
lean_object* v_val_142_; uint8_t v___x_143_; uint8_t v___x_144_; 
v_val_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_val_142_);
lean_dec_ref_known(v___x_141_, 1);
v___x_143_ = 0;
v___x_144_ = l_Lean_Syntax_Range_contains(v_val_142_, v_hoverPos_123_, v___x_143_);
lean_dec(v_val_142_);
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
lean_dec(v___x_141_);
v___x_145_ = 0;
return v___x_145_;
}
}
}
else
{
goto v___jp_128_;
}
v___jp_125_:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_126_, 0, v_i_124_);
v___x_127_ = l_Lean_Elab_Info_occursInOrOnBoundary(v___x_126_, v_hoverPos_123_);
lean_dec_ref_known(v___x_126_, 1);
return v___x_127_;
}
v___jp_128_:
{
if (lean_obj_tag(v_i_124_) == 7)
{
lean_object* v_id_x3f_129_; 
v_id_x3f_129_ = lean_ctor_get(v_i_124_, 1);
if (lean_obj_tag(v_id_x3f_129_) == 0)
{
lean_object* v_stx_130_; uint8_t v___x_131_; lean_object* v___x_132_; 
v_stx_130_ = lean_ctor_get(v_i_124_, 0);
lean_inc(v_stx_130_);
lean_dec_ref_known(v_i_124_, 3);
v___x_131_ = 1;
v___x_132_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_130_, v___x_131_);
lean_dec(v_stx_130_);
if (lean_obj_tag(v___x_132_) == 1)
{
lean_object* v_val_133_; uint8_t v___x_134_; uint8_t v___x_135_; 
v_val_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v___x_132_, 1);
v___x_134_ = 0;
v___x_135_ = l_Lean_Syntax_Range_contains(v_val_133_, v_hoverPos_123_, v___x_134_);
lean_dec(v_val_133_);
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
lean_dec(v___x_132_);
v___x_136_ = 0;
return v___x_136_;
}
}
else
{
goto v___jp_125_;
}
}
else
{
goto v___jp_125_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos___boxed(lean_object* v_hoverPos_146_, lean_object* v_i_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_146_, v_i_147_);
lean_dec(v_hoverPos_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(lean_object* v_msg_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_panic_fn_borrowed(v___x_151_, v_msg_150_);
return v___x_152_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2));
v___x_157_ = lean_unsigned_to_nat(14u);
v___x_158_ = lean_unsigned_to_nat(22u);
v___x_159_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1));
v___x_160_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0));
v___x_161_ = l_mkPanicMessageWithDecl(v___x_160_, v___x_159_, v___x_158_, v___x_157_, v___x_156_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(lean_object* v_fileMap_162_, lean_object* v_hoverPos_163_, lean_object* v_hoverLine_164_, lean_object* v_ctx_165_, lean_object* v_info_166_, lean_object* v_best_167_){
_start:
{
if (lean_obj_tag(v_info_166_) == 8)
{
lean_object* v_i_168_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_191_; uint8_t v___x_196_; 
v_i_168_ = lean_ctor_get(v_info_166_, 0);
lean_inc_ref_n(v_i_168_, 2);
v___x_196_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_163_, v_i_168_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_i_168_);
lean_dec_ref_known(v_info_166_, 1);
lean_dec_ref(v_ctx_165_);
lean_dec_ref(v_fileMap_162_);
return v_best_167_;
}
else
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Elab_Info_pos_x3f(v_info_166_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_199_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_198_);
v___y_191_ = v___x_199_;
goto v___jp_190_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v___x_197_, 1);
v___y_191_ = v_val_200_;
goto v___jp_190_;
}
}
v___jp_169_:
{
lean_object* v___x_173_; lean_object* v_line_174_; lean_object* v___x_175_; lean_object* v_line_176_; uint8_t v___x_177_; 
lean_inc_ref(v_fileMap_162_);
v___x_173_ = l_Lean_FileMap_toPosition(v_fileMap_162_, v___y_171_);
lean_dec(v___y_171_);
v_line_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_line_174_);
lean_dec_ref(v___x_173_);
v___x_175_ = l_Lean_FileMap_toPosition(v_fileMap_162_, v___y_170_);
lean_dec(v___y_170_);
v_line_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_line_176_);
lean_dec_ref(v___x_175_);
v___x_177_ = lean_nat_dec_eq(v_line_174_, v_hoverLine_164_);
if (v___x_177_ == 0)
{
lean_dec(v_line_176_);
lean_dec(v_line_174_);
lean_dec(v___y_172_);
lean_dec_ref(v_i_168_);
lean_dec_ref(v_ctx_165_);
return v_best_167_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = lean_nat_dec_eq(v_line_174_, v_line_176_);
lean_dec(v_line_176_);
lean_dec(v_line_174_);
if (v___x_178_ == 0)
{
lean_dec(v___y_172_);
lean_dec_ref(v_i_168_);
lean_dec_ref(v_ctx_165_);
return v_best_167_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_179_, 0, v___y_172_);
lean_ctor_set(v___x_179_, 1, v_ctx_165_);
lean_ctor_set(v___x_179_, 2, v_i_168_);
v___x_180_ = lean_array_push(v_best_167_, v___x_179_);
return v___x_180_;
}
}
}
v___jp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_add(v_hoverPos_163_, v___x_184_);
v___x_186_ = lean_nat_dec_le(v___x_185_, v___y_183_);
lean_dec(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(0);
v___y_170_ = v___y_183_;
v___y_171_ = v___y_182_;
v___y_172_ = v___x_187_;
goto v___jp_169_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_nat_sub(v_hoverPos_163_, v___y_182_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___y_170_ = v___y_183_;
v___y_171_ = v___y_182_;
v___y_172_ = v___x_189_;
goto v___jp_169_;
}
}
v___jp_190_:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Elab_Info_tailPos_x3f(v_info_166_);
lean_dec_ref_known(v_info_166_, 1);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3, &l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once, _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
v___x_194_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_193_);
v___y_182_ = v___y_191_;
v___y_183_ = v___x_194_;
goto v___jp_181_;
}
else
{
lean_object* v_val_195_; 
v_val_195_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v___x_192_, 1);
v___y_182_ = v___y_191_;
v___y_183_ = v_val_195_;
goto v___jp_181_;
}
}
}
else
{
lean_dec_ref(v_info_166_);
lean_dec_ref(v_ctx_165_);
lean_dec_ref(v_fileMap_162_);
return v_best_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed(lean_object* v_fileMap_201_, lean_object* v_hoverPos_202_, lean_object* v_hoverLine_203_, lean_object* v_ctx_204_, lean_object* v_info_205_, lean_object* v_best_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(v_fileMap_201_, v_hoverPos_202_, v_hoverLine_203_, v_ctx_204_, v_info_205_, v_best_206_);
lean_dec(v_hoverLine_203_);
lean_dec(v_hoverPos_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object* v_fileMap_208_, lean_object* v_hoverPos_209_, lean_object* v_cmdStx_210_, lean_object* v_infoTree_211_){
_start:
{
uint8_t v_isComplete_213_; lean_object* v_completionInfoCandidates_214_; lean_object* v___x_218_; lean_object* v_line_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_completionInfoCandidates_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
lean_inc_ref_n(v_fileMap_208_, 2);
v___x_218_ = l_Lean_FileMap_toPosition(v_fileMap_208_, v_hoverPos_209_);
v_line_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_line_219_);
lean_dec_ref(v___x_218_);
lean_inc(v_hoverPos_209_);
v___x_220_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed), 6, 3);
lean_closure_set(v___x_220_, 0, v_fileMap_208_);
lean_closure_set(v___x_220_, 1, v_hoverPos_209_);
lean_closure_set(v___x_220_, 2, v_line_219_);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0));
lean_inc_ref(v_infoTree_211_);
v_completionInfoCandidates_223_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___x_220_, v___x_222_, v_infoTree_211_);
v___x_224_ = lean_array_get_size(v_completionInfoCandidates_223_);
v___x_225_ = lean_nat_dec_eq(v___x_224_, v___x_221_);
if (v___x_225_ == 0)
{
uint8_t v_isComplete_226_; 
lean_dec_ref(v_infoTree_211_);
lean_dec(v_cmdStx_210_);
lean_dec(v_hoverPos_209_);
lean_dec_ref(v_fileMap_208_);
v_isComplete_226_ = 1;
v_isComplete_213_ = v_isComplete_226_;
v_completionInfoCandidates_214_ = v_completionInfoCandidates_223_;
goto v___jp_212_;
}
else
{
lean_object* v_completionInfoCandidates_227_; uint8_t v_isComplete_228_; 
lean_dec(v_completionInfoCandidates_223_);
v_completionInfoCandidates_227_ = l_Lean_Server_Completion_findSyntheticCompletions(v_fileMap_208_, v_hoverPos_209_, v_cmdStx_210_, v_infoTree_211_);
v_isComplete_228_ = 0;
v_isComplete_213_ = v_isComplete_228_;
v_completionInfoCandidates_214_ = v_completionInfoCandidates_227_;
goto v___jp_212_;
}
v___jp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_completionInfoCandidates_214_);
lean_dec_ref(v_completionInfoCandidates_214_);
v___x_216_ = lean_box(v_isComplete_213_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(lean_object* v_x_229_){
_start:
{
lean_object* v_fst_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_245_; 
v_fst_230_ = lean_ctor_get(v_x_229_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v_x_229_, 1);
lean_dec(v_unused_246_);
v___x_232_ = v_x_229_;
v_isShared_233_ = v_isSharedCheck_245_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_fst_230_);
lean_dec(v_x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_245_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_info_234_; uint8_t v___y_236_; 
v_info_234_ = lean_ctor_get(v_fst_230_, 2);
lean_inc_ref(v_info_234_);
lean_dec(v_fst_230_);
if (lean_obj_tag(v_info_234_) == 1)
{
uint8_t v___x_243_; 
v___x_243_ = 1;
v___y_236_ = v___x_243_;
goto v___jp_235_;
}
else
{
uint8_t v___x_244_; 
v___x_244_ = 0;
v___y_236_ = v___x_244_;
goto v___jp_235_;
}
v___jp_235_:
{
lean_object* v___x_237_; lean_object* v_size_x3f_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_237_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_237_, 0, v_info_234_);
v_size_x3f_238_ = l_Lean_Elab_Info_size_x3f(v___x_237_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = lean_box(v___y_236_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v_size_x3f_238_);
lean_ctor_set(v___x_232_, 0, v___x_239_);
v___x_241_ = v___x_232_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_size_x3f_238_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
return v_x_247_;
}
else
{
lean_object* v_key_249_; lean_object* v_value_250_; lean_object* v_tail_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_key_249_ = lean_ctor_get(v_x_248_, 0);
v_value_250_ = lean_ctor_get(v_x_248_, 1);
v_tail_251_ = lean_ctor_get(v_x_248_, 2);
lean_inc(v_value_250_);
lean_inc(v_key_249_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_key_249_);
lean_ctor_set(v___x_252_, 1, v_value_250_);
v___x_253_ = lean_array_push(v_x_247_, v___x_252_);
v_x_247_ = v___x_253_;
v_x_248_ = v_tail_251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_x_255_, v_x_256_);
lean_dec(v_x_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(lean_object* v_as_258_, size_t v_i_259_, size_t v_stop_260_, lean_object* v_b_261_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = lean_usize_dec_eq(v_i_259_, v_stop_260_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; size_t v___x_265_; size_t v___x_266_; 
v___x_263_ = lean_array_uget_borrowed(v_as_258_, v_i_259_);
v___x_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_b_261_, v___x_263_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_i_259_, v___x_265_);
v_i_259_ = v___x_266_;
v_b_261_ = v___x_264_;
goto _start;
}
else
{
return v_b_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4___boxed(lean_object* v_as_268_, lean_object* v_i_269_, lean_object* v_stop_270_, lean_object* v_b_271_){
_start:
{
size_t v_i_boxed_272_; size_t v_stop_boxed_273_; lean_object* v_res_274_; 
v_i_boxed_272_ = lean_unbox_usize(v_i_269_);
lean_dec(v_i_269_);
v_stop_boxed_273_ = lean_unbox_usize(v_stop_270_);
lean_dec(v_stop_270_);
v_res_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_268_, v_i_boxed_272_, v_stop_boxed_273_, v_b_271_);
lean_dec_ref(v_as_268_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(size_t v_sz_275_, size_t v_i_276_, lean_object* v_bs_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_lt(v_i_276_, v_sz_275_);
if (v___x_278_ == 0)
{
return v_bs_277_;
}
else
{
lean_object* v_v_279_; lean_object* v_snd_280_; lean_object* v___x_281_; lean_object* v_bs_x27_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v_v_279_ = lean_array_uget_borrowed(v_bs_277_, v_i_276_);
v_snd_280_ = lean_ctor_get(v_v_279_, 1);
lean_inc(v_snd_280_);
v___x_281_ = lean_unsigned_to_nat(0u);
v_bs_x27_282_ = lean_array_uset(v_bs_277_, v_i_276_, v___x_281_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_276_, v___x_283_);
v___x_285_ = lean_array_uset(v_bs_x27_282_, v_i_276_, v_snd_280_);
v_i_276_ = v___x_284_;
v_bs_277_ = v___x_285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(lean_object* v_sz_287_, lean_object* v_i_288_, lean_object* v_bs_289_){
_start:
{
size_t v_sz_boxed_290_; size_t v_i_boxed_291_; lean_object* v_res_292_; 
v_sz_boxed_290_ = lean_unbox_usize(v_sz_287_);
lean_dec(v_sz_287_);
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_290_, v_i_boxed_291_, v_bs_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(lean_object* v_hi_293_, lean_object* v_pivot_294_, lean_object* v_as_295_, lean_object* v_i_296_, lean_object* v_k_297_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = lean_nat_dec_lt(v_k_297_, v_hi_293_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_k_297_);
v___x_309_ = lean_array_fswap(v_as_295_, v_i_296_, v_hi_293_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_i_296_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v_fst_312_; lean_object* v_fst_313_; lean_object* v_fst_314_; lean_object* v_snd_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; 
v___x_311_ = lean_array_fget_borrowed(v_as_295_, v_k_297_);
v_fst_312_ = lean_ctor_get(v___x_311_, 0);
v_fst_313_ = lean_ctor_get(v_pivot_294_, 0);
v_fst_314_ = lean_ctor_get(v_fst_312_, 0);
v_snd_315_ = lean_ctor_get(v_fst_312_, 1);
v_fst_316_ = lean_ctor_get(v_fst_313_, 0);
v_snd_317_ = lean_ctor_get(v_fst_313_, 1);
if (lean_obj_tag(v_snd_315_) == 0)
{
if (lean_obj_tag(v_snd_317_) == 1)
{
goto v___jp_298_;
}
else
{
goto v___jp_324_;
}
}
else
{
if (lean_obj_tag(v_snd_317_) == 0)
{
goto v___jp_302_;
}
else
{
goto v___jp_324_;
}
}
v___jp_318_:
{
if (lean_obj_tag(v_snd_315_) == 1)
{
if (lean_obj_tag(v_snd_317_) == 1)
{
lean_object* v_val_319_; lean_object* v_val_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_val_319_ = lean_ctor_get(v_snd_315_, 0);
v_val_320_ = lean_ctor_get(v_snd_317_, 0);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_val_319_, v___x_321_);
v___x_323_ = lean_nat_dec_le(v___x_322_, v_val_320_);
lean_dec(v___x_322_);
if (v___x_323_ == 0)
{
goto v___jp_298_;
}
else
{
goto v___jp_302_;
}
}
else
{
goto v___jp_298_;
}
}
else
{
goto v___jp_298_;
}
}
v___jp_324_:
{
uint8_t v___x_325_; 
v___x_325_ = lean_unbox(v_fst_314_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
v___x_326_ = lean_unbox(v_fst_316_);
if (v___x_326_ == 1)
{
goto v___jp_302_;
}
else
{
goto v___jp_318_;
}
}
else
{
uint8_t v___x_327_; 
v___x_327_ = lean_unbox(v_fst_316_);
if (v___x_327_ == 0)
{
goto v___jp_298_;
}
else
{
goto v___jp_318_;
}
}
}
}
v___jp_298_:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v_k_297_, v___x_299_);
lean_dec(v_k_297_);
v_k_297_ = v___x_300_;
goto _start;
}
v___jp_302_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_array_fswap(v_as_295_, v_i_296_, v_k_297_);
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_i_296_, v___x_304_);
lean_dec(v_i_296_);
v___x_306_ = lean_nat_add(v_k_297_, v___x_304_);
lean_dec(v_k_297_);
v_as_295_ = v___x_303_;
v_i_296_ = v___x_305_;
v_k_297_ = v___x_306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(lean_object* v_hi_328_, lean_object* v_pivot_329_, lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_k_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_328_, v_pivot_329_, v_as_330_, v_i_331_, v_k_332_);
lean_dec_ref(v_pivot_329_);
lean_dec(v_hi_328_);
return v_res_333_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(uint8_t v___x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v_fst_337_; lean_object* v_fst_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v_fst_341_; lean_object* v_snd_342_; 
v_fst_337_ = lean_ctor_get(v_x_335_, 0);
v_fst_338_ = lean_ctor_get(v_x_336_, 0);
v_fst_339_ = lean_ctor_get(v_fst_337_, 0);
v_snd_340_ = lean_ctor_get(v_fst_337_, 1);
v_fst_341_ = lean_ctor_get(v_fst_338_, 0);
v_snd_342_ = lean_ctor_get(v_fst_338_, 1);
if (lean_obj_tag(v_snd_340_) == 0)
{
if (lean_obj_tag(v_snd_342_) == 1)
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
if (lean_obj_tag(v_snd_342_) == 0)
{
return v___x_334_;
}
else
{
goto v___jp_351_;
}
}
v___jp_343_:
{
if (lean_obj_tag(v_snd_340_) == 1)
{
if (lean_obj_tag(v_snd_342_) == 1)
{
lean_object* v_val_344_; lean_object* v_val_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_val_344_ = lean_ctor_get(v_snd_340_, 0);
v_val_345_ = lean_ctor_get(v_snd_342_, 0);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_val_344_, v___x_346_);
v___x_348_ = lean_nat_dec_le(v___x_347_, v_val_345_);
lean_dec(v___x_347_);
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
v___x_352_ = lean_unbox(v_fst_339_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
v___x_353_ = lean_unbox(v_fst_341_);
if (v___x_353_ == 1)
{
uint8_t v___x_354_; 
v___x_354_ = lean_unbox(v_fst_341_);
return v___x_354_;
}
else
{
goto v___jp_343_;
}
}
else
{
uint8_t v___x_355_; 
v___x_355_ = lean_unbox(v_fst_341_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
v___x_356_ = lean_unbox(v_fst_341_);
return v___x_356_;
}
else
{
goto v___jp_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0___boxed(lean_object* v___x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
uint8_t v___x_2381__boxed_361_; uint8_t v_res_362_; lean_object* v_r_363_; 
v___x_2381__boxed_361_ = lean_unbox(v___x_358_);
v_res_362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_2381__boxed_361_, v_x_359_, v_x_360_);
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
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_nbuckets_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_460_ = lean_array_get_size(v_data_459_);
v___x_461_ = lean_unsigned_to_nat(2u);
v_nbuckets_462_ = lean_nat_mul(v___x_460_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_box(0);
v___x_465_ = lean_mk_array(v_nbuckets_462_, v___x_464_);
v___x_466_ = lean_array_propagate_mark(v_data_459_, v___x_465_);
v___x_467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v___x_463_, v_data_459_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
if (lean_obj_tag(v_x_469_) == 0)
{
uint8_t v___x_470_; 
v___x_470_ = 1;
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = 0;
return v___x_471_;
}
}
else
{
if (lean_obj_tag(v_x_469_) == 0)
{
uint8_t v___x_472_; 
v___x_472_ = 0;
return v___x_472_;
}
else
{
lean_object* v_val_473_; lean_object* v_val_474_; uint8_t v_decide_475_; 
v_val_473_ = lean_ctor_get(v_x_468_, 0);
v_val_474_ = lean_ctor_get(v_x_469_, 0);
v_decide_475_ = lean_nat_dec_eq(v_val_473_, v_val_474_);
return v_decide_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_476_, v_x_477_);
lean_dec(v_x_477_);
lean_dec(v_x_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(lean_object* v_a_480_, lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
else
{
lean_object* v_key_483_; lean_object* v_tail_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v_fst_487_; lean_object* v_snd_488_; uint8_t v___x_492_; 
v_key_483_ = lean_ctor_get(v_x_481_, 0);
v_tail_484_ = lean_ctor_get(v_x_481_, 2);
v_fst_485_ = lean_ctor_get(v_key_483_, 0);
v_snd_486_ = lean_ctor_get(v_key_483_, 1);
v_fst_487_ = lean_ctor_get(v_a_480_, 0);
v_snd_488_ = lean_ctor_get(v_a_480_, 1);
v___x_492_ = lean_unbox(v_fst_487_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = lean_unbox(v_fst_485_);
if (v___x_493_ == 0)
{
goto v___jp_489_;
}
else
{
v_x_481_ = v_tail_484_;
goto _start;
}
}
else
{
uint8_t v___x_495_; 
v___x_495_ = lean_unbox(v_fst_485_);
if (v___x_495_ == 0)
{
v_x_481_ = v_tail_484_;
goto _start;
}
else
{
goto v___jp_489_;
}
}
v___jp_489_:
{
uint8_t v___x_490_; 
v___x_490_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_486_, v_snd_488_);
if (v___x_490_ == 0)
{
v_x_481_ = v_tail_484_;
goto _start;
}
else
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_497_, lean_object* v_x_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_497_, v_x_498_);
lean_dec(v_x_498_);
lean_dec_ref(v_a_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
lean_object* v___y_506_; 
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___y_506_ = v___x_509_;
goto v___jp_505_;
}
else
{
lean_object* v_val_510_; 
v_val_510_ = lean_ctor_get(v_x_504_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v_x_504_, 1);
v___y_506_ = v_val_510_;
goto v___jp_505_;
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_array_push(v___y_506_, v_a_503_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_val_516_; lean_object* v___x_517_; 
v___x_514_ = lean_box(0);
v___x_515_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_511_, v___x_514_);
v_val_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_516_);
lean_dec(v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_517_, 0, v_a_512_);
lean_ctor_set(v___x_517_, 1, v_val_516_);
lean_ctor_set(v___x_517_, 2, v_x_513_);
return v___x_517_;
}
else
{
lean_object* v_key_518_; lean_object* v_value_519_; lean_object* v_tail_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_542_; 
v_key_518_ = lean_ctor_get(v_x_513_, 0);
v_value_519_ = lean_ctor_get(v_x_513_, 1);
v_tail_520_ = lean_ctor_get(v_x_513_, 2);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_542_ == 0)
{
v___x_522_ = v_x_513_;
v_isShared_523_ = v_isSharedCheck_542_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_tail_520_);
lean_inc(v_value_519_);
lean_inc(v_key_518_);
lean_dec(v_x_513_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_542_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v_fst_531_; lean_object* v_snd_532_; uint8_t v___x_539_; 
v_fst_529_ = lean_ctor_get(v_key_518_, 0);
v_snd_530_ = lean_ctor_get(v_key_518_, 1);
v_fst_531_ = lean_ctor_get(v_a_512_, 0);
v_snd_532_ = lean_ctor_get(v_a_512_, 1);
v___x_539_ = lean_unbox(v_fst_531_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_fst_529_);
if (v___x_540_ == 0)
{
goto v___jp_533_;
}
else
{
goto v___jp_524_;
}
}
else
{
uint8_t v___x_541_; 
v___x_541_ = lean_unbox(v_fst_529_);
if (v___x_541_ == 0)
{
goto v___jp_524_;
}
else
{
goto v___jp_533_;
}
}
v___jp_524_:
{
lean_object* v_tail_525_; lean_object* v___x_527_; 
v_tail_525_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_511_, v_a_512_, v_tail_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 2, v_tail_525_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_key_518_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_value_519_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_tail_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
v___jp_533_:
{
uint8_t v___x_534_; 
v___x_534_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_530_, v_snd_532_);
if (v___x_534_ == 0)
{
goto v___jp_524_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_val_537_; lean_object* v___x_538_; 
lean_del_object(v___x_522_);
lean_dec(v_key_518_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_value_519_);
v___x_536_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_511_, v___x_535_);
v_val_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_537_);
lean_dec(v___x_536_);
v___x_538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_538_, 0, v_a_512_);
lean_ctor_set(v___x_538_, 1, v_val_537_);
lean_ctor_set(v___x_538_, 2, v_tail_520_);
return v___x_538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(lean_object* v_a_543_, lean_object* v_m_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___y_547_; lean_object* v___y_548_; size_t v___y_549_; lean_object* v___y_550_; lean_object* v_size_553_; lean_object* v_buckets_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_613_; 
v_size_553_ = lean_ctor_get(v_m_544_, 0);
v_buckets_554_ = lean_ctor_get(v_m_544_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_m_544_);
if (v_isSharedCheck_613_ == 0)
{
v___x_556_ = v_m_544_;
v_isShared_557_ = v_isSharedCheck_613_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_buckets_554_);
lean_inc(v_size_553_);
lean_dec(v_m_544_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_613_;
goto v_resetjp_555_;
}
v___jp_546_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_array_uset(v___y_547_, v___y_549_, v___y_548_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___y_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
return v___x_552_;
}
v_resetjp_555_:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_560_; uint64_t v___y_562_; uint64_t v___y_563_; uint64_t v___y_604_; uint8_t v___x_610_; 
v_fst_558_ = lean_ctor_get(v_a_545_, 0);
v_snd_559_ = lean_ctor_get(v_a_545_, 1);
v___x_560_ = lean_array_get_size(v_buckets_554_);
v___x_610_ = lean_unbox(v_fst_558_);
if (v___x_610_ == 0)
{
uint64_t v___x_611_; 
v___x_611_ = 13ULL;
v___y_604_ = v___x_611_;
goto v___jp_603_;
}
else
{
uint64_t v___x_612_; 
v___x_612_ = 11ULL;
v___y_604_ = v___x_612_;
goto v___jp_603_;
}
v___jp_561_:
{
uint64_t v___x_564_; uint64_t v___x_565_; uint64_t v___x_566_; uint64_t v_fold_567_; uint64_t v___x_568_; uint64_t v___x_569_; uint64_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v_bkt_576_; uint8_t v___x_577_; 
v___x_564_ = lean_uint64_mix_hash(v___y_562_, v___y_563_);
v___x_565_ = 32ULL;
v___x_566_ = lean_uint64_shift_right(v___x_564_, v___x_565_);
v_fold_567_ = lean_uint64_xor(v___x_564_, v___x_566_);
v___x_568_ = 16ULL;
v___x_569_ = lean_uint64_shift_right(v_fold_567_, v___x_568_);
v___x_570_ = lean_uint64_xor(v_fold_567_, v___x_569_);
v___x_571_ = lean_uint64_to_usize(v___x_570_);
v___x_572_ = lean_usize_of_nat(v___x_560_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_sub(v___x_572_, v___x_573_);
v___x_575_ = lean_usize_land(v___x_571_, v___x_574_);
v_bkt_576_ = lean_array_uget_borrowed(v_buckets_554_, v___x_575_);
v___x_577_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_545_, v_bkt_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_size_x27_581_; lean_object* v___x_582_; lean_object* v_buckets_x27_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_578_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0));
v___x_579_ = lean_array_push(v___x_578_, v_a_543_);
v___x_580_ = lean_unsigned_to_nat(1u);
v_size_x27_581_ = lean_nat_add(v_size_553_, v___x_580_);
lean_dec(v_size_553_);
lean_inc(v_bkt_576_);
v___x_582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_582_, 0, v_a_545_);
lean_ctor_set(v___x_582_, 1, v___x_579_);
lean_ctor_set(v___x_582_, 2, v_bkt_576_);
v_buckets_x27_583_ = lean_array_uset(v_buckets_554_, v___x_575_, v___x_582_);
v___x_584_ = lean_unsigned_to_nat(4u);
v___x_585_ = lean_nat_mul(v_size_x27_581_, v___x_584_);
v___x_586_ = lean_unsigned_to_nat(3u);
v___x_587_ = lean_nat_div(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_array_get_size(v_buckets_x27_583_);
v___x_589_ = lean_nat_dec_le(v___x_587_, v___x_588_);
lean_dec(v___x_587_);
if (v___x_589_ == 0)
{
lean_object* v_val_590_; lean_object* v___x_592_; 
v_val_590_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_buckets_x27_583_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_val_590_);
lean_ctor_set(v___x_556_, 0, v_size_x27_581_);
v___x_592_ = v___x_556_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_size_x27_581_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_val_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_object* v___x_595_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_buckets_x27_583_);
lean_ctor_set(v___x_556_, 0, v_size_x27_581_);
v___x_595_ = v___x_556_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_size_x27_581_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_buckets_x27_583_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v___x_597_; lean_object* v_buckets_x27_598_; lean_object* v_bkt_x27_599_; uint8_t v___x_600_; 
lean_inc(v_bkt_576_);
lean_del_object(v___x_556_);
v___x_597_ = lean_box(0);
v_buckets_x27_598_ = lean_array_uset(v_buckets_554_, v___x_575_, v___x_597_);
lean_inc_ref(v_a_545_);
v_bkt_x27_599_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_543_, v_a_545_, v_bkt_576_);
v___x_600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_545_, v_bkt_x27_599_);
lean_dec_ref(v_a_545_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_sub(v_size_553_, v___x_601_);
lean_dec(v_size_553_);
v___y_547_ = v_buckets_x27_598_;
v___y_548_ = v_bkt_x27_599_;
v___y_549_ = v___x_575_;
v___y_550_ = v___x_602_;
goto v___jp_546_;
}
else
{
v___y_547_ = v_buckets_x27_598_;
v___y_548_ = v_bkt_x27_599_;
v___y_549_ = v___x_575_;
v___y_550_ = v_size_553_;
goto v___jp_546_;
}
}
}
v___jp_603_:
{
if (lean_obj_tag(v_snd_559_) == 0)
{
uint64_t v___x_605_; 
v___x_605_ = 11ULL;
v___y_562_ = v___y_604_;
v___y_563_ = v___x_605_;
goto v___jp_561_;
}
else
{
lean_object* v_val_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v___x_609_; 
v_val_606_ = lean_ctor_get(v_snd_559_, 0);
v___x_607_ = l_String_instHashableRaw_hash(v_val_606_);
v___x_608_ = 13ULL;
v___x_609_ = lean_uint64_mix_hash(v___x_607_, v___x_608_);
v___y_562_ = v___y_604_;
v___y_563_ = v___x_609_;
goto v___jp_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(lean_object* v_key_614_, lean_object* v_as_615_, size_t v_sz_616_, size_t v_i_617_, lean_object* v_b_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_lt(v_i_617_, v_sz_616_);
if (v___x_619_ == 0)
{
lean_dec_ref(v_key_614_);
return v_b_618_;
}
else
{
lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; 
v_a_620_ = lean_array_uget_borrowed(v_as_615_, v_i_617_);
lean_inc_ref(v_key_614_);
lean_inc_n(v_a_620_, 2);
v___x_621_ = lean_apply_1(v_key_614_, v_a_620_);
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_620_, v_b_618_, v___x_621_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_617_, v___x_623_);
v_i_617_ = v___x_624_;
v_b_618_ = v___x_622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg___boxed(lean_object* v_key_626_, lean_object* v_as_627_, lean_object* v_sz_628_, lean_object* v_i_629_, lean_object* v_b_630_){
_start:
{
size_t v_sz_boxed_631_; size_t v_i_boxed_632_; lean_object* v_res_633_; 
v_sz_boxed_631_ = lean_unbox_usize(v_sz_628_);
lean_dec(v_sz_628_);
v_i_boxed_632_ = lean_unbox_usize(v_i_629_);
lean_dec(v_i_629_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_626_, v_as_627_, v_sz_boxed_631_, v_i_boxed_632_, v_b_630_);
lean_dec_ref(v_as_627_);
return v_res_633_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_box(0);
v___x_635_ = lean_unsigned_to_nat(16u);
v___x_636_ = lean_mk_array(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_groups_639_; 
v___x_637_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0);
v___x_638_ = lean_unsigned_to_nat(0u);
v_groups_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_639_, 0, v___x_638_);
lean_ctor_set(v_groups_639_, 1, v___x_637_);
return v_groups_639_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(lean_object* v_key_640_, lean_object* v_xs_641_){
_start:
{
lean_object* v_groups_642_; size_t v_sz_643_; size_t v___x_644_; lean_object* v___x_645_; 
v_groups_642_ = lean_obj_once(&l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1, &l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once, _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1);
v_sz_643_ = lean_array_size(v_xs_641_);
v___x_644_ = ((size_t)0ULL);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_640_, v_xs_641_, v_sz_643_, v___x_644_, v_groups_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(lean_object* v_key_646_, lean_object* v_xs_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_646_, v_xs_647_);
lean_dec_ref(v_xs_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(lean_object* v_items_650_){
_start:
{
lean_object* v___y_652_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_669_; lean_object* v___f_676_; lean_object* v_partitions_677_; lean_object* v_size_678_; lean_object* v_buckets_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___f_676_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0));
v_partitions_677_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v___f_676_, v_items_650_);
v_size_678_ = lean_ctor_get(v_partitions_677_, 0);
lean_inc(v_size_678_);
v_buckets_679_ = lean_ctor_get(v_partitions_677_, 1);
lean_inc_ref(v_buckets_679_);
lean_dec_ref(v_partitions_677_);
v___x_680_ = lean_mk_empty_array_with_capacity(v_size_678_);
lean_dec(v_size_678_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_array_get_size(v_buckets_679_);
v___x_683_ = lean_nat_dec_lt(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec_ref(v_buckets_679_);
v___y_669_ = v___x_680_;
goto v___jp_668_;
}
else
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_682_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_679_, v___x_684_, v___x_685_, v___x_680_);
lean_dec_ref(v_buckets_679_);
v___y_669_ = v___x_686_;
goto v___jp_668_;
}
v___jp_651_:
{
size_t v_sz_653_; size_t v___x_654_; lean_object* v___x_655_; 
v_sz_653_ = lean_array_size(v___y_652_);
v___x_654_ = ((size_t)0ULL);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_653_, v___x_654_, v___y_652_);
return v___x_655_;
}
v___jp_656_:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v___y_658_, v___y_657_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec(v___y_658_);
v___y_652_ = v___x_661_;
goto v___jp_651_;
}
v___jp_662_:
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_le(v___y_666_, v___y_663_);
if (v___x_667_ == 0)
{
lean_dec(v___y_663_);
lean_inc(v___y_666_);
v___y_657_ = v___y_664_;
v___y_658_ = v___y_665_;
v___y_659_ = v___y_666_;
v___y_660_ = v___y_666_;
goto v___jp_656_;
}
else
{
v___y_657_ = v___y_664_;
v___y_658_ = v___y_665_;
v___y_659_ = v___y_666_;
v___y_660_ = v___y_663_;
goto v___jp_656_;
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = lean_array_get_size(v___y_669_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_nat_dec_eq(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_sub(v___x_670_, v___x_673_);
v___x_675_ = lean_nat_dec_le(v___x_671_, v___x_674_);
if (v___x_675_ == 0)
{
lean_inc(v___x_674_);
v___y_663_ = v___x_674_;
v___y_664_ = v___y_669_;
v___y_665_ = v___x_670_;
v___y_666_ = v___x_674_;
goto v___jp_662_;
}
else
{
v___y_663_ = v___x_674_;
v___y_664_ = v___y_669_;
v___y_665_ = v___x_670_;
v___y_666_ = v___x_671_;
goto v___jp_662_;
}
}
else
{
v___y_652_ = v___y_669_;
goto v___jp_651_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(lean_object* v_items_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_687_);
lean_dec_ref(v_items_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(lean_object* v_n_689_, lean_object* v_as_690_, lean_object* v_lo_691_, lean_object* v_hi_692_, lean_object* v_w_693_, lean_object* v_hlo_694_, lean_object* v_hhi_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_689_, v_as_690_, v_lo_691_, v_hi_692_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(lean_object* v_n_697_, lean_object* v_as_698_, lean_object* v_lo_699_, lean_object* v_hi_700_, lean_object* v_w_701_, lean_object* v_hlo_702_, lean_object* v_hhi_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_n_697_, v_as_698_, v_lo_699_, v_hi_700_, v_w_701_, v_hlo_702_, v_hhi_703_);
lean_dec(v_hi_700_);
lean_dec(v_n_697_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(lean_object* v_00_u03b2_705_, lean_object* v_key_706_, lean_object* v_xs_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_706_, v_xs_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(lean_object* v_00_u03b2_709_, lean_object* v_key_710_, lean_object* v_xs_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_00_u03b2_709_, v_key_710_, v_xs_711_);
lean_dec_ref(v_xs_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(lean_object* v_n_713_, lean_object* v_lo_714_, lean_object* v_hi_715_, lean_object* v_hhi_716_, lean_object* v_pivot_717_, lean_object* v_as_718_, lean_object* v_i_719_, lean_object* v_k_720_, lean_object* v_ilo_721_, lean_object* v_ik_722_, lean_object* v_w_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_715_, v_pivot_717_, v_as_718_, v_i_719_, v_k_720_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(lean_object* v_n_725_, lean_object* v_lo_726_, lean_object* v_hi_727_, lean_object* v_hhi_728_, lean_object* v_pivot_729_, lean_object* v_as_730_, lean_object* v_i_731_, lean_object* v_k_732_, lean_object* v_ilo_733_, lean_object* v_ik_734_, lean_object* v_w_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_n_725_, v_lo_726_, v_hi_727_, v_hhi_728_, v_pivot_729_, v_as_730_, v_i_731_, v_k_732_, v_ilo_733_, v_ik_734_, v_w_735_);
lean_dec_ref(v_pivot_729_);
lean_dec(v_hi_727_);
lean_dec(v_lo_726_);
lean_dec(v_n_725_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(lean_object* v_00_u03b2_737_, lean_object* v_a_738_, lean_object* v_m_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_738_, v_m_739_, v_a_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(lean_object* v_00_u03b2_742_, lean_object* v_key_743_, lean_object* v_as_744_, size_t v_sz_745_, size_t v_i_746_, lean_object* v_b_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_743_, v_as_744_, v_sz_745_, v_i_746_, v_b_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(lean_object* v_00_u03b2_749_, lean_object* v_key_750_, lean_object* v_as_751_, lean_object* v_sz_752_, lean_object* v_i_753_, lean_object* v_b_754_){
_start:
{
size_t v_sz_boxed_755_; size_t v_i_boxed_756_; lean_object* v_res_757_; 
v_sz_boxed_755_ = lean_unbox_usize(v_sz_752_);
lean_dec(v_sz_752_);
v_i_boxed_756_ = lean_unbox_usize(v_i_753_);
lean_dec(v_i_753_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(v_00_u03b2_749_, v_key_750_, v_as_751_, v_sz_boxed_755_, v_i_boxed_756_, v_b_754_);
lean_dec_ref(v_as_751_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_758_, lean_object* v_a_759_, lean_object* v_x_760_){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_759_, v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_762_, lean_object* v_a_763_, lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(v_00_u03b2_762_, v_a_763_, v_x_764_);
lean_dec(v_x_764_);
lean_dec_ref(v_a_763_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_767_, lean_object* v_data_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_data_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_771_, v_a_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_775_, lean_object* v_i_776_, lean_object* v_source_777_, lean_object* v_target_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v_i_776_, v_source_777_, v_target_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_x_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object* v_fileMap_784_, lean_object* v_hoverPos_785_, lean_object* v_cmdStx_786_, lean_object* v_infoTree_787_){
_start:
{
lean_object* v___x_788_; lean_object* v_fst_789_; lean_object* v_snd_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_800_; 
v___x_788_ = l_Lean_Server_Completion_findCompletionInfosAt(v_fileMap_784_, v_hoverPos_785_, v_cmdStx_786_, v_infoTree_787_);
v_fst_789_ = lean_ctor_get(v___x_788_, 0);
v_snd_790_ = lean_ctor_get(v___x_788_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_800_ == 0)
{
v___x_792_ = v___x_788_;
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snd_790_);
lean_inc(v_fst_789_);
lean_dec(v___x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_partitions_796_; lean_object* v___x_798_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Array_zipIdx___redArg(v_fst_789_, v___x_794_);
v_partitions_796_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_795_);
lean_dec_ref(v___x_795_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_partitions_796_);
v___x_798_ = v___x_792_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_partitions_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_790_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
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
