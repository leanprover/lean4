// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Diagnostics
// Imports: public import Lean.Meta.Diagnostics public import Lean.Meta.Tactic.Simp.Types
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedOrigin_default;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_Origin_lt___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics_threshold;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_crossEmoji;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDiagSummary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_appendSection(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Meta_DiagSummary_isEmpty(lean_object*);
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (builtin simproc)"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 61, 75, 186, 44, 210, 52, 194)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", succeeded: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Origin_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0_value;
static const lean_closure_object l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2;
static const lean_ctor_object l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", key: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_mkDiagMessages___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_mkDiagMessages___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_mkDiagMessages___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_mkDiagMessages___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "used theorems"};
static const lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_mkDiagMessages___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tried theorems"};
static const lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_mkDiagMessages___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "tried congruence theorems"};
static const lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_mkDiagMessages___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "theorems with bad keys"};
static const lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_mkDiagMessages___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "use `set_option diagnostics.threshold <num>` to control threshold for reporting counters"};
static const lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_mkDiagMessages___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__5_value)}};
static const lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_mkDiagMessages___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkDiagMessages___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkDiagMessages___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_reportDiag___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Diagnostics"};
static const lean_object* l_Lean_Meta_Simp_reportDiag___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_reportDiag___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_reportDiag___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_reportDiag___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Simp_reportDiag___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_reportDiag___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_reportDiag___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_reportDiag___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__0));
v___x_3_ = l_Lean_stringToMessageData(v___x_2_);
return v___x_3_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(lean_object* v_thmId_4_, lean_object* v_a_5_){
_start:
{
switch(lean_obj_tag(v_thmId_4_))
{
case 0:
{
lean_object* v_declName_7_; lean_object* v___x_8_; lean_object* v_env_9_; uint8_t v___x_10_; uint8_t v___x_11_; 
v_declName_7_ = lean_ctor_get(v_thmId_4_, 0);
lean_inc_n(v_declName_7_, 2);
lean_dec_ref_known(v_thmId_4_, 1);
v___x_8_ = lean_st_ref_get(v_a_5_);
v_env_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_env_9_);
lean_dec(v___x_8_);
v___x_10_ = 1;
v___x_11_ = l_Lean_Environment_contains(v_env_9_, v_declName_7_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = l_Lean_MessageData_ofName(v_declName_7_);
v___x_13_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1, &l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___closed__1);
v___x_14_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
else
{
uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = 0;
v___x_17_ = l_Lean_MessageData_ofConstName(v_declName_7_, v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
case 1:
{
lean_object* v_fvarId_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_28_; 
v_fvarId_19_ = lean_ctor_get(v_thmId_4_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v_thmId_4_);
if (v_isSharedCheck_28_ == 0)
{
v___x_21_ = v_thmId_4_;
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_fvarId_19_);
lean_dec(v_thmId_4_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_23_ = l_Lean_mkFVar(v_fvarId_19_);
v___x_24_ = l_Lean_MessageData_ofExpr(v___x_23_);
if (v_isShared_22_ == 0)
{
lean_ctor_set_tag(v___x_21_, 0);
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_26_ = v___x_21_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
default: 
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = l_Lean_Meta_Origin_key(v_thmId_4_);
lean_dec_ref(v_thmId_4_);
v___x_30_ = l_Lean_MessageData_ofName(v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmId_4_ = stack[0].m_obj;
lean_object* v_a_5_ = stack[1].m_obj;
lean_object* v_res_32_;
v_res_32_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_thmId_4_, v_a_5_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___boxed(lean_object* v_thmId_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_thmId_33_, v_a_34_);
lean_dec(v_a_34_);
return v_res_36_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(lean_object* v_thmId_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_thmId_37_, v_a_41_);
return v___x_43_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmId_37_ = stack[0].m_obj;
lean_object* v_a_38_ = stack[1].m_obj;
lean_object* v_a_39_ = stack[2].m_obj;
lean_object* v_a_40_ = stack[3].m_obj;
lean_object* v_a_41_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(v_thmId_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___boxed(lean_object* v_thmId_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(v_thmId_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(lean_object* v_opts_52_, lean_object* v_opt_53_){
_start:
{
lean_object* v_name_54_; lean_object* v_defValue_55_; lean_object* v_map_56_; lean_object* v___x_57_; 
v_name_54_ = lean_ctor_get(v_opt_53_, 0);
v_defValue_55_ = lean_ctor_get(v_opt_53_, 1);
v_map_56_ = lean_ctor_get(v_opts_52_, 0);
v___x_57_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_56_, v_name_54_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_inc(v_defValue_55_);
return v_defValue_55_;
}
else
{
lean_object* v_val_58_; 
v_val_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_val_58_);
lean_dec_ref_known(v___x_57_, 1);
if (lean_obj_tag(v_val_58_) == 3)
{
lean_object* v_v_59_; 
v_v_59_ = lean_ctor_get(v_val_58_, 0);
lean_inc(v_v_59_);
lean_dec_ref_known(v_val_58_, 1);
return v_v_59_;
}
else
{
lean_dec(v_val_58_);
lean_inc(v_defValue_55_);
return v_defValue_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0___boxed(lean_object* v_opts_60_, lean_object* v_opt_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(v_opts_60_, v_opt_61_);
lean_dec_ref(v_opt_61_);
lean_dec_ref(v_opts_60_);
return v_res_62_;
}
}
uint8_t l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(lean_object* v_x_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = 1;
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_63_ = stack[0].m_obj;
uint8_t v_res_65_;
v_res_65_ = l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(v_x_63_);
stack->m_num = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0___boxed(lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(v_x_66_);
lean_dec_ref(v_x_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0(lean_object* v_f_69_, lean_object* v_s_70_, lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_a_71_);
lean_ctor_set(v___x_73_, 1, v_b_72_);
v___x_74_ = lean_apply_2(v_f_69_, v___x_73_, v_s_70_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_a_83_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_74_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_74_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_f_91_, lean_object* v_keys_92_, lean_object* v_vals_93_, lean_object* v_i_94_, lean_object* v_acc_95_){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = lean_array_get_size(v_keys_92_);
v___x_97_ = lean_nat_dec_lt(v_i_94_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec(v_i_94_);
lean_dec_ref(v_f_91_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_acc_95_);
return v___x_98_;
}
else
{
lean_object* v_k_99_; lean_object* v_v_100_; lean_object* v___x_101_; 
v_k_99_ = lean_array_fget_borrowed(v_keys_92_, v_i_94_);
v_v_100_ = lean_array_fget_borrowed(v_vals_93_, v_i_94_);
lean_inc_ref(v_f_91_);
lean_inc(v_v_100_);
lean_inc(v_k_99_);
v___x_101_ = lean_apply_3(v_f_91_, v_acc_95_, v_k_99_, v_v_100_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_dec(v_i_94_);
lean_dec_ref(v_f_91_);
return v___x_101_;
}
else
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_94_, v___x_103_);
lean_dec(v_i_94_);
v_i_94_ = v___x_104_;
v_acc_95_ = v_a_102_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_f_106_, lean_object* v_keys_107_, lean_object* v_vals_108_, lean_object* v_i_109_, lean_object* v_acc_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_106_, v_keys_107_, v_vals_108_, v_i_109_, v_acc_110_);
lean_dec_ref(v_vals_108_);
lean_dec_ref(v_keys_107_);
return v_res_111_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_112_, lean_object* v_as_113_, size_t v_i_114_, size_t v_stop_115_, lean_object* v_b_116_){
_start:
{
lean_object* v_a_118_; lean_object* v___y_123_; uint8_t v___x_125_; 
v___x_125_ = lean_usize_dec_eq(v_i_114_, v_stop_115_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_array_uget_borrowed(v_as_113_, v_i_114_);
switch(lean_obj_tag(v___x_126_))
{
case 0:
{
lean_object* v_key_127_; lean_object* v_val_128_; lean_object* v___x_129_; 
v_key_127_ = lean_ctor_get(v___x_126_, 0);
v_val_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc_ref(v_f_112_);
lean_inc(v_val_128_);
lean_inc(v_key_127_);
v___x_129_ = lean_apply_3(v_f_112_, v_b_116_, v_key_127_, v_val_128_);
v___y_123_ = v___x_129_;
goto v___jp_122_;
}
case 1:
{
lean_object* v_node_130_; lean_object* v___x_131_; 
v_node_130_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_node_130_);
lean_inc_ref(v_f_112_);
v___x_131_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_112_, v_node_130_, v_b_116_);
v___y_123_ = v___x_131_;
goto v___jp_122_;
}
default: 
{
v_a_118_ = v_b_116_;
goto v___jp_117_;
}
}
}
else
{
lean_object* v___x_132_; 
lean_dec_ref(v_f_112_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v_b_116_);
return v___x_132_;
}
v___jp_117_:
{
size_t v___x_119_; size_t v___x_120_; 
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_add(v_i_114_, v___x_119_);
v_i_114_ = v___x_120_;
v_b_116_ = v_a_118_;
goto _start;
}
v___jp_122_:
{
if (lean_obj_tag(v___y_123_) == 0)
{
lean_dec_ref(v_f_112_);
return v___y_123_;
}
else
{
lean_object* v_a_124_; 
v_a_124_ = lean_ctor_get(v___y_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v___y_123_, 1);
v_a_118_ = v_a_124_;
goto v___jp_117_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_112_ = stack[0].m_obj;
lean_object* v_as_113_ = stack[1].m_obj;
size_t v_i_114_ = stack[2].m_num;
size_t v_stop_115_ = stack[3].m_num;
lean_object* v_b_116_ = stack[4].m_obj;
lean_object* v_res_133_;
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_112_, v_as_113_, v_i_114_, v_stop_115_, v_b_116_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_f_134_, lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v_es_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_150_; 
v_es_137_ = lean_ctor_get(v_x_135_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_150_ == 0)
{
v___x_139_ = v_x_135_;
v_isShared_140_ = v_isSharedCheck_150_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_es_137_);
lean_dec(v_x_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_150_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_array_get_size(v_es_137_);
v___x_143_ = lean_nat_dec_lt(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_145_; 
lean_dec_ref(v_es_137_);
lean_dec_ref(v_f_134_);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 1);
lean_ctor_set(v___x_139_, 0, v_x_136_);
v___x_145_ = v___x_139_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_x_136_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
lean_del_object(v___x_139_);
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_142_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_134_, v_es_137_, v___x_147_, v___x_148_, v_x_136_);
lean_dec_ref(v_es_137_);
return v___x_149_;
}
}
}
else
{
lean_object* v_ks_151_; lean_object* v_vs_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_ks_151_ = lean_ctor_get(v_x_135_, 0);
lean_inc_ref(v_ks_151_);
v_vs_152_ = lean_ctor_get(v_x_135_, 1);
lean_inc_ref(v_vs_152_);
lean_dec_ref_known(v_x_135_, 2);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_134_, v_ks_151_, v_vs_152_, v___x_153_, v_x_136_);
lean_dec_ref(v_vs_152_);
lean_dec_ref(v_ks_151_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_155_, lean_object* v_as_156_, lean_object* v_i_157_, lean_object* v_stop_158_, lean_object* v_b_159_){
_start:
{
size_t v_i_boxed_160_; size_t v_stop_boxed_161_; lean_object* v_res_162_; 
v_i_boxed_160_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_stop_boxed_161_ = lean_unbox_usize(v_stop_158_);
lean_dec(v_stop_158_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_155_, v_as_156_, v_i_boxed_160_, v_stop_boxed_161_, v_b_159_);
lean_dec_ref(v_as_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(lean_object* v_map_163_, lean_object* v_init_164_, lean_object* v_f_165_){
_start:
{
lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v_a_168_; 
v___f_166_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_166_, 0, v_f_165_);
lean_inc_ref(v_map_163_);
v___x_167_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v___f_166_, v_map_163_, v_init_164_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref(v___x_167_);
return v_a_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___boxed(lean_object* v_map_169_, lean_object* v_init_170_, lean_object* v_f_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_169_, v_init_170_, v_f_171_);
lean_dec_ref(v_map_169_);
return v_res_172_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(lean_object* v_lt_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v_fst_178_; lean_object* v_snd_179_; uint8_t v___x_180_; 
v_fst_176_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v_x_174_);
v_fst_178_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_fst_178_);
v_snd_179_ = lean_ctor_get(v_x_175_, 1);
lean_inc(v_snd_179_);
lean_dec_ref(v_x_175_);
v___x_180_ = lean_nat_dec_eq(v_snd_177_, v_snd_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; 
lean_dec(v_fst_178_);
lean_dec(v_fst_176_);
lean_dec_ref(v_lt_173_);
v___x_181_ = lean_nat_dec_lt(v_snd_179_, v_snd_177_);
lean_dec(v_snd_177_);
lean_dec(v_snd_179_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
lean_dec(v_snd_179_);
lean_dec(v_snd_177_);
v___x_182_ = lean_apply_2(v_lt_173_, v_fst_176_, v_fst_178_);
v___x_183_ = lean_unbox(v___x_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lt_173_ = stack[0].m_obj;
lean_object* v_x_174_ = stack[1].m_obj;
lean_object* v_x_175_ = stack[2].m_obj;
uint8_t v_res_184_;
v_res_184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_173_, v_x_174_, v_x_175_);
stack->m_num = v_res_184_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_lt_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_185_, v_x_186_, v_x_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(lean_object* v_lt_190_, lean_object* v_hi_191_, lean_object* v_pivot_192_, lean_object* v_as_193_, lean_object* v_i_194_, lean_object* v_k_195_){
_start:
{
uint8_t v___y_197_; uint8_t v___x_206_; 
v___x_206_ = lean_nat_dec_lt(v_k_195_, v_hi_191_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_k_195_);
lean_dec_ref(v_pivot_192_);
lean_dec_ref(v_lt_190_);
v___x_207_ = lean_array_fswap(v_as_193_, v_i_194_, v_hi_191_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_i_194_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v_fst_212_; lean_object* v_snd_213_; uint8_t v___x_214_; 
v___x_209_ = lean_array_fget_borrowed(v_as_193_, v_k_195_);
v_fst_210_ = lean_ctor_get(v___x_209_, 0);
v_snd_211_ = lean_ctor_get(v___x_209_, 1);
v_fst_212_ = lean_ctor_get(v_pivot_192_, 0);
v_snd_213_ = lean_ctor_get(v_pivot_192_, 1);
v___x_214_ = lean_nat_dec_eq(v_snd_211_, v_snd_213_);
if (v___x_214_ == 0)
{
uint8_t v___x_215_; 
v___x_215_ = lean_nat_dec_lt(v_snd_213_, v_snd_211_);
v___y_197_ = v___x_215_;
goto v___jp_196_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
lean_inc_ref(v_lt_190_);
lean_inc(v_fst_212_);
lean_inc(v_fst_210_);
v___x_216_ = lean_apply_2(v_lt_190_, v_fst_210_, v_fst_212_);
v___x_217_ = lean_unbox(v___x_216_);
v___y_197_ = v___x_217_;
goto v___jp_196_;
}
}
v___jp_196_:
{
if (v___y_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v_k_195_, v___x_198_);
lean_dec(v_k_195_);
v_k_195_ = v___x_199_;
goto _start;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_201_ = lean_array_fswap(v_as_193_, v_i_194_, v_k_195_);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_i_194_, v___x_202_);
lean_dec(v_i_194_);
v___x_204_ = lean_nat_add(v_k_195_, v___x_202_);
lean_dec(v_k_195_);
v_as_193_ = v___x_201_;
v_i_194_ = v___x_203_;
v_k_195_ = v___x_204_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_lt_218_, lean_object* v_hi_219_, lean_object* v_pivot_220_, lean_object* v_as_221_, lean_object* v_i_222_, lean_object* v_k_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_218_, v_hi_219_, v_pivot_220_, v_as_221_, v_i_222_, v_k_223_);
lean_dec(v_hi_219_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(lean_object* v_lt_225_, lean_object* v_n_226_, lean_object* v_as_227_, lean_object* v_lo_228_, lean_object* v_hi_229_){
_start:
{
lean_object* v___y_231_; uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_lt(v_lo_228_, v_hi_229_);
if (v___x_241_ == 0)
{
lean_dec(v_lo_228_);
lean_dec_ref(v_lt_225_);
return v_as_227_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_mid_244_; lean_object* v___y_246_; lean_object* v___y_252_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_242_ = lean_nat_add(v_lo_228_, v_hi_229_);
v___x_243_ = lean_unsigned_to_nat(1u);
v_mid_244_ = lean_nat_shiftr(v___x_242_, v___x_243_);
lean_dec(v___x_242_);
v___x_257_ = lean_array_fget_borrowed(v_as_227_, v_mid_244_);
v___x_258_ = lean_array_fget_borrowed(v_as_227_, v_lo_228_);
lean_inc(v___x_258_);
lean_inc(v___x_257_);
lean_inc_ref(v_lt_225_);
v___x_259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_225_, v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
v___y_252_ = v_as_227_;
goto v___jp_251_;
}
else
{
lean_object* v___x_260_; 
v___x_260_ = lean_array_fswap(v_as_227_, v_lo_228_, v_mid_244_);
v___y_252_ = v___x_260_;
goto v___jp_251_;
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_array_fget_borrowed(v___y_246_, v_mid_244_);
v___x_248_ = lean_array_fget_borrowed(v___y_246_, v_hi_229_);
lean_inc(v___x_248_);
lean_inc(v___x_247_);
lean_inc_ref(v_lt_225_);
v___x_249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_225_, v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_dec(v_mid_244_);
v___y_231_ = v___y_246_;
goto v___jp_230_;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = lean_array_fswap(v___y_246_, v_mid_244_, v_hi_229_);
lean_dec(v_mid_244_);
v___y_231_ = v___x_250_;
goto v___jp_230_;
}
}
v___jp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_253_ = lean_array_fget_borrowed(v___y_252_, v_hi_229_);
v___x_254_ = lean_array_fget_borrowed(v___y_252_, v_lo_228_);
lean_inc(v___x_254_);
lean_inc(v___x_253_);
lean_inc_ref(v_lt_225_);
v___x_255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_225_, v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
v___y_246_ = v___y_252_;
goto v___jp_245_;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = lean_array_fswap(v___y_252_, v_lo_228_, v_hi_229_);
v___y_246_ = v___x_256_;
goto v___jp_245_;
}
}
}
v___jp_230_:
{
lean_object* v_pivot_232_; lean_object* v___x_233_; lean_object* v_fst_234_; lean_object* v_snd_235_; uint8_t v___x_236_; 
v_pivot_232_ = lean_array_fget(v___y_231_, v_hi_229_);
lean_inc_n(v_lo_228_, 2);
lean_inc_ref(v_lt_225_);
v___x_233_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_225_, v_hi_229_, v_pivot_232_, v___y_231_, v_lo_228_, v_lo_228_);
v_fst_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_fst_234_);
v_snd_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_snd_235_);
lean_dec_ref(v___x_233_);
v___x_236_ = lean_nat_dec_le(v_hi_229_, v_fst_234_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_inc_ref(v_lt_225_);
v___x_237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_225_, v_n_226_, v_snd_235_, v_lo_228_, v_fst_234_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_fst_234_, v___x_238_);
lean_dec(v_fst_234_);
v_as_227_ = v___x_237_;
v_lo_228_ = v___x_239_;
goto _start;
}
else
{
lean_dec(v_fst_234_);
lean_dec(v_lo_228_);
lean_dec_ref(v_lt_225_);
return v_snd_235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___boxed(lean_object* v_lt_261_, lean_object* v_n_262_, lean_object* v_as_263_, lean_object* v_lo_264_, lean_object* v_hi_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_261_, v_n_262_, v_as_263_, v_lo_264_, v_hi_265_);
lean_dec(v_hi_265_);
lean_dec(v_n_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(lean_object* v_threshold_267_, lean_object* v_p_268_, lean_object* v_x_269_, lean_object* v_____s_270_){
_start:
{
lean_object* v_fst_271_; lean_object* v_snd_272_; uint8_t v___x_273_; 
v_fst_271_ = lean_ctor_get(v_x_269_, 0);
v_snd_272_ = lean_ctor_get(v_x_269_, 1);
v___x_273_ = lean_nat_dec_lt(v_threshold_267_, v_snd_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec_ref(v_x_269_);
lean_dec_ref(v_p_268_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_____s_270_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; uint8_t v___x_276_; 
lean_inc(v_fst_271_);
v___x_275_ = lean_apply_1(v_p_268_, v_fst_271_);
v___x_276_ = lean_unbox(v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec_ref(v_x_269_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_____s_270_);
return v___x_277_;
}
else
{
lean_object* v_r_278_; lean_object* v___x_279_; 
v_r_278_ = lean_array_push(v_____s_270_, v_x_269_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_r_278_);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed(lean_object* v_threshold_280_, lean_object* v_p_281_, lean_object* v_x_282_, lean_object* v_____s_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(v_threshold_280_, v_p_281_, v_x_282_, v_____s_283_);
lean_dec(v_threshold_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(lean_object* v_counters_287_, lean_object* v_threshold_288_, lean_object* v_p_289_, lean_object* v_lt_290_){
_start:
{
lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v_r_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___f_291_ = lean_alloc_closure((void*)(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed), 4, 2);
lean_closure_set(v___f_291_, 0, v_threshold_288_);
lean_closure_set(v___f_291_, 1, v_p_289_);
v___x_292_ = lean_unsigned_to_nat(0u);
v_r_293_ = ((lean_object*)(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0));
v___x_294_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_counters_287_, v_r_293_, v___f_291_);
v___x_295_ = lean_array_get_size(v___x_294_);
v___x_296_ = lean_nat_dec_eq(v___x_295_, v___x_292_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___y_300_; uint8_t v___x_304_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_sub(v___x_295_, v___x_297_);
v___x_304_ = lean_nat_dec_le(v___x_292_, v___x_298_);
if (v___x_304_ == 0)
{
lean_inc(v___x_298_);
v___y_300_ = v___x_298_;
goto v___jp_299_;
}
else
{
v___y_300_ = v___x_292_;
goto v___jp_299_;
}
v___jp_299_:
{
uint8_t v___x_301_; 
v___x_301_ = lean_nat_dec_le(v___y_300_, v___x_298_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_dec(v___x_298_);
lean_inc(v___y_300_);
v___x_302_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_290_, v___x_295_, v___x_294_, v___y_300_, v___y_300_);
lean_dec(v___y_300_);
return v___x_302_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_290_, v___x_295_, v___x_294_, v___y_300_, v___x_298_);
lean_dec(v___x_298_);
return v___x_303_;
}
}
}
else
{
lean_dec_ref(v_lt_290_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___boxed(lean_object* v_counters_305_, lean_object* v_threshold_306_, lean_object* v_p_307_, lean_object* v_lt_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(v_counters_305_, v_threshold_306_, v_p_307_, v_lt_308_);
lean_dec_ref(v_counters_305_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(lean_object* v_keys_310_, lean_object* v_vals_311_, lean_object* v_i_312_, lean_object* v_k_313_){
_start:
{
uint8_t v___y_319_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_array_get_size(v_keys_310_);
v___x_323_ = lean_nat_dec_lt(v_i_312_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_i_312_);
v___x_324_ = lean_box(0);
return v___x_324_;
}
else
{
lean_object* v_k_x27_325_; 
v_k_x27_325_ = lean_array_fget_borrowed(v_keys_310_, v_i_312_);
if (lean_obj_tag(v_k_313_) == 0)
{
if (lean_obj_tag(v_k_x27_325_) == 0)
{
lean_object* v_declName_326_; uint8_t v_inv_327_; lean_object* v_declName_328_; uint8_t v_inv_329_; uint8_t v___x_330_; 
v_declName_326_ = lean_ctor_get(v_k_313_, 0);
v_inv_327_ = lean_ctor_get_uint8(v_k_313_, sizeof(void*)*1 + 1);
v_declName_328_ = lean_ctor_get(v_k_x27_325_, 0);
v_inv_329_ = lean_ctor_get_uint8(v_k_x27_325_, sizeof(void*)*1 + 1);
v___x_330_ = lean_name_eq(v_declName_326_, v_declName_328_);
if (v___x_330_ == 0)
{
v___y_319_ = v___x_330_;
goto v___jp_318_;
}
else
{
if (v_inv_329_ == 0)
{
if (v_inv_327_ == 0)
{
v___y_319_ = v___x_330_;
goto v___jp_318_;
}
else
{
goto v___jp_314_;
}
}
else
{
v___y_319_ = v_inv_327_;
goto v___jp_318_;
}
}
}
else
{
goto v___jp_314_;
}
}
else
{
if (lean_obj_tag(v_k_x27_325_) == 0)
{
goto v___jp_314_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = l_Lean_Meta_Origin_key(v_k_313_);
v___x_332_ = l_Lean_Meta_Origin_key(v_k_x27_325_);
v___x_333_ = lean_name_eq(v___x_331_, v___x_332_);
lean_dec(v___x_332_);
lean_dec(v___x_331_);
v___y_319_ = v___x_333_;
goto v___jp_318_;
}
}
}
v___jp_314_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_i_312_, v___x_315_);
lean_dec(v_i_312_);
v_i_312_ = v___x_316_;
goto _start;
}
v___jp_318_:
{
if (v___y_319_ == 0)
{
goto v___jp_314_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_array_fget_borrowed(v_vals_311_, v_i_312_);
lean_dec(v_i_312_);
lean_inc(v___x_320_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_keys_334_, lean_object* v_vals_335_, lean_object* v_i_336_, lean_object* v_k_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_334_, v_vals_335_, v_i_336_, v_k_337_);
lean_dec_ref(v_k_337_);
lean_dec_ref(v_vals_335_);
lean_dec_ref(v_keys_334_);
return v_res_338_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(lean_object* v_x_339_, size_t v_x_340_, lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
lean_object* v_es_342_; lean_object* v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v_j_346_; lean_object* v___x_347_; 
v_es_342_ = lean_ctor_get(v_x_339_, 0);
v___x_343_ = lean_box(2);
v___x_344_ = ((size_t)31ULL);
v___x_345_ = lean_usize_land(v_x_340_, v___x_344_);
v_j_346_ = lean_usize_to_nat(v___x_345_);
v___x_347_ = lean_array_get_borrowed(v___x_343_, v_es_342_, v_j_346_);
lean_dec(v_j_346_);
switch(lean_obj_tag(v___x_347_))
{
case 0:
{
lean_object* v_key_348_; lean_object* v_val_349_; uint8_t v___y_351_; 
v_key_348_ = lean_ctor_get(v___x_347_, 0);
v_val_349_ = lean_ctor_get(v___x_347_, 1);
if (lean_obj_tag(v_x_341_) == 0)
{
if (lean_obj_tag(v_key_348_) == 0)
{
lean_object* v_declName_354_; uint8_t v_inv_355_; lean_object* v_declName_356_; uint8_t v_inv_357_; uint8_t v___x_358_; 
v_declName_354_ = lean_ctor_get(v_x_341_, 0);
v_inv_355_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*1 + 1);
v_declName_356_ = lean_ctor_get(v_key_348_, 0);
v_inv_357_ = lean_ctor_get_uint8(v_key_348_, sizeof(void*)*1 + 1);
v___x_358_ = lean_name_eq(v_declName_354_, v_declName_356_);
if (v___x_358_ == 0)
{
v___y_351_ = v___x_358_;
goto v___jp_350_;
}
else
{
if (v_inv_357_ == 0)
{
if (v_inv_355_ == 0)
{
v___y_351_ = v___x_358_;
goto v___jp_350_;
}
else
{
lean_object* v___x_359_; 
v___x_359_ = lean_box(0);
return v___x_359_;
}
}
else
{
v___y_351_ = v_inv_355_;
goto v___jp_350_;
}
}
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_box(0);
return v___x_360_;
}
}
else
{
if (lean_obj_tag(v_key_348_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = l_Lean_Meta_Origin_key(v_x_341_);
v___x_363_ = l_Lean_Meta_Origin_key(v_key_348_);
v___x_364_ = lean_name_eq(v___x_362_, v___x_363_);
lean_dec(v___x_363_);
lean_dec(v___x_362_);
v___y_351_ = v___x_364_;
goto v___jp_350_;
}
}
v___jp_350_:
{
if (v___y_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
lean_inc(v_val_349_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_val_349_);
return v___x_353_;
}
}
}
case 1:
{
lean_object* v_node_365_; size_t v___x_366_; size_t v___x_367_; 
v_node_365_ = lean_ctor_get(v___x_347_, 0);
v___x_366_ = ((size_t)5ULL);
v___x_367_ = lean_usize_shift_right(v_x_340_, v___x_366_);
v_x_339_ = v_node_365_;
v_x_340_ = v___x_367_;
goto _start;
}
default: 
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
}
}
else
{
lean_object* v_ks_370_; lean_object* v_vs_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_ks_370_ = lean_ctor_get(v_x_339_, 0);
v_vs_371_ = lean_ctor_get(v_x_339_, 1);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_ks_370_, v_vs_371_, v___x_372_, v_x_341_);
return v___x_373_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_339_ = stack[0].m_obj;
size_t v_x_340_ = stack[1].m_num;
lean_object* v_x_341_ = stack[2].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_339_, v_x_340_, v_x_341_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___boxed(lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_4484__boxed_378_; lean_object* v_res_379_; 
v_x_4484__boxed_378_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_res_379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_375_, v_x_4484__boxed_378_, v_x_377_);
lean_dec_ref(v_x_377_);
lean_dec_ref(v_x_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
uint64_t v___y_383_; uint64_t v___y_387_; uint64_t v___y_391_; 
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v_inv_394_; 
v_inv_394_ = lean_ctor_get_uint8(v_x_381_, sizeof(void*)*1 + 1);
if (v_inv_394_ == 0)
{
lean_object* v_declName_395_; 
v_declName_395_ = lean_ctor_get(v_x_381_, 0);
if (lean_obj_tag(v_declName_395_) == 0)
{
uint64_t v___x_396_; 
v___x_396_ = 1723ULL;
v___y_387_ = v___x_396_;
goto v___jp_386_;
}
else
{
uint64_t v_hash_397_; 
v_hash_397_ = lean_ctor_get_uint64(v_declName_395_, sizeof(void*)*2);
v___y_387_ = v_hash_397_;
goto v___jp_386_;
}
}
else
{
lean_object* v_declName_398_; 
v_declName_398_ = lean_ctor_get(v_x_381_, 0);
if (lean_obj_tag(v_declName_398_) == 0)
{
uint64_t v___x_399_; 
v___x_399_ = 1723ULL;
v___y_391_ = v___x_399_;
goto v___jp_390_;
}
else
{
uint64_t v_hash_400_; 
v_hash_400_ = lean_ctor_get_uint64(v_declName_398_, sizeof(void*)*2);
v___y_391_ = v_hash_400_;
goto v___jp_390_;
}
}
}
else
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Origin_key(v_x_381_);
if (lean_obj_tag(v___x_401_) == 0)
{
uint64_t v___x_402_; 
v___x_402_ = 1723ULL;
v___y_383_ = v___x_402_;
goto v___jp_382_;
}
else
{
uint64_t v_hash_403_; 
v_hash_403_ = lean_ctor_get_uint64(v___x_401_, sizeof(void*)*2);
lean_dec(v___x_401_);
v___y_383_ = v_hash_403_;
goto v___jp_382_;
}
}
v___jp_382_:
{
size_t v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_uint64_to_usize(v___y_383_);
v___x_385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_380_, v___x_384_, v_x_381_);
return v___x_385_;
}
v___jp_386_:
{
uint64_t v___x_388_; uint64_t v___x_389_; 
v___x_388_ = 13ULL;
v___x_389_ = lean_uint64_mix_hash(v___y_387_, v___x_388_);
v___y_383_ = v___x_389_;
goto v___jp_382_;
}
v___jp_390_:
{
uint64_t v___x_392_; uint64_t v___x_393_; 
v___x_392_ = 11ULL;
v___x_393_ = lean_uint64_mix_hash(v___y_391_, v___x_392_);
v___y_383_ = v___x_393_;
goto v___jp_382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___boxed(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_404_, v_x_405_);
lean_dec_ref(v_x_405_);
lean_dec_ref(v_x_404_);
return v_res_406_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_412_; double v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_float_of_nat(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = l_Lean_crossEmoji;
v___x_421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8));
v___x_422_ = lean_string_append(v___x_421_, v___x_420_);
return v___x_422_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(lean_object* v_usedCounters_x3f_423_, lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_, lean_object* v___y_428_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_427_);
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_479_; 
v_a_432_ = lean_array_uget(v_as_424_, v_i_426_);
v_fst_433_ = lean_ctor_get(v_a_432_, 0);
v_snd_434_ = lean_ctor_get(v_a_432_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_432_);
if (v_isSharedCheck_479_ == 0)
{
v___x_436_ = v_a_432_;
v_isShared_437_ = v_isSharedCheck_479_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_434_);
lean_inc(v_fst_433_);
lean_dec(v_a_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_479_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
lean_inc(v_fst_433_);
v___x_439_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_fst_433_, v___y_428_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_usedMsg_442_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
if (lean_obj_tag(v_usedCounters_x3f_423_) == 1)
{
lean_object* v_val_463_; lean_object* v___x_464_; 
v_val_463_ = lean_ctor_get(v_usedCounters_x3f_423_, 0);
v___x_464_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_val_463_, v_fst_433_);
lean_dec(v_fst_433_);
if (lean_obj_tag(v___x_464_) == 1)
{
lean_object* v_val_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_val_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7));
v___x_467_ = l_Nat_reprFast(v_val_465_);
v___x_468_ = lean_string_append(v___x_466_, v___x_467_);
lean_dec_ref(v___x_467_);
v_usedMsg_442_ = v___x_468_;
goto v___jp_441_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v___x_464_);
v___x_469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9);
v_usedMsg_442_ = v___x_469_;
goto v___jp_441_;
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v_fst_433_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v_usedMsg_442_ = v___x_470_;
goto v___jp_441_;
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; double v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_444_ = lean_box(0);
v___x_445_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_447_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_447_, 0, v___x_443_);
lean_ctor_set(v___x_447_, 1, v___x_444_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
lean_ctor_set_float(v___x_447_, sizeof(void*)*3, v___x_445_);
lean_ctor_set_float(v___x_447_, sizeof(void*)*3 + 8, v___x_445_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3 + 16, v___x_430_);
v___x_448_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 7);
lean_ctor_set(v___x_436_, 1, v___x_448_);
lean_ctor_set(v___x_436_, 0, v_a_440_);
v___x_450_ = v___x_436_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_440_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_462_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; size_t v___x_459_; size_t v___x_460_; 
v___x_451_ = l_Nat_reprFast(v_snd_434_);
v___x_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = l_Lean_MessageData_ofFormat(v___x_452_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_450_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_stringToMessageData(v_usedMsg_442_);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_447_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
lean_ctor_set(v___x_457_, 2, v___x_438_);
v___x_458_ = lean_array_push(v_b_427_, v___x_457_);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_add(v_i_426_, v___x_459_);
v_i_426_ = v___x_460_;
v_b_427_ = v___x_458_;
goto _start;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_436_);
lean_dec(v_snd_434_);
lean_dec(v_fst_433_);
lean_dec_ref(v_b_427_);
v_a_471_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_439_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_439_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_usedCounters_x3f_423_ = stack[0].m_obj;
lean_object* v_as_424_ = stack[1].m_obj;
size_t v_sz_425_ = stack[2].m_num;
size_t v_i_426_ = stack[3].m_num;
lean_object* v_b_427_ = stack[4].m_obj;
lean_object* v___y_428_ = stack[5].m_obj;
lean_object* v_res_480_;
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_423_, v_as_424_, v_sz_425_, v_i_426_, v_b_427_, v___y_428_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___boxed(lean_object* v_usedCounters_x3f_481_, lean_object* v_as_482_, lean_object* v_sz_483_, lean_object* v_i_484_, lean_object* v_b_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
size_t v_sz_boxed_488_; size_t v_i_boxed_489_; lean_object* v_res_490_; 
v_sz_boxed_488_ = lean_unbox_usize(v_sz_483_);
lean_dec(v_sz_483_);
v_i_boxed_489_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_481_, v_as_482_, v_sz_boxed_488_, v_i_boxed_489_, v_b_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v_as_482_);
lean_dec(v_usedCounters_x3f_481_);
return v_res_490_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = l_Lean_Meta_instInhabitedOrigin_default;
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
return v___x_495_;
}
}
lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary(lean_object* v_counters_499_, lean_object* v_usedCounters_x3f_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___f_506_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0));
v___f_507_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1));
v___x_508_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_503_);
v___x_509_ = l_Lean_diagnostics_threshold;
v___x_510_ = l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(v___x_508_, v___x_509_);
lean_dec_ref(v___x_508_);
v___x_511_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(v_counters_499_, v___x_510_, v___f_507_, v___f_506_);
v___x_512_ = lean_array_get_size(v___x_511_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_nat_dec_eq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; size_t v_sz_517_; size_t v___x_518_; lean_object* v___x_519_; 
v___x_515_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2, &l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2_once, _init_l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v_sz_517_ = lean_array_size(v___x_511_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_500_, v___x_511_, v_sz_517_, v___x_518_, v___x_516_, v_a_504_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_537_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_537_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_537_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_537_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v_snd_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_535_; 
v___x_524_ = lean_array_get(v___x_515_, v___x_511_, v___x_513_);
lean_dec_ref(v___x_511_);
v_snd_525_ = lean_ctor_get(v___x_524_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; 
v_unused_536_ = lean_ctor_get(v___x_524_, 0);
lean_dec(v_unused_536_);
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snd_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v_a_520_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_520_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_snd_525_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_530_);
v___x_532_ = v___x_522_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v___x_511_);
v_a_538_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_519_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_519_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref(v___x_511_);
v___x_546_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3));
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_mkSimpDiagSummary_0interp(lean_interpreter_value* stack)
{
lean_object* v_counters_499_ = stack[0].m_obj;
lean_object* v_usedCounters_x3f_500_ = stack[1].m_obj;
lean_object* v_a_501_ = stack[2].m_obj;
lean_object* v_a_502_ = stack[3].m_obj;
lean_object* v_a_503_ = stack[4].m_obj;
lean_object* v_a_504_ = stack[5].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_counters_499_, v_usedCounters_x3f_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___boxed(lean_object* v_counters_549_, lean_object* v_usedCounters_x3f_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_counters_549_, v_usedCounters_x3f_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_usedCounters_x3f_550_);
lean_dec_ref(v_counters_549_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(lean_object* v_00_u03b2_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___boxed(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(v_00_u03b2_561_, v_x_562_, v_x_563_);
lean_dec_ref(v_x_563_);
lean_dec_ref(v_x_562_);
return v_res_564_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(lean_object* v_usedCounters_x3f_565_, lean_object* v_as_566_, size_t v_sz_567_, size_t v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_565_, v_as_566_, v_sz_567_, v_i_568_, v_b_569_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_usedCounters_x3f_565_ = stack[0].m_obj;
lean_object* v_as_566_ = stack[1].m_obj;
size_t v_sz_567_ = stack[2].m_num;
size_t v_i_568_ = stack[3].m_num;
lean_object* v_b_569_ = stack[4].m_obj;
lean_object* v___y_570_ = stack[5].m_obj;
lean_object* v___y_571_ = stack[6].m_obj;
lean_object* v___y_572_ = stack[7].m_obj;
lean_object* v___y_573_ = stack[8].m_obj;
lean_object* v_res_576_;
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(v_usedCounters_x3f_565_, v_as_566_, v_sz_567_, v_i_568_, v_b_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___boxed(lean_object* v_usedCounters_x3f_577_, lean_object* v_as_578_, lean_object* v_sz_579_, lean_object* v_i_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
size_t v_sz_boxed_587_; size_t v_i_boxed_588_; lean_object* v_res_589_; 
v_sz_boxed_587_ = lean_unbox_usize(v_sz_579_);
lean_dec(v_sz_579_);
v_i_boxed_588_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(v_usedCounters_x3f_577_, v_as_578_, v_sz_boxed_587_, v_i_boxed_588_, v_b_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec_ref(v_as_578_);
lean_dec(v_usedCounters_x3f_577_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(lean_object* v_00_u03c3_590_, lean_object* v_00_u03b2_591_, lean_object* v_map_592_, lean_object* v_init_593_, lean_object* v_f_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_592_, v_init_593_, v_f_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___boxed(lean_object* v_00_u03c3_596_, lean_object* v_00_u03b2_597_, lean_object* v_map_598_, lean_object* v_init_599_, lean_object* v_f_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(v_00_u03c3_596_, v_00_u03b2_597_, v_map_598_, v_init_599_, v_f_600_);
lean_dec_ref(v_map_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(lean_object* v_lt_602_, lean_object* v_n_603_, lean_object* v_as_604_, lean_object* v_lo_605_, lean_object* v_hi_606_, lean_object* v_w_607_, lean_object* v_hlo_608_, lean_object* v_hhi_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_602_, v_n_603_, v_as_604_, v_lo_605_, v_hi_606_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___boxed(lean_object* v_lt_611_, lean_object* v_n_612_, lean_object* v_as_613_, lean_object* v_lo_614_, lean_object* v_hi_615_, lean_object* v_w_616_, lean_object* v_hlo_617_, lean_object* v_hhi_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(v_lt_611_, v_n_612_, v_as_613_, v_lo_614_, v_hi_615_, v_w_616_, v_hlo_617_, v_hhi_618_);
lean_dec(v_hi_615_);
lean_dec(v_n_612_);
return v_res_619_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(lean_object* v_00_u03b2_620_, lean_object* v_x_621_, size_t v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_621_, v_x_622_, v_x_623_);
return v___x_624_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_621_ = stack[1].m_obj;
size_t v_x_622_ = stack[2].m_num;
lean_object* v_x_623_ = stack[3].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(lean_box(0), v_x_621_, v_x_622_, v_x_623_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___boxed(lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_5090__boxed_630_; lean_object* v_res_631_; 
v_x_5090__boxed_630_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_res_631_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(v_00_u03b2_626_, v_x_627_, v_x_5090__boxed_630_, v_x_629_);
lean_dec_ref(v_x_629_);
lean_dec_ref(v_x_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2___redArg(lean_object* v_map_632_, lean_object* v_f_633_, lean_object* v_init_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_633_, v_map_632_, v_init_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_636_, lean_object* v_00_u03c3_637_, lean_object* v_00_u03b2_638_, lean_object* v_map_639_, lean_object* v_f_640_, lean_object* v_init_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_640_, v_map_639_, v_init_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(lean_object* v_lt_643_, lean_object* v_n_644_, lean_object* v_lo_645_, lean_object* v_hi_646_, lean_object* v_hhi_647_, lean_object* v_pivot_648_, lean_object* v_as_649_, lean_object* v_i_650_, lean_object* v_k_651_, lean_object* v_ilo_652_, lean_object* v_ik_653_, lean_object* v_w_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_643_, v_hi_646_, v_pivot_648_, v_as_649_, v_i_650_, v_k_651_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___boxed(lean_object* v_lt_656_, lean_object* v_n_657_, lean_object* v_lo_658_, lean_object* v_hi_659_, lean_object* v_hhi_660_, lean_object* v_pivot_661_, lean_object* v_as_662_, lean_object* v_i_663_, lean_object* v_k_664_, lean_object* v_ilo_665_, lean_object* v_ik_666_, lean_object* v_w_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(v_lt_656_, v_n_657_, v_lo_658_, v_hi_659_, v_hhi_660_, v_pivot_661_, v_as_662_, v_i_663_, v_k_664_, v_ilo_665_, v_ik_666_, v_w_667_);
lean_dec(v_hi_659_);
lean_dec(v_lo_658_);
lean_dec(v_n_657_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_heq_672_, lean_object* v_i_673_, lean_object* v_k_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_670_, v_vals_671_, v_i_673_, v_k_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_heq_679_, lean_object* v_i_680_, lean_object* v_k_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(v_00_u03b2_676_, v_keys_677_, v_vals_678_, v_heq_679_, v_i_680_, v_k_681_);
lean_dec_ref(v_k_681_);
lean_dec_ref(v_vals_678_);
lean_dec_ref(v_keys_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_683_, lean_object* v_00_u03c3_684_, lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_f_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_687_, v_x_688_, v_x_689_);
return v___x_690_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_00_u03c3_693_, lean_object* v_00_u03c3_694_, lean_object* v_f_695_, lean_object* v_as_696_, size_t v_i_697_, size_t v_stop_698_, lean_object* v_b_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_695_, v_as_696_, v_i_697_, v_stop_698_, v_b_699_);
return v___x_700_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_695_ = stack[4].m_obj;
lean_object* v_as_696_ = stack[5].m_obj;
size_t v_i_697_ = stack[6].m_num;
size_t v_stop_698_ = stack[7].m_num;
lean_object* v_b_699_ = stack[8].m_obj;
lean_object* v_res_701_;
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_695_, v_as_696_, v_i_697_, v_stop_698_, v_b_699_);
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_00_u03c3_704_, lean_object* v_00_u03c3_705_, lean_object* v_f_706_, lean_object* v_as_707_, lean_object* v_i_708_, lean_object* v_stop_709_, lean_object* v_b_710_){
_start:
{
size_t v_i_boxed_711_; size_t v_stop_boxed_712_; lean_object* v_res_713_; 
v_i_boxed_711_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_stop_boxed_712_ = lean_unbox_usize(v_stop_709_);
lean_dec(v_stop_709_);
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b1_702_, v_00_u03b2_703_, v_00_u03c3_704_, v_00_u03c3_705_, v_f_706_, v_as_707_, v_i_boxed_711_, v_stop_boxed_712_, v_b_710_);
lean_dec_ref(v_as_707_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03c3_714_, lean_object* v_00_u03c3_715_, lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_f_718_, lean_object* v_keys_719_, lean_object* v_vals_720_, lean_object* v_heq_721_, lean_object* v_i_722_, lean_object* v_acc_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_718_, v_keys_719_, v_vals_720_, v_i_722_, v_acc_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03c3_725_, lean_object* v_00_u03c3_726_, lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_f_729_, lean_object* v_keys_730_, lean_object* v_vals_731_, lean_object* v_heq_732_, lean_object* v_i_733_, lean_object* v_acc_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(v_00_u03c3_725_, v_00_u03c3_726_, v_00_u03b1_727_, v_00_u03b2_728_, v_f_729_, v_keys_730_, v_vals_731_, v_heq_732_, v_i_733_, v_acc_734_);
lean_dec_ref(v_vals_731_);
lean_dec_ref(v_keys_730_);
return v_res_735_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_738_ = l_Lean_stringToMessageData(v___x_737_);
return v___x_738_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_as_739_, size_t v_sz_740_, size_t v_i_741_, lean_object* v_b_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = lean_usize_dec_lt(v_i_741_, v_sz_740_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_b_742_);
return v___x_747_;
}
else
{
lean_object* v_snd_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_792_; 
v_snd_748_ = lean_ctor_get(v_b_742_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_b_742_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_b_742_, 0);
lean_dec(v_unused_793_);
v___x_750_ = v_b_742_;
v_isShared_751_ = v_isSharedCheck_792_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_748_);
lean_dec(v_b_742_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_792_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_a_752_; lean_object* v_keys_753_; lean_object* v_origin_754_; lean_object* v_data_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_a_752_ = lean_array_uget_borrowed(v_as_739_, v_i_741_);
v_keys_753_ = lean_ctor_get(v_a_752_, 0);
v_origin_754_ = lean_ctor_get(v_a_752_, 4);
v_data_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_756_ = lean_box(0);
lean_inc_ref(v_origin_754_);
v___x_757_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_754_, v___y_744_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
lean_inc_ref(v_keys_753_);
v___x_759_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_753_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; double v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_762_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_764_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_764_, 0, v___x_761_);
lean_ctor_set(v___x_764_, 1, v___x_756_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
lean_ctor_set_float(v___x_764_, sizeof(void*)*3, v___x_762_);
lean_ctor_set_float(v___x_764_, sizeof(void*)*3 + 8, v___x_762_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*3 + 16, v___x_746_);
v___x_765_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v_a_758_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_a_760_);
v___x_768_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_768_, 0, v___x_764_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
lean_ctor_set(v___x_768_, 2, v_data_755_);
v___x_769_ = lean_array_push(v_snd_748_, v___x_768_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_769_);
lean_ctor_set(v___x_750_, 0, v___x_756_);
v___x_771_ = v___x_750_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_741_, v___x_772_);
v_i_741_ = v___x_773_;
v_b_742_ = v___x_771_;
goto _start;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_758_);
lean_del_object(v___x_750_);
lean_dec(v_snd_748_);
v_a_776_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_759_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_759_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_750_);
lean_dec(v_snd_748_);
v_a_784_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_757_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_757_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_739_ = stack[0].m_obj;
size_t v_sz_740_ = stack[1].m_num;
size_t v_i_741_ = stack[2].m_num;
lean_object* v_b_742_ = stack[3].m_obj;
lean_object* v___y_743_ = stack[4].m_obj;
lean_object* v___y_744_ = stack[5].m_obj;
lean_object* v_res_794_;
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_739_, v_sz_740_, v_i_741_, v_b_742_, v___y_743_, v___y_744_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_as_795_, lean_object* v_sz_796_, lean_object* v_i_797_, lean_object* v_b_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
size_t v_sz_boxed_802_; size_t v_i_boxed_803_; lean_object* v_res_804_; 
v_sz_boxed_802_ = lean_unbox_usize(v_sz_796_);
lean_dec(v_sz_796_);
v_i_boxed_803_ = lean_unbox_usize(v_i_797_);
lean_dec(v_i_797_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_795_, v_sz_boxed_802_, v_i_boxed_803_, v_b_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v_as_795_);
return v_res_804_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(lean_object* v_as_805_, size_t v_sz_806_, size_t v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = lean_usize_dec_lt(v_i_807_, v_sz_806_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_b_808_);
return v___x_815_;
}
else
{
lean_object* v_snd_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_860_; 
v_snd_816_ = lean_ctor_get(v_b_808_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_b_808_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_b_808_, 0);
lean_dec(v_unused_861_);
v___x_818_ = v_b_808_;
v_isShared_819_ = v_isSharedCheck_860_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snd_816_);
lean_dec(v_b_808_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_860_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_a_820_; lean_object* v_keys_821_; lean_object* v_origin_822_; lean_object* v_data_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_a_820_ = lean_array_uget_borrowed(v_as_805_, v_i_807_);
v_keys_821_ = lean_ctor_get(v_a_820_, 0);
v_origin_822_ = lean_ctor_get(v_a_820_, 4);
v_data_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_824_ = lean_box(0);
lean_inc_ref(v_origin_822_);
v___x_825_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_822_, v___y_812_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
lean_inc_ref(v_keys_821_);
v___x_827_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_821_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; double v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v___x_829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_830_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_832_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_832_, 0, v___x_829_);
lean_ctor_set(v___x_832_, 1, v___x_824_);
lean_ctor_set(v___x_832_, 2, v___x_831_);
lean_ctor_set_float(v___x_832_, sizeof(void*)*3, v___x_830_);
lean_ctor_set_float(v___x_832_, sizeof(void*)*3 + 8, v___x_830_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*3 + 16, v___x_814_);
v___x_833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v_a_826_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_a_828_);
v___x_836_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_836_, 0, v___x_832_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
lean_ctor_set(v___x_836_, 2, v_data_823_);
v___x_837_ = lean_array_push(v_snd_816_, v___x_836_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v___x_837_);
lean_ctor_set(v___x_818_, 0, v___x_824_);
v___x_839_ = v___x_818_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_807_, v___x_840_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_805_, v_sz_806_, v___x_841_, v___x_839_, v___y_811_, v___y_812_);
return v___x_842_;
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_a_826_);
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
v_a_844_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_827_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_827_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
v_a_852_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_825_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_825_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_805_ = stack[0].m_obj;
size_t v_sz_806_ = stack[1].m_num;
size_t v_i_807_ = stack[2].m_num;
lean_object* v_b_808_ = stack[3].m_obj;
lean_object* v___y_809_ = stack[4].m_obj;
lean_object* v___y_810_ = stack[5].m_obj;
lean_object* v___y_811_ = stack[6].m_obj;
lean_object* v___y_812_ = stack[7].m_obj;
lean_object* v_res_862_;
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_as_805_, v_sz_806_, v_i_807_, v_b_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2___boxed(lean_object* v_as_863_, lean_object* v_sz_864_, lean_object* v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
size_t v_sz_boxed_872_; size_t v_i_boxed_873_; lean_object* v_res_874_; 
v_sz_boxed_872_ = lean_unbox_usize(v_sz_864_);
lean_dec(v_sz_864_);
v_i_boxed_873_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_as_863_, v_sz_boxed_872_, v_i_boxed_873_, v_b_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec_ref(v_as_863_);
return v_res_874_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(lean_object* v_init_875_, lean_object* v_n_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
if (lean_obj_tag(v_n_876_) == 0)
{
lean_object* v_cs_883_; lean_object* v___x_884_; lean_object* v___x_885_; size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; 
v_cs_883_ = lean_ctor_get(v_n_876_, 0);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_b_877_);
v_sz_886_ = lean_array_size(v_cs_883_);
v___x_887_ = ((size_t)0ULL);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_875_, v_cs_883_, v_sz_886_, v___x_887_, v___x_885_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_903_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_903_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_fst_893_; 
v_fst_893_ = lean_ctor_get(v_a_889_, 0);
if (lean_obj_tag(v_fst_893_) == 0)
{
lean_object* v_snd_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v_snd_894_ = lean_ctor_get(v_a_889_, 1);
lean_inc(v_snd_894_);
lean_dec(v_a_889_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_snd_894_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_895_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_object* v_val_899_; lean_object* v___x_901_; 
lean_inc_ref(v_fst_893_);
lean_dec(v_a_889_);
v_val_899_ = lean_ctor_get(v_fst_893_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v_fst_893_, 1);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_val_899_);
v___x_901_ = v___x_891_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_val_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_888_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_888_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_vs_912_; lean_object* v___x_913_; lean_object* v___x_914_; size_t v_sz_915_; size_t v___x_916_; lean_object* v___x_917_; 
v_vs_912_ = lean_ctor_get(v_n_876_, 0);
v___x_913_ = lean_box(0);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_b_877_);
v_sz_915_ = lean_array_size(v_vs_912_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_vs_912_, v_sz_915_, v___x_916_, v___x_914_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_932_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_932_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_fst_922_; 
v_fst_922_ = lean_ctor_get(v_a_918_, 0);
if (lean_obj_tag(v_fst_922_) == 0)
{
lean_object* v_snd_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v_snd_923_ = lean_ctor_get(v_a_918_, 1);
lean_inc(v_snd_923_);
lean_dec(v_a_918_);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_snd_923_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_924_);
v___x_926_ = v___x_920_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_object* v_val_928_; lean_object* v___x_930_; 
lean_inc_ref(v_fst_922_);
lean_dec(v_a_918_);
v_val_928_ = lean_ctor_get(v_fst_922_, 0);
lean_inc(v_val_928_);
lean_dec_ref_known(v_fst_922_, 1);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v_val_928_);
v___x_930_ = v___x_920_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_val_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
v_a_933_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_917_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_917_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_875_ = stack[0].m_obj;
lean_object* v_n_876_ = stack[1].m_obj;
lean_object* v_b_877_ = stack[2].m_obj;
lean_object* v___y_878_ = stack[3].m_obj;
lean_object* v___y_879_ = stack[4].m_obj;
lean_object* v___y_880_ = stack[5].m_obj;
lean_object* v___y_881_ = stack[6].m_obj;
lean_object* v_res_941_;
v_res_941_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_875_, v_n_876_, v_b_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
stack->m_obj
 = v_res_941_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(lean_object* v_init_942_, lean_object* v_as_943_, size_t v_sz_944_, size_t v_i_945_, lean_object* v_b_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_946_);
return v___x_953_;
}
else
{
lean_object* v_snd_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_988_; 
v_snd_954_ = lean_ctor_get(v_b_946_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_b_946_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_b_946_, 0);
lean_dec(v_unused_989_);
v___x_956_ = v_b_946_;
v_isShared_957_ = v_isSharedCheck_988_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_954_);
lean_dec(v_b_946_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_988_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_960_; 
v___x_958_ = lean_box(0);
v_a_959_ = lean_array_uget_borrowed(v_as_943_, v_i_945_);
lean_inc(v_snd_954_);
v___x_960_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_942_, v_a_959_, v_snd_954_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_979_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_979_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
if (lean_obj_tag(v_a_961_) == 0)
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_a_961_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_965_);
v___x_967_ = v___x_956_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_snd_954_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_967_);
v___x_969_ = v___x_963_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; 
lean_del_object(v___x_963_);
lean_dec(v_snd_954_);
v_a_972_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v_a_961_, 1);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_a_972_);
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_974_ = v___x_956_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_a_972_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
size_t v___x_975_; size_t v___x_976_; 
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_add(v_i_945_, v___x_975_);
v_i_945_ = v___x_976_;
v_b_946_ = v___x_974_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
v_a_980_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_960_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_960_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_942_ = stack[0].m_obj;
lean_object* v_as_943_ = stack[1].m_obj;
size_t v_sz_944_ = stack[2].m_num;
size_t v_i_945_ = stack[3].m_num;
lean_object* v_b_946_ = stack[4].m_obj;
lean_object* v___y_947_ = stack[5].m_obj;
lean_object* v___y_948_ = stack[6].m_obj;
lean_object* v___y_949_ = stack[7].m_obj;
lean_object* v___y_950_ = stack[8].m_obj;
lean_object* v_res_990_;
v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_942_, v_as_943_, v_sz_944_, v_i_945_, v_b_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1___boxed(lean_object* v_init_991_, lean_object* v_as_992_, lean_object* v_sz_993_, lean_object* v_i_994_, lean_object* v_b_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
size_t v_sz_boxed_1001_; size_t v_i_boxed_1002_; lean_object* v_res_1003_; 
v_sz_boxed_1001_ = lean_unbox_usize(v_sz_993_);
lean_dec(v_sz_993_);
v_i_boxed_1002_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_991_, v_as_992_, v_sz_boxed_1001_, v_i_boxed_1002_, v_b_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec_ref(v_as_992_);
lean_dec_ref(v_init_991_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0___boxed(lean_object* v_init_1004_, lean_object* v_n_1005_, lean_object* v_b_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_1004_, v_n_1005_, v_b_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_n_1005_);
lean_dec_ref(v_init_1004_);
return v_res_1012_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1013_, size_t v_sz_1014_, size_t v_i_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_lt(v_i_1015_, v_sz_1014_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_b_1016_);
return v___x_1021_;
}
else
{
lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1066_; 
v_snd_1022_ = lean_ctor_get(v_b_1016_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_b_1016_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_b_1016_, 0);
lean_dec(v_unused_1067_);
v___x_1024_ = v_b_1016_;
v_isShared_1025_ = v_isSharedCheck_1066_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_dec(v_b_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1066_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_a_1026_; lean_object* v_keys_1027_; lean_object* v_origin_1028_; lean_object* v_data_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_a_1026_ = lean_array_uget_borrowed(v_as_1013_, v_i_1015_);
v_keys_1027_ = lean_ctor_get(v_a_1026_, 0);
v_origin_1028_ = lean_ctor_get(v_a_1026_, 4);
v_data_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1030_ = lean_box(0);
lean_inc_ref(v_origin_1028_);
v___x_1031_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_1028_, v___y_1018_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
lean_inc_ref(v_keys_1027_);
v___x_1033_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1027_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; double v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1036_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1038_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1038_, 0, v___x_1035_);
lean_ctor_set(v___x_1038_, 1, v___x_1030_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
lean_ctor_set_float(v___x_1038_, sizeof(void*)*3, v___x_1036_);
lean_ctor_set_float(v___x_1038_, sizeof(void*)*3 + 8, v___x_1036_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*3 + 16, v___x_1020_);
v___x_1039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_a_1032_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_a_1034_);
v___x_1042_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1038_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
lean_ctor_set(v___x_1042_, 2, v_data_1029_);
v___x_1043_ = lean_array_push(v_snd_1022_, v___x_1042_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1043_);
lean_ctor_set(v___x_1024_, 0, v___x_1030_);
v___x_1045_ = v___x_1024_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
size_t v___x_1046_; size_t v___x_1047_; 
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_add(v_i_1015_, v___x_1046_);
v_i_1015_ = v___x_1047_;
v_b_1016_ = v___x_1045_;
goto _start;
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1032_);
lean_del_object(v___x_1024_);
lean_dec(v_snd_1022_);
v_a_1050_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1033_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1033_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_del_object(v___x_1024_);
lean_dec(v_snd_1022_);
v_a_1058_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1031_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1031_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1013_ = stack[0].m_obj;
size_t v_sz_1014_ = stack[1].m_num;
size_t v_i_1015_ = stack[2].m_num;
lean_object* v_b_1016_ = stack[3].m_obj;
lean_object* v___y_1017_ = stack[4].m_obj;
lean_object* v___y_1018_ = stack[5].m_obj;
lean_object* v_res_1068_;
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1013_, v_sz_1014_, v_i_1015_, v_b_1016_, v___y_1017_, v___y_1018_);
stack->m_obj
 = v_res_1068_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1069_, lean_object* v_sz_1070_, lean_object* v_i_1071_, lean_object* v_b_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
size_t v_sz_boxed_1076_; size_t v_i_boxed_1077_; lean_object* v_res_1078_; 
v_sz_boxed_1076_ = lean_unbox_usize(v_sz_1070_);
lean_dec(v_sz_1070_);
v_i_boxed_1077_ = lean_unbox_usize(v_i_1071_);
lean_dec(v_i_1071_);
v_res_1078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1069_, v_sz_boxed_1076_, v_i_boxed_1077_, v_b_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec_ref(v_as_1069_);
return v_res_1078_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(lean_object* v_as_1079_, size_t v_sz_1080_, size_t v_i_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
uint8_t v___x_1088_; 
v___x_1088_ = lean_usize_dec_lt(v_i_1081_, v_sz_1080_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_b_1082_);
return v___x_1089_;
}
else
{
lean_object* v_snd_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1134_; 
v_snd_1090_ = lean_ctor_get(v_b_1082_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_b_1082_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v_b_1082_, 0);
lean_dec(v_unused_1135_);
v___x_1092_ = v_b_1082_;
v_isShared_1093_ = v_isSharedCheck_1134_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_snd_1090_);
lean_dec(v_b_1082_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1134_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_a_1094_; lean_object* v_keys_1095_; lean_object* v_origin_1096_; lean_object* v_data_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1094_ = lean_array_uget_borrowed(v_as_1079_, v_i_1081_);
v_keys_1095_ = lean_ctor_get(v_a_1094_, 0);
v_origin_1096_ = lean_ctor_get(v_a_1094_, 4);
v_data_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1098_ = lean_box(0);
lean_inc_ref(v_origin_1096_);
v___x_1099_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_1096_, v___y_1086_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
lean_inc_ref(v_keys_1095_);
v___x_1101_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1095_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1103_; double v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1104_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1106_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1098_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
lean_ctor_set_float(v___x_1106_, sizeof(void*)*3, v___x_1104_);
lean_ctor_set_float(v___x_1106_, sizeof(void*)*3 + 8, v___x_1104_);
lean_ctor_set_uint8(v___x_1106_, sizeof(void*)*3 + 16, v___x_1088_);
v___x_1107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_a_1100_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_a_1102_);
v___x_1110_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1106_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
lean_ctor_set(v___x_1110_, 2, v_data_1097_);
v___x_1111_ = lean_array_push(v_snd_1090_, v___x_1110_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v___x_1111_);
lean_ctor_set(v___x_1092_, 0, v___x_1098_);
v___x_1113_ = v___x_1092_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_add(v_i_1081_, v___x_1114_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1079_, v_sz_1080_, v___x_1115_, v___x_1113_, v___y_1085_, v___y_1086_);
return v___x_1116_;
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1100_);
lean_del_object(v___x_1092_);
lean_dec(v_snd_1090_);
v_a_1118_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1101_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1101_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_del_object(v___x_1092_);
lean_dec(v_snd_1090_);
v_a_1126_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1099_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1099_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1079_ = stack[0].m_obj;
size_t v_sz_1080_ = stack[1].m_num;
size_t v_i_1081_ = stack[2].m_num;
lean_object* v_b_1082_ = stack[3].m_obj;
lean_object* v___y_1083_ = stack[4].m_obj;
lean_object* v___y_1084_ = stack[5].m_obj;
lean_object* v___y_1085_ = stack[6].m_obj;
lean_object* v___y_1086_ = stack[7].m_obj;
lean_object* v_res_1136_;
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_as_1079_, v_sz_1080_, v_i_1081_, v_b_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
stack->m_obj
 = v_res_1136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1___boxed(lean_object* v_as_1137_, lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_as_1137_, v_sz_boxed_1146_, v_i_boxed_1147_, v_b_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_as_1137_);
return v_res_1148_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(lean_object* v_t_1149_, lean_object* v_init_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_root_1156_; lean_object* v_tail_1157_; lean_object* v___x_1158_; 
v_root_1156_ = lean_ctor_get(v_t_1149_, 0);
v_tail_1157_ = lean_ctor_get(v_t_1149_, 1);
lean_inc_ref(v_init_1150_);
v___x_1158_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_1150_, v_root_1156_, v_init_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec_ref(v_init_1150_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1195_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1195_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1195_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
if (lean_obj_tag(v_a_1159_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; 
v_a_1163_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v_a_1159_, 1);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v_a_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; size_t v_sz_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
lean_del_object(v___x_1161_);
v_a_1167_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v_a_1159_, 1);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v_a_1167_);
v_sz_1170_ = lean_array_size(v_tail_1157_);
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_tail_1157_, v_sz_1170_, v___x_1171_, v___x_1169_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1186_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1186_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1186_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_fst_1177_; 
v_fst_1177_ = lean_ctor_get(v_a_1173_, 0);
if (lean_obj_tag(v_fst_1177_) == 0)
{
lean_object* v_snd_1178_; lean_object* v___x_1180_; 
v_snd_1178_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1178_);
lean_dec(v_a_1173_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v_snd_1178_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_snd_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
else
{
lean_object* v_val_1182_; lean_object* v___x_1184_; 
lean_inc_ref(v_fst_1177_);
lean_dec(v_a_1173_);
v_val_1182_ = lean_ctor_get(v_fst_1177_, 0);
lean_inc(v_val_1182_);
lean_dec_ref_known(v_fst_1177_, 1);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v_val_1182_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_val_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1187_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1172_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1172_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_a_1196_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1158_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1158_);
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
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1149_ = stack[0].m_obj;
lean_object* v_init_1150_ = stack[1].m_obj;
lean_object* v___y_1151_ = stack[2].m_obj;
lean_object* v___y_1152_ = stack[3].m_obj;
lean_object* v___y_1153_ = stack[4].m_obj;
lean_object* v___y_1154_ = stack[5].m_obj;
lean_object* v_res_1204_;
v_res_1204_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_t_1149_, v_init_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0___boxed(lean_object* v_t_1205_, lean_object* v_init_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_t_1205_, v_init_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v_t_1205_);
return v_res_1212_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(lean_object* v_thms_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = l_Lean_PersistentArray_isEmpty___redArg(v_thms_1213_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v_data_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v_data_1221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1222_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_thms_1213_, v_data_1221_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1231_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1223_);
lean_ctor_set(v___x_1227_, 1, v___x_1220_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v_a_1232_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1222_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1222_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3));
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_0interp(lean_interpreter_value* stack)
{
lean_object* v_thms_1213_ = stack[0].m_obj;
lean_object* v_a_1214_ = stack[1].m_obj;
lean_object* v_a_1215_ = stack[2].m_obj;
lean_object* v_a_1216_ = stack[3].m_obj;
lean_object* v_a_1217_ = stack[4].m_obj;
lean_object* v_res_1242_;
v_res_1242_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thms_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
stack->m_obj
 = v_res_1242_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary___boxed(lean_object* v_thms_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thms_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_thms_1243_);
return v_res_1249_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(lean_object* v_as_1250_, size_t v_sz_1251_, size_t v_i_1252_, lean_object* v_b_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1250_, v_sz_1251_, v_i_1252_, v_b_1253_, v___y_1256_, v___y_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1250_ = stack[0].m_obj;
size_t v_sz_1251_ = stack[1].m_num;
size_t v_i_1252_ = stack[2].m_num;
lean_object* v_b_1253_ = stack[3].m_obj;
lean_object* v___y_1254_ = stack[4].m_obj;
lean_object* v___y_1255_ = stack[5].m_obj;
lean_object* v___y_1256_ = stack[6].m_obj;
lean_object* v___y_1257_ = stack[7].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(v_as_1250_, v_sz_1251_, v_i_1252_, v_b_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1261_, lean_object* v_sz_1262_, lean_object* v_i_1263_, lean_object* v_b_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
size_t v_sz_boxed_1270_; size_t v_i_boxed_1271_; lean_object* v_res_1272_; 
v_sz_boxed_1270_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1271_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(v_as_1261_, v_sz_boxed_1270_, v_i_boxed_1271_, v_b_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec_ref(v_as_1261_);
return v_res_1272_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1273_, size_t v_sz_1274_, size_t v_i_1275_, lean_object* v_b_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_1273_, v_sz_1274_, v_i_1275_, v_b_1276_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1273_ = stack[0].m_obj;
size_t v_sz_1274_ = stack[1].m_num;
size_t v_i_1275_ = stack[2].m_num;
lean_object* v_b_1276_ = stack[3].m_obj;
lean_object* v___y_1277_ = stack[4].m_obj;
lean_object* v___y_1278_ = stack[5].m_obj;
lean_object* v___y_1279_ = stack[6].m_obj;
lean_object* v___y_1280_ = stack[7].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(v_as_1273_, v_sz_1274_, v_i_1275_, v_b_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1284_, lean_object* v_sz_1285_, lean_object* v_i_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
size_t v_sz_boxed_1293_; size_t v_i_boxed_1294_; lean_object* v_res_1295_; 
v_sz_boxed_1293_ = lean_unbox_usize(v_sz_1285_);
lean_dec(v_sz_1285_);
v_i_boxed_1294_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(v_as_1284_, v_sz_boxed_1293_, v_i_boxed_1294_, v_b_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v_as_1284_);
return v_res_1295_;
}
}
uint8_t l_Lean_Meta_Simp_mkDiagMessages___lam__0(lean_object* v_x_1296_){
_start:
{
uint8_t v___x_1297_; 
v___x_1297_ = 1;
return v___x_1297_;
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_mkDiagMessages___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1296_ = stack[0].m_obj;
uint8_t v_res_1298_;
v_res_1298_ = l_Lean_Meta_Simp_mkDiagMessages___lam__0(v_x_1296_);
stack->m_num = v_res_1298_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___lam__0___boxed(lean_object* v_x_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Lean_Meta_Simp_mkDiagMessages___lam__0(v_x_1299_);
lean_dec(v_x_1299_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__6));
v___x_1311_ = l_Lean_MessageData_ofFormat(v___x_1310_);
return v___x_1311_;
}
}
lean_object* l_Lean_Meta_Simp_mkDiagMessages(lean_object* v_diag_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_usedThmCounter_1318_; lean_object* v_triedThmCounter_1319_; lean_object* v_congrThmCounter_1320_; lean_object* v_thmsWithBadKeys_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_usedThmCounter_1318_ = lean_ctor_get(v_diag_1312_, 0);
v_triedThmCounter_1319_ = lean_ctor_get(v_diag_1312_, 1);
v_congrThmCounter_1320_ = lean_ctor_get(v_diag_1312_, 2);
v_thmsWithBadKeys_1321_ = lean_ctor_get(v_diag_1312_, 3);
v___f_1322_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__0));
v___x_1323_ = lean_box(0);
v___x_1324_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_usedThmCounter_1318_, v___x_1323_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
lean_inc_ref(v_usedThmCounter_1318_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v_usedThmCounter_1318_);
v___x_1327_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_triedThmCounter_1319_, v___x_1326_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec_ref_known(v___x_1326_, 1);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1330_ = l_Lean_Meta_mkDiagSummary(v___x_1329_, v_congrThmCounter_1320_, v___f_1322_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1376_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1376_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1376_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thmsWithBadKeys_1321_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1367_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1367_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1367_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___y_1341_; uint8_t v___y_1358_; uint8_t v___x_1365_; 
v___x_1365_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1325_);
if (v___x_1365_ == 0)
{
v___y_1358_ = v___x_1365_;
goto v___jp_1357_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1328_);
v___y_1358_ = v___x_1366_;
goto v___jp_1357_;
}
v___jp_1340_:
{
uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1342_ = 1;
v___x_1343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__1));
v___x_1345_ = l_Lean_Meta_appendSection(v___x_1343_, v___x_1329_, v___x_1344_, v_a_1325_, v___x_1342_);
v___x_1346_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__2));
v___x_1347_ = l_Lean_Meta_appendSection(v___x_1345_, v___x_1329_, v___x_1346_, v_a_1328_, v___x_1342_);
v___x_1348_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__3));
v___x_1349_ = l_Lean_Meta_appendSection(v___x_1347_, v___x_1329_, v___x_1348_, v_a_1331_, v___x_1342_);
v___x_1350_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__4));
v___x_1351_ = l_Lean_Meta_appendSection(v___x_1349_, v___x_1329_, v___x_1350_, v_a_1336_, v___y_1341_);
v___x_1352_ = lean_obj_once(&l_Lean_Meta_Simp_mkDiagMessages___closed__7, &l_Lean_Meta_Simp_mkDiagMessages___closed__7_once, _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7);
v___x_1353_ = lean_array_push(v___x_1351_, v___x_1352_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1353_);
v___x_1355_ = v___x_1338_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
v___jp_1357_:
{
if (v___y_1358_ == 0)
{
lean_del_object(v___x_1333_);
v___y_1341_ = v___y_1358_;
goto v___jp_1340_;
}
else
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1331_);
if (v___x_1359_ == 0)
{
lean_del_object(v___x_1333_);
v___y_1341_ = v___x_1359_;
goto v___jp_1340_;
}
else
{
uint8_t v___x_1360_; 
v___x_1360_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1336_);
if (v___x_1360_ == 0)
{
lean_del_object(v___x_1333_);
v___y_1341_ = v___x_1360_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_del_object(v___x_1338_);
lean_dec(v_a_1336_);
lean_dec(v_a_1331_);
lean_dec(v_a_1328_);
lean_dec(v_a_1325_);
v___x_1361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1361_);
v___x_1363_ = v___x_1333_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1333_);
lean_dec(v_a_1331_);
lean_dec(v_a_1328_);
lean_dec(v_a_1325_);
v_a_1368_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1335_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1335_);
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
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_a_1328_);
lean_dec(v_a_1325_);
v_a_1377_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1330_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1330_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_a_1325_);
v_a_1385_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1327_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1327_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1324_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1324_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_mkDiagMessages_0interp(lean_interpreter_value* stack)
{
lean_object* v_diag_1312_ = stack[0].m_obj;
lean_object* v_a_1313_ = stack[1].m_obj;
lean_object* v_a_1314_ = stack[2].m_obj;
lean_object* v_a_1315_ = stack[3].m_obj;
lean_object* v_a_1316_ = stack[4].m_obj;
lean_object* v_res_1401_;
v_res_1401_ = l_Lean_Meta_Simp_mkDiagMessages(v_diag_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
stack->m_obj
 = v_res_1401_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___boxed(lean_object* v_diag_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Meta_Simp_mkDiagMessages(v_diag_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec_ref(v_diag_1402_);
return v_res_1408_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1417_, uint8_t v___y_1418_, lean_object* v_x_1419_){
_start:
{
if (lean_obj_tag(v_x_1419_) == 1)
{
lean_object* v_pre_1420_; 
v_pre_1420_ = lean_ctor_get(v_x_1419_, 0);
switch(lean_obj_tag(v_pre_1420_))
{
case 1:
{
lean_object* v_pre_1421_; 
v_pre_1421_ = lean_ctor_get(v_pre_1420_, 0);
switch(lean_obj_tag(v_pre_1421_))
{
case 0:
{
lean_object* v_str_1422_; lean_object* v_str_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_str_1422_ = lean_ctor_get(v_x_1419_, 1);
v_str_1423_ = lean_ctor_get(v_pre_1420_, 1);
v___x_1424_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1425_ = lean_string_dec_eq(v_str_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1427_ = lean_string_dec_eq(v_str_1423_, v___x_1426_);
if (v___x_1427_ == 0)
{
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1429_ = lean_string_dec_eq(v_str_1422_, v___x_1428_);
if (v___x_1429_ == 0)
{
return v___x_1429_;
}
else
{
return v_suppressElabErrors_1417_;
}
}
}
else
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1431_ = lean_string_dec_eq(v_str_1422_, v___x_1430_);
if (v___x_1431_ == 0)
{
return v___x_1431_;
}
else
{
return v_suppressElabErrors_1417_;
}
}
}
case 1:
{
lean_object* v_pre_1432_; 
v_pre_1432_ = lean_ctor_get(v_pre_1421_, 0);
if (lean_obj_tag(v_pre_1432_) == 0)
{
lean_object* v_str_1433_; lean_object* v_str_1434_; lean_object* v_str_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_str_1433_ = lean_ctor_get(v_x_1419_, 1);
v_str_1434_ = lean_ctor_get(v_pre_1420_, 1);
v_str_1435_ = lean_ctor_get(v_pre_1421_, 1);
v___x_1436_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1437_ = lean_string_dec_eq(v_str_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1439_ = lean_string_dec_eq(v_str_1434_, v___x_1438_);
if (v___x_1439_ == 0)
{
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_1441_ = lean_string_dec_eq(v_str_1433_, v___x_1440_);
if (v___x_1441_ == 0)
{
return v___x_1441_;
}
else
{
return v_suppressElabErrors_1417_;
}
}
}
}
else
{
return v___y_1418_;
}
}
default: 
{
return v___y_1418_;
}
}
}
case 0:
{
lean_object* v_str_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_str_1442_ = lean_ctor_get(v_x_1419_, 1);
v___x_1443_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_1444_ = lean_string_dec_eq(v_str_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
return v___x_1444_;
}
else
{
return v_suppressElabErrors_1417_;
}
}
default: 
{
return v___y_1418_;
}
}
}
else
{
return v___y_1418_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1417_ = stack[0].m_num;
uint8_t v___y_1418_ = stack[1].m_num;
lean_object* v_x_1419_ = stack[2].m_obj;
uint8_t v_res_1445_;
v_res_1445_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_1417_, v___y_1418_, v_x_1419_);
stack->m_num = v_res_1445_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1446_, lean_object* v___y_1447_, lean_object* v_x_1448_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1449_; uint8_t v___y_6646__boxed_1450_; uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_suppressElabErrors_boxed_1449_ = lean_unbox(v_suppressElabErrors_1446_);
v___y_6646__boxed_1450_ = lean_unbox(v___y_1447_);
v_res_1451_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1449_, v___y_6646__boxed_1450_, v_x_1448_);
lean_dec(v_x_1448_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_1453_, lean_object* v_opt_1454_){
_start:
{
lean_object* v_name_1455_; lean_object* v_defValue_1456_; lean_object* v_map_1457_; lean_object* v___x_1458_; 
v_name_1455_ = lean_ctor_get(v_opt_1454_, 0);
v_defValue_1456_ = lean_ctor_get(v_opt_1454_, 1);
v_map_1457_ = lean_ctor_get(v_opts_1453_, 0);
v___x_1458_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1457_, v_name_1455_);
if (lean_obj_tag(v___x_1458_) == 0)
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_unbox(v_defValue_1456_);
return v___x_1459_;
}
else
{
lean_object* v_val_1460_; 
v_val_1460_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v___x_1458_, 1);
if (lean_obj_tag(v_val_1460_) == 1)
{
uint8_t v_v_1461_; 
v_v_1461_ = lean_ctor_get_uint8(v_val_1460_, 0);
lean_dec_ref_known(v_val_1460_, 0);
return v_v_1461_;
}
else
{
uint8_t v___x_1462_; 
lean_dec(v_val_1460_);
v___x_1462_ = lean_unbox(v_defValue_1456_);
return v___x_1462_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1453_ = stack[0].m_obj;
lean_object* v_opt_1454_ = stack[1].m_obj;
uint8_t v_res_1463_;
v_res_1463_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_opts_1453_, v_opt_1454_);
stack->m_num = v_res_1463_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_1464_, lean_object* v_opt_1465_){
_start:
{
uint8_t v_res_1466_; lean_object* v_r_1467_; 
v_res_1466_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_opts_1464_, v_opt_1465_);
lean_dec_ref(v_opt_1465_);
lean_dec_ref(v_opts_1464_);
v_r_1467_ = lean_box(v_res_1466_);
return v_r_1467_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v_env_1475_; uint8_t v___x_1476_; lean_object* v_env_1477_; lean_object* v___x_1478_; lean_object* v_toCold_1479_; lean_object* v_mctx_1480_; lean_object* v_lctx_1481_; lean_object* v_options_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1474_ = lean_st_ref_get(v___y_1472_);
v_env_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc_ref(v_env_1475_);
lean_dec(v___x_1474_);
v___x_1476_ = 0;
v_env_1477_ = l_Lean_Environment_setRecordingDeps(v_env_1475_, v___x_1476_);
v___x_1478_ = lean_st_ref_get(v___y_1470_);
v_toCold_1479_ = lean_ctor_get(v___y_1471_, 0);
v_mctx_1480_ = lean_ctor_get(v___x_1478_, 0);
lean_inc_ref(v_mctx_1480_);
lean_dec(v___x_1478_);
v_lctx_1481_ = lean_ctor_get(v___y_1469_, 2);
v_options_1482_ = lean_ctor_get(v_toCold_1479_, 2);
lean_inc_ref(v_options_1482_);
lean_inc_ref(v_lctx_1481_);
v___x_1483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1483_, 0, v_env_1477_);
lean_ctor_set(v___x_1483_, 1, v_mctx_1480_);
lean_ctor_set(v___x_1483_, 2, v_lctx_1481_);
lean_ctor_set(v___x_1483_, 3, v_options_1482_);
v___x_1484_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v_msgData_1468_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1468_ = stack[0].m_obj;
lean_object* v___y_1469_ = stack[1].m_obj;
lean_object* v___y_1470_ = stack[2].m_obj;
lean_object* v___y_1471_ = stack[3].m_obj;
lean_object* v___y_1472_ = stack[4].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v_msgData_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v_msgData_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(lean_object* v_ref_1494_, lean_object* v_msgData_1495_, uint8_t v_severity_1496_, uint8_t v_isSilent_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; uint8_t v___y_1509_; lean_object* v___y_1510_; lean_object* v_toCold_1511_; lean_object* v___y_1512_; lean_object* v___y_1541_; lean_object* v___y_1542_; uint8_t v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v___y_1546_; uint8_t v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1568_; lean_object* v___y_1569_; uint8_t v___y_1570_; uint8_t v___y_1571_; uint8_t v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; uint8_t v___y_1578_; uint8_t v___y_1579_; uint8_t v___y_1580_; uint8_t v___x_1591_; uint8_t v___y_1593_; uint8_t v___y_1594_; uint8_t v___y_1595_; uint8_t v___y_1597_; uint8_t v___x_1605_; 
v___x_1591_ = 2;
v___x_1605_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1496_, v___x_1591_);
if (v___x_1605_ == 0)
{
v___y_1597_ = v___x_1605_;
goto v___jp_1596_;
}
else
{
uint8_t v___x_1606_; 
lean_inc_ref(v_msgData_1495_);
v___x_1606_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1495_);
v___y_1597_ = v___x_1606_;
goto v___jp_1596_;
}
v___jp_1503_:
{
lean_object* v_currNamespace_1513_; lean_object* v_openDecls_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_env_1519_; lean_object* v_nextMacroScope_1520_; lean_object* v_ngen_1521_; lean_object* v_auxDeclNGen_1522_; lean_object* v_traceState_1523_; lean_object* v_cache_1524_; lean_object* v_recordedDeps_1525_; lean_object* v_messages_1526_; lean_object* v_infoState_1527_; lean_object* v_snapshotTasks_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1539_; 
v_currNamespace_1513_ = lean_ctor_get(v_toCold_1511_, 4);
v_openDecls_1514_ = lean_ctor_get(v_toCold_1511_, 5);
lean_inc(v_openDecls_1514_);
lean_inc(v_currNamespace_1513_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_currNamespace_1513_);
lean_ctor_set(v___x_1515_, 1, v_openDecls_1514_);
v___x_1516_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc_ref(v___y_1507_);
v___x_1517_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1517_, 0, v___y_1507_);
lean_ctor_set(v___x_1517_, 1, v___y_1508_);
lean_ctor_set(v___x_1517_, 2, v___y_1510_);
lean_ctor_set(v___x_1517_, 3, v___y_1505_);
lean_ctor_set(v___x_1517_, 4, v___x_1516_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*5, v___y_1504_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*5 + 1, v___y_1509_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*5 + 2, v_isSilent_1497_);
v___x_1518_ = lean_st_ref_take(v___y_1512_);
v_env_1519_ = lean_ctor_get(v___x_1518_, 0);
v_nextMacroScope_1520_ = lean_ctor_get(v___x_1518_, 1);
v_ngen_1521_ = lean_ctor_get(v___x_1518_, 2);
v_auxDeclNGen_1522_ = lean_ctor_get(v___x_1518_, 3);
v_traceState_1523_ = lean_ctor_get(v___x_1518_, 4);
v_cache_1524_ = lean_ctor_get(v___x_1518_, 5);
v_recordedDeps_1525_ = lean_ctor_get(v___x_1518_, 6);
v_messages_1526_ = lean_ctor_get(v___x_1518_, 7);
v_infoState_1527_ = lean_ctor_get(v___x_1518_, 8);
v_snapshotTasks_1528_ = lean_ctor_get(v___x_1518_, 9);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1530_ = v___x_1518_;
v_isShared_1531_ = v_isSharedCheck_1539_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snapshotTasks_1528_);
lean_inc(v_infoState_1527_);
lean_inc(v_messages_1526_);
lean_inc(v_recordedDeps_1525_);
lean_inc(v_cache_1524_);
lean_inc(v_traceState_1523_);
lean_inc(v_auxDeclNGen_1522_);
lean_inc(v_ngen_1521_);
lean_inc(v_nextMacroScope_1520_);
lean_inc(v_env_1519_);
lean_dec(v___x_1518_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1539_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = l_Lean_MessageLog_add(v___x_1517_, v_messages_1526_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 7, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_env_1519_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_nextMacroScope_1520_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_ngen_1521_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_auxDeclNGen_1522_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_traceState_1523_);
lean_ctor_set(v_reuseFailAlloc_1538_, 5, v_cache_1524_);
lean_ctor_set(v_reuseFailAlloc_1538_, 6, v_recordedDeps_1525_);
lean_ctor_set(v_reuseFailAlloc_1538_, 7, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1538_, 8, v_infoState_1527_);
lean_ctor_set(v_reuseFailAlloc_1538_, 9, v_snapshotTasks_1528_);
v___x_1535_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_st_ref_put(v___y_1512_, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1532_);
return v___x_1537_;
}
}
}
v___jp_1540_:
{
lean_object* v_fileName_1549_; lean_object* v_fileMap_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1566_; 
v_fileName_1549_ = lean_ctor_get(v___y_1545_, 0);
v_fileMap_1550_ = lean_ctor_get(v___y_1545_, 1);
v___x_1551_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1495_);
v___x_1552_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v___x_1551_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1566_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1566_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_inc_ref_n(v_fileMap_1550_, 2);
v___x_1557_ = l_Lean_FileMap_toPosition(v_fileMap_1550_, v___y_1544_);
lean_dec(v___y_1544_);
v___x_1558_ = l_Lean_FileMap_toPosition(v_fileMap_1550_, v___y_1548_);
lean_dec(v___y_1548_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
v___x_1560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
if (v___y_1547_ == 0)
{
lean_del_object(v___x_1555_);
lean_dec_ref(v___y_1541_);
v___y_1504_ = v___y_1543_;
v___y_1505_ = v___x_1560_;
v___y_1506_ = v_a_1553_;
v___y_1507_ = v_fileName_1549_;
v___y_1508_ = v___x_1557_;
v___y_1509_ = v___y_1546_;
v___y_1510_ = v___x_1559_;
v_toCold_1511_ = v___y_1542_;
v___y_1512_ = v___y_1501_;
goto v___jp_1503_;
}
else
{
uint8_t v___x_1561_; 
lean_inc(v_a_1553_);
v___x_1561_ = l_Lean_MessageData_hasTag(v___y_1541_, v_a_1553_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
lean_dec_ref_known(v___x_1559_, 1);
lean_dec_ref(v___x_1557_);
lean_dec(v_a_1553_);
v___x_1562_ = lean_box(0);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1562_);
v___x_1564_ = v___x_1555_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
else
{
lean_del_object(v___x_1555_);
v___y_1504_ = v___y_1543_;
v___y_1505_ = v___x_1560_;
v___y_1506_ = v_a_1553_;
v___y_1507_ = v_fileName_1549_;
v___y_1508_ = v___x_1557_;
v___y_1509_ = v___y_1546_;
v___y_1510_ = v___x_1559_;
v_toCold_1511_ = v___y_1542_;
v___y_1512_ = v___y_1501_;
goto v___jp_1503_;
}
}
}
}
v___jp_1567_:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Syntax_getTailPos_x3f(v___y_1573_, v___y_1571_);
lean_dec(v___y_1573_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_inc(v___y_1574_);
v___y_1541_ = v___y_1568_;
v___y_1542_ = v___y_1569_;
v___y_1543_ = v___y_1571_;
v___y_1544_ = v___y_1574_;
v___y_1545_ = v___y_1569_;
v___y_1546_ = v___y_1572_;
v___y_1547_ = v___y_1570_;
v___y_1548_ = v___y_1574_;
goto v___jp_1540_;
}
else
{
lean_object* v_val_1576_; 
v_val_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___y_1541_ = v___y_1568_;
v___y_1542_ = v___y_1569_;
v___y_1543_ = v___y_1571_;
v___y_1544_ = v___y_1574_;
v___y_1545_ = v___y_1569_;
v___y_1546_ = v___y_1572_;
v___y_1547_ = v___y_1570_;
v___y_1548_ = v_val_1576_;
goto v___jp_1540_;
}
}
v___jp_1577_:
{
lean_object* v_toCold_1581_; lean_object* v_ref_1582_; uint8_t v_suppressElabErrors_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___f_1586_; lean_object* v_ref_1587_; lean_object* v___x_1588_; 
v_toCold_1581_ = lean_ctor_get(v___y_1500_, 0);
v_ref_1582_ = lean_ctor_get(v___y_1500_, 2);
v_suppressElabErrors_1583_ = lean_ctor_get_uint8(v___y_1500_, sizeof(void*)*3 + 2);
v___x_1584_ = lean_box(v_suppressElabErrors_1583_);
v___x_1585_ = lean_box(v___y_1578_);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1586_, 0, v___x_1584_);
lean_closure_set(v___f_1586_, 1, v___x_1585_);
v_ref_1587_ = l_Lean_replaceRef(v_ref_1494_, v_ref_1582_);
v___x_1588_ = l_Lean_Syntax_getPos_x3f(v_ref_1587_, v___y_1579_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_unsigned_to_nat(0u);
v___y_1568_ = v___f_1586_;
v___y_1569_ = v_toCold_1581_;
v___y_1570_ = v_suppressElabErrors_1583_;
v___y_1571_ = v___y_1579_;
v___y_1572_ = v___y_1580_;
v___y_1573_ = v_ref_1587_;
v___y_1574_ = v___x_1589_;
goto v___jp_1567_;
}
else
{
lean_object* v_val_1590_; 
v_val_1590_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1588_, 1);
v___y_1568_ = v___f_1586_;
v___y_1569_ = v_toCold_1581_;
v___y_1570_ = v_suppressElabErrors_1583_;
v___y_1571_ = v___y_1579_;
v___y_1572_ = v___y_1580_;
v___y_1573_ = v_ref_1587_;
v___y_1574_ = v_val_1590_;
goto v___jp_1567_;
}
}
v___jp_1592_:
{
if (v___y_1595_ == 0)
{
v___y_1578_ = v___y_1593_;
v___y_1579_ = v___y_1594_;
v___y_1580_ = v_severity_1496_;
goto v___jp_1577_;
}
else
{
v___y_1578_ = v___y_1593_;
v___y_1579_ = v___y_1594_;
v___y_1580_ = v___x_1591_;
goto v___jp_1577_;
}
}
v___jp_1596_:
{
if (v___y_1597_ == 0)
{
uint8_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = 1;
v___x_1599_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1496_, v___x_1598_);
if (v___x_1599_ == 0)
{
v___y_1593_ = v___y_1597_;
v___y_1594_ = v___y_1597_;
v___y_1595_ = v___x_1599_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1500_);
v___x_1601_ = l_Lean_warningAsError;
v___x_1602_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v___x_1600_, v___x_1601_);
lean_dec_ref(v___x_1600_);
v___y_1593_ = v___y_1597_;
v___y_1594_ = v___y_1597_;
v___y_1595_ = v___x_1602_;
goto v___jp_1592_;
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref(v_msgData_1495_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1494_ = stack[0].m_obj;
lean_object* v_msgData_1495_ = stack[1].m_obj;
uint8_t v_severity_1496_ = stack[2].m_num;
uint8_t v_isSilent_1497_ = stack[3].m_num;
lean_object* v___y_1498_ = stack[4].m_obj;
lean_object* v___y_1499_ = stack[5].m_obj;
lean_object* v___y_1500_ = stack[6].m_obj;
lean_object* v___y_1501_ = stack[7].m_obj;
lean_object* v_res_1607_;
v_res_1607_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_1494_, v_msgData_1495_, v_severity_1496_, v_isSilent_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
stack->m_obj
 = v_res_1607_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1608_, lean_object* v_msgData_1609_, lean_object* v_severity_1610_, lean_object* v_isSilent_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v_severity_boxed_1617_; uint8_t v_isSilent_boxed_1618_; lean_object* v_res_1619_; 
v_severity_boxed_1617_ = lean_unbox(v_severity_1610_);
v_isSilent_boxed_1618_ = lean_unbox(v_isSilent_1611_);
v_res_1619_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_1608_, v_msgData_1609_, v_severity_boxed_1617_, v_isSilent_boxed_1618_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v_ref_1608_);
return v_res_1619_;
}
}
lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(lean_object* v_msgData_1620_, uint8_t v_severity_1621_, uint8_t v_isSilent_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_ref_1628_; lean_object* v___x_1629_; 
v_ref_1628_ = lean_ctor_get(v___y_1625_, 2);
v___x_1629_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_1628_, v_msgData_1620_, v_severity_1621_, v_isSilent_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1620_ = stack[0].m_obj;
uint8_t v_severity_1621_ = stack[1].m_num;
uint8_t v_isSilent_1622_ = stack[2].m_num;
lean_object* v___y_1623_ = stack[3].m_obj;
lean_object* v___y_1624_ = stack[4].m_obj;
lean_object* v___y_1625_ = stack[5].m_obj;
lean_object* v___y_1626_ = stack[6].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(v_msgData_1620_, v_severity_1621_, v_isSilent_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0___boxed(lean_object* v_msgData_1631_, lean_object* v_severity_1632_, lean_object* v_isSilent_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v_severity_boxed_1639_; uint8_t v_isSilent_boxed_1640_; lean_object* v_res_1641_; 
v_severity_boxed_1639_ = lean_unbox(v_severity_1632_);
v_isSilent_boxed_1640_ = lean_unbox(v_isSilent_1633_);
v_res_1641_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(v_msgData_1631_, v_severity_boxed_1639_, v_isSilent_boxed_1640_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1641_;
}
}
lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(lean_object* v_msgData_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = 0;
v___x_1649_ = 0;
v___x_1650_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(v_msgData_1642_, v___x_1648_, v___x_1649_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1650_;
}
}
LEAN_EXPORT void l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1642_ = stack[0].m_obj;
lean_object* v___y_1643_ = stack[1].m_obj;
lean_object* v___y_1644_ = stack[2].m_obj;
lean_object* v___y_1645_ = stack[3].m_obj;
lean_object* v___y_1646_ = stack[4].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(v_msgData_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0___boxed(lean_object* v_msgData_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(v_msgData_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1658_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_Meta_Simp_reportDiag___lam__0___closed__1));
v___x_1663_ = l_Lean_MessageData_ofFormat(v___x_1662_);
return v___x_1663_;
}
}
lean_object* l_Lean_Meta_Simp_reportDiag___lam__0(lean_object* v_diag_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Meta_Simp_mkDiagMessages(v_diag_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1690_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1690_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1690_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1675_ = lean_array_get_size(v_a_1671_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_nat_dec_eq(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; double v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_del_object(v___x_1673_);
v___x_1678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1682_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1682_, 0, v___x_1678_);
lean_ctor_set(v___x_1682_, 1, v___x_1679_);
lean_ctor_set(v___x_1682_, 2, v___x_1681_);
lean_ctor_set_float(v___x_1682_, sizeof(void*)*3, v___x_1680_);
lean_ctor_set_float(v___x_1682_, sizeof(void*)*3 + 8, v___x_1680_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*3 + 16, v___x_1677_);
v___x_1683_ = lean_obj_once(&l_Lean_Meta_Simp_reportDiag___lam__0___closed__2, &l_Lean_Meta_Simp_reportDiag___lam__0___closed__2_once, _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2);
v___x_1684_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
lean_ctor_set(v___x_1684_, 2, v_a_1671_);
v___x_1685_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(v___x_1684_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_dec(v_a_1671_);
v___x_1686_ = lean_box(0);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1686_);
v___x_1688_ = v___x_1673_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1670_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1670_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_reportDiag___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_diag_1664_ = stack[0].m_obj;
lean_object* v___y_1665_ = stack[1].m_obj;
lean_object* v___y_1666_ = stack[2].m_obj;
lean_object* v___y_1667_ = stack[3].m_obj;
lean_object* v___y_1668_ = stack[4].m_obj;
lean_object* v_res_1699_;
v_res_1699_ = l_Lean_Meta_Simp_reportDiag___lam__0(v_diag_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
stack->m_obj
 = v_res_1699_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___lam__0___boxed(lean_object* v_diag_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Meta_Simp_reportDiag___lam__0(v_diag_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_diag_1700_);
return v_res_1706_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(lean_object* v___y_1707_, uint8_t v_isExporting_1708_, lean_object* v___x_1709_, lean_object* v___y_1710_, lean_object* v___x_1711_, lean_object* v_a_x3f_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v_env_1715_; lean_object* v_nextMacroScope_1716_; lean_object* v_ngen_1717_; lean_object* v_auxDeclNGen_1718_; lean_object* v_traceState_1719_; lean_object* v_recordedDeps_1720_; lean_object* v_messages_1721_; lean_object* v_infoState_1722_; lean_object* v_snapshotTasks_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1748_; 
v___x_1714_ = lean_st_ref_take(v___y_1707_);
v_env_1715_ = lean_ctor_get(v___x_1714_, 0);
v_nextMacroScope_1716_ = lean_ctor_get(v___x_1714_, 1);
v_ngen_1717_ = lean_ctor_get(v___x_1714_, 2);
v_auxDeclNGen_1718_ = lean_ctor_get(v___x_1714_, 3);
v_traceState_1719_ = lean_ctor_get(v___x_1714_, 4);
v_recordedDeps_1720_ = lean_ctor_get(v___x_1714_, 6);
v_messages_1721_ = lean_ctor_get(v___x_1714_, 7);
v_infoState_1722_ = lean_ctor_get(v___x_1714_, 8);
v_snapshotTasks_1723_ = lean_ctor_get(v___x_1714_, 9);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v___x_1714_, 5);
lean_dec(v_unused_1749_);
v___x_1725_ = v___x_1714_;
v_isShared_1726_ = v_isSharedCheck_1748_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_snapshotTasks_1723_);
lean_inc(v_infoState_1722_);
lean_inc(v_messages_1721_);
lean_inc(v_recordedDeps_1720_);
lean_inc(v_traceState_1719_);
lean_inc(v_auxDeclNGen_1718_);
lean_inc(v_ngen_1717_);
lean_inc(v_nextMacroScope_1716_);
lean_inc(v_env_1715_);
lean_dec(v___x_1714_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1748_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_Environment_setExporting(v_env_1715_, v_isExporting_1708_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 5, v___x_1709_);
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_nextMacroScope_1716_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_ngen_1717_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v_auxDeclNGen_1718_);
lean_ctor_set(v_reuseFailAlloc_1747_, 4, v_traceState_1719_);
lean_ctor_set(v_reuseFailAlloc_1747_, 5, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1747_, 6, v_recordedDeps_1720_);
lean_ctor_set(v_reuseFailAlloc_1747_, 7, v_messages_1721_);
lean_ctor_set(v_reuseFailAlloc_1747_, 8, v_infoState_1722_);
lean_ctor_set(v_reuseFailAlloc_1747_, 9, v_snapshotTasks_1723_);
v___x_1729_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_mctx_1732_; lean_object* v_zetaDeltaFVarIds_1733_; lean_object* v_postponed_1734_; lean_object* v_diag_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1745_; 
v___x_1730_ = lean_st_ref_put(v___y_1707_, v___x_1729_);
v___x_1731_ = lean_st_ref_take(v___y_1710_);
v_mctx_1732_ = lean_ctor_get(v___x_1731_, 0);
v_zetaDeltaFVarIds_1733_ = lean_ctor_get(v___x_1731_, 2);
v_postponed_1734_ = lean_ctor_get(v___x_1731_, 3);
v_diag_1735_ = lean_ctor_get(v___x_1731_, 4);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v___x_1731_, 1);
lean_dec(v_unused_1746_);
v___x_1737_ = v___x_1731_;
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_diag_1735_);
lean_inc(v_postponed_1734_);
lean_inc(v_zetaDeltaFVarIds_1733_);
lean_inc(v_mctx_1732_);
lean_dec(v___x_1731_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_box(0);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v___x_1711_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_mctx_1732_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_zetaDeltaFVarIds_1733_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_postponed_1734_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v_diag_1735_);
v___x_1741_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_st_ref_put(v___y_1710_, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1739_);
return v___x_1743_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1707_ = stack[0].m_obj;
uint8_t v_isExporting_1708_ = stack[1].m_num;
lean_object* v___x_1709_ = stack[2].m_obj;
lean_object* v___y_1710_ = stack[3].m_obj;
lean_object* v___x_1711_ = stack[4].m_obj;
lean_object* v_a_x3f_1712_ = stack[5].m_obj;
lean_object* v_res_1750_;
v_res_1750_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1707_, v_isExporting_1708_, v___x_1709_, v___y_1710_, v___x_1711_, v_a_x3f_1712_);
stack->m_obj
 = v_res_1750_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_1751_, lean_object* v_isExporting_1752_, lean_object* v___x_1753_, lean_object* v___y_1754_, lean_object* v___x_1755_, lean_object* v_a_x3f_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v_isExporting_boxed_1758_; lean_object* v_res_1759_; 
v_isExporting_boxed_1758_ = lean_unbox(v_isExporting_1752_);
v_res_1759_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1751_, v_isExporting_boxed_1758_, v___x_1753_, v___y_1754_, v___x_1755_, v_a_x3f_1756_);
lean_dec(v_a_x3f_1756_);
lean_dec(v___y_1754_);
lean_dec(v___y_1751_);
return v_res_1759_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
v___x_1766_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
lean_ctor_set(v___x_1766_, 2, v___x_1765_);
lean_ctor_set(v___x_1766_, 3, v___x_1765_);
lean_ctor_set(v___x_1766_, 4, v___x_1765_);
lean_ctor_set(v___x_1766_, 5, v___x_1765_);
return v___x_1766_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(lean_object* v_x_1767_, uint8_t v_isExporting_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; lean_object* v_env_1775_; lean_object* v___x_1776_; uint8_t v_isModule_1777_; 
v___x_1774_ = lean_st_ref_get(v___y_1772_);
v_env_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_ref(v_env_1775_);
lean_dec(v___x_1774_);
v___x_1776_ = l_Lean_Environment_header(v_env_1775_);
v_isModule_1777_ = lean_ctor_get_uint8(v___x_1776_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1776_);
if (v_isModule_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref(v_env_1775_);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
v___x_1778_ = lean_apply_5(v_x_1767_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, lean_box(0));
return v___x_1778_;
}
else
{
uint8_t v_isExporting_1779_; 
v_isExporting_1779_ = lean_ctor_get_uint8(v_env_1775_, sizeof(void*)*13);
lean_dec_ref(v_env_1775_);
if (v_isExporting_1768_ == 0)
{
if (v_isExporting_1779_ == 0)
{
lean_object* v___x_1846_; 
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
v___x_1846_ = lean_apply_5(v_x_1767_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, lean_box(0));
return v___x_1846_;
}
else
{
goto v___jp_1780_;
}
}
else
{
if (v_isExporting_1779_ == 0)
{
goto v___jp_1780_;
}
else
{
lean_object* v___x_1847_; 
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
v___x_1847_ = lean_apply_5(v_x_1767_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, lean_box(0));
return v___x_1847_;
}
}
v___jp_1780_:
{
lean_object* v___x_1781_; lean_object* v_env_1782_; lean_object* v_nextMacroScope_1783_; lean_object* v_ngen_1784_; lean_object* v_auxDeclNGen_1785_; lean_object* v_traceState_1786_; lean_object* v_recordedDeps_1787_; lean_object* v_messages_1788_; lean_object* v_infoState_1789_; lean_object* v_snapshotTasks_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1844_; 
v___x_1781_ = lean_st_ref_take(v___y_1772_);
v_env_1782_ = lean_ctor_get(v___x_1781_, 0);
v_nextMacroScope_1783_ = lean_ctor_get(v___x_1781_, 1);
v_ngen_1784_ = lean_ctor_get(v___x_1781_, 2);
v_auxDeclNGen_1785_ = lean_ctor_get(v___x_1781_, 3);
v_traceState_1786_ = lean_ctor_get(v___x_1781_, 4);
v_recordedDeps_1787_ = lean_ctor_get(v___x_1781_, 6);
v_messages_1788_ = lean_ctor_get(v___x_1781_, 7);
v_infoState_1789_ = lean_ctor_get(v___x_1781_, 8);
v_snapshotTasks_1790_ = lean_ctor_get(v___x_1781_, 9);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; 
v_unused_1845_ = lean_ctor_get(v___x_1781_, 5);
lean_dec(v_unused_1845_);
v___x_1792_ = v___x_1781_;
v_isShared_1793_ = v_isSharedCheck_1844_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_snapshotTasks_1790_);
lean_inc(v_infoState_1789_);
lean_inc(v_messages_1788_);
lean_inc(v_recordedDeps_1787_);
lean_inc(v_traceState_1786_);
lean_inc(v_auxDeclNGen_1785_);
lean_inc(v_ngen_1784_);
lean_inc(v_nextMacroScope_1783_);
lean_inc(v_env_1782_);
lean_dec(v___x_1781_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1844_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1794_ = l_Lean_Environment_setExporting(v_env_1782_, v_isExporting_1768_);
v___x_1795_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 5, v___x_1795_);
lean_ctor_set(v___x_1792_, 0, v___x_1794_);
v___x_1797_ = v___x_1792_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_nextMacroScope_1783_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_ngen_1784_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_auxDeclNGen_1785_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_traceState_1786_);
lean_ctor_set(v_reuseFailAlloc_1843_, 5, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1843_, 6, v_recordedDeps_1787_);
lean_ctor_set(v_reuseFailAlloc_1843_, 7, v_messages_1788_);
lean_ctor_set(v_reuseFailAlloc_1843_, 8, v_infoState_1789_);
lean_ctor_set(v_reuseFailAlloc_1843_, 9, v_snapshotTasks_1790_);
v___x_1797_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_mctx_1800_; lean_object* v_zetaDeltaFVarIds_1801_; lean_object* v_postponed_1802_; lean_object* v_diag_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1841_; 
v___x_1798_ = lean_st_ref_put(v___y_1772_, v___x_1797_);
v___x_1799_ = lean_st_ref_take(v___y_1770_);
v_mctx_1800_ = lean_ctor_get(v___x_1799_, 0);
v_zetaDeltaFVarIds_1801_ = lean_ctor_get(v___x_1799_, 2);
v_postponed_1802_ = lean_ctor_get(v___x_1799_, 3);
v_diag_1803_ = lean_ctor_get(v___x_1799_, 4);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v___x_1799_, 1);
lean_dec(v_unused_1842_);
v___x_1805_ = v___x_1799_;
v_isShared_1806_ = v_isSharedCheck_1841_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_diag_1803_);
lean_inc(v_postponed_1802_);
lean_inc(v_zetaDeltaFVarIds_1801_);
lean_inc(v_mctx_1800_);
lean_dec(v___x_1799_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1841_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1807_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_mctx_1800_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_zetaDeltaFVarIds_1801_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v_postponed_1802_);
lean_ctor_set(v_reuseFailAlloc_1840_, 4, v_diag_1803_);
v___x_1809_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; lean_object* v_r_1811_; 
v___x_1810_ = lean_st_ref_put(v___y_1770_, v___x_1809_);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
v_r_1811_ = lean_apply_5(v_x_1767_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, lean_box(0));
if (lean_obj_tag(v_r_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1828_; 
v_a_1812_ = lean_ctor_get(v_r_1811_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_r_1811_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1814_ = v_r_1811_;
v_isShared_1815_ = v_isSharedCheck_1828_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v_r_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1828_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
lean_inc(v_a_1812_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v___x_1818_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1772_, v_isExporting_1779_, v___x_1795_, v___y_1770_, v___x_1807_, v___x_1817_);
lean_dec_ref(v___x_1817_);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1826_);
v___x_1820_ = v___x_1818_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1818_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v_a_1812_);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1812_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
v_a_1829_ = lean_ctor_get(v_r_1811_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v_r_1811_, 1);
v___x_1830_ = lean_box(0);
v___x_1831_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1772_, v_isExporting_1779_, v___x_1795_, v___y_1770_, v___x_1807_, v___x_1830_);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v___x_1831_, 0);
lean_dec(v_unused_1839_);
v___x_1833_ = v___x_1831_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_dec(v___x_1831_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 1);
lean_ctor_set(v___x_1833_, 0, v_a_1829_);
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1829_);
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
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1767_ = stack[0].m_obj;
uint8_t v_isExporting_1768_ = stack[1].m_num;
lean_object* v___y_1769_ = stack[2].m_obj;
lean_object* v___y_1770_ = stack[3].m_obj;
lean_object* v___y_1771_ = stack[4].m_obj;
lean_object* v___y_1772_ = stack[5].m_obj;
lean_object* v_res_1848_;
v_res_1848_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1767_, v_isExporting_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
stack->m_obj
 = v_res_1848_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___boxed(lean_object* v_x_1849_, lean_object* v_isExporting_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
uint8_t v_isExporting_boxed_1856_; lean_object* v_res_1857_; 
v_isExporting_boxed_1856_ = lean_unbox(v_isExporting_1850_);
v_res_1857_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1849_, v_isExporting_boxed_1856_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1857_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(lean_object* v_x_1858_, uint8_t v_when_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
if (v_when_1859_ == 0)
{
lean_object* v___x_1865_; 
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc_ref(v___y_1860_);
v___x_1865_ = lean_apply_5(v_x_1858_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, lean_box(0));
return v___x_1865_;
}
else
{
uint8_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = 0;
v___x_1867_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1858_, v___x_1866_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1867_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1858_ = stack[0].m_obj;
uint8_t v_when_1859_ = stack[1].m_num;
lean_object* v___y_1860_ = stack[2].m_obj;
lean_object* v___y_1861_ = stack[3].m_obj;
lean_object* v___y_1862_ = stack[4].m_obj;
lean_object* v___y_1863_ = stack[5].m_obj;
lean_object* v_res_1868_;
v_res_1868_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v_x_1858_, v_when_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
stack->m_obj
 = v_res_1868_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg___boxed(lean_object* v_x_1869_, lean_object* v_when_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
uint8_t v_when_boxed_1876_; lean_object* v_res_1877_; 
v_when_boxed_1876_ = lean_unbox(v_when_1870_);
v_res_1877_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v_x_1869_, v_when_boxed_1876_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1877_;
}
}
lean_object* l_Lean_Meta_Simp_reportDiag(lean_object* v_diag_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v___f_1884_; lean_object* v___x_1885_; 
v___f_1884_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_reportDiag___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1884_, 0, v_diag_1878_);
v___x_1885_ = l_Lean_isDiagnosticsEnabled___redArg(v_a_1881_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1897_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_unbox(v_a_1886_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
lean_dec(v_a_1886_);
lean_dec_ref(v___f_1884_);
v___x_1891_ = lean_box(0);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1891_);
v___x_1893_ = v___x_1888_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
uint8_t v___x_1895_; lean_object* v___x_1896_; 
lean_del_object(v___x_1888_);
v___x_1895_ = lean_unbox(v_a_1886_);
lean_dec(v_a_1886_);
v___x_1896_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v___f_1884_, v___x_1895_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
return v___x_1896_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref(v___f_1884_);
v_a_1898_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1885_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1885_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_reportDiag_0interp(lean_interpreter_value* stack)
{
lean_object* v_diag_1878_ = stack[0].m_obj;
lean_object* v_a_1879_ = stack[1].m_obj;
lean_object* v_a_1880_ = stack[2].m_obj;
lean_object* v_a_1881_ = stack[3].m_obj;
lean_object* v_a_1882_ = stack[4].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l_Lean_Meta_Simp_reportDiag(v_diag_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___boxed(lean_object* v_diag_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Meta_Simp_reportDiag(v_diag_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
return v_res_1913_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(lean_object* v_00_u03b1_1914_, lean_object* v_x_1915_, uint8_t v_isExporting_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1915_, v_isExporting_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1915_ = stack[1].m_obj;
uint8_t v_isExporting_1916_ = stack[2].m_num;
lean_object* v___y_1917_ = stack[3].m_obj;
lean_object* v___y_1918_ = stack[4].m_obj;
lean_object* v___y_1919_ = stack[5].m_obj;
lean_object* v___y_1920_ = stack[6].m_obj;
lean_object* v_res_1923_;
v_res_1923_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(lean_box(0), v_x_1915_, v_isExporting_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
stack->m_obj
 = v_res_1923_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_x_1925_, lean_object* v_isExporting_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
uint8_t v_isExporting_boxed_1932_; lean_object* v_res_1933_; 
v_isExporting_boxed_1932_ = lean_unbox(v_isExporting_1926_);
v_res_1933_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(v_00_u03b1_1924_, v_x_1925_, v_isExporting_boxed_1932_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1933_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(lean_object* v_00_u03b1_1934_, lean_object* v_x_1935_, uint8_t v_when_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v_x_1935_, v_when_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1935_ = stack[1].m_obj;
uint8_t v_when_1936_ = stack[2].m_num;
lean_object* v___y_1937_ = stack[3].m_obj;
lean_object* v___y_1938_ = stack[4].m_obj;
lean_object* v___y_1939_ = stack[5].m_obj;
lean_object* v___y_1940_ = stack[6].m_obj;
lean_object* v_res_1943_;
v_res_1943_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(lean_box(0), v_x_1935_, v_when_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
stack->m_obj
 = v_res_1943_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_x_1945_, lean_object* v_when_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v_when_boxed_1952_; lean_object* v_res_1953_; 
v_when_boxed_1952_ = lean_unbox(v_when_1946_);
v_res_1953_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(v_00_u03b1_1944_, v_x_1945_, v_when_boxed_1952_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1953_;
}
}
lean_object* runtime_initialize_Lean_Meta_Diagnostics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Diagnostics(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin);
}
#ifdef __cplusplus
}
#endif
