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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedOrigin_default;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*);
lean_object* l_Lean_Meta_Origin_lt___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics_threshold;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(lean_object* v_thmId_4_, lean_object* v_a_5_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg___boxed(lean_object* v_thmId_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_thmId_32_, v_a_33_);
lean_dec(v_a_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(lean_object* v_thmId_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_thmId_36_, v_a_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___boxed(lean_object* v_thmId_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey(v_thmId_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(lean_object* v_opts_50_, lean_object* v_opt_51_){
_start:
{
lean_object* v_name_52_; lean_object* v_defValue_53_; lean_object* v_map_54_; lean_object* v___x_55_; 
v_name_52_ = lean_ctor_get(v_opt_51_, 0);
v_defValue_53_ = lean_ctor_get(v_opt_51_, 1);
v_map_54_ = lean_ctor_get(v_opts_50_, 0);
v___x_55_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_54_, v_name_52_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_inc(v_defValue_53_);
return v_defValue_53_;
}
else
{
lean_object* v_val_56_; 
v_val_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v___x_55_, 1);
if (lean_obj_tag(v_val_56_) == 3)
{
lean_object* v_v_57_; 
v_v_57_ = lean_ctor_get(v_val_56_, 0);
lean_inc(v_v_57_);
lean_dec_ref_known(v_val_56_, 1);
return v_v_57_;
}
else
{
lean_dec(v_val_56_);
lean_inc(v_defValue_53_);
return v_defValue_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0___boxed(lean_object* v_opts_58_, lean_object* v_opt_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(v_opts_58_, v_opt_59_);
lean_dec_ref(v_opt_59_);
lean_dec_ref(v_opts_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(lean_object* v_x_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 1;
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0___boxed(lean_object* v_x_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_Meta_Simp_mkSimpDiagSummary___lam__0(v_x_63_);
lean_dec_ref(v_x_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0(lean_object* v_f_66_, lean_object* v_s_67_, lean_object* v_a_68_, lean_object* v_b_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_a_68_);
lean_ctor_set(v___x_70_, 1, v_b_69_);
v___x_71_ = lean_apply_2(v_f_66_, v___x_70_, v_s_67_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_a_80_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_71_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_71_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_f_88_, lean_object* v_keys_89_, lean_object* v_vals_90_, lean_object* v_i_91_, lean_object* v_acc_92_){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_array_get_size(v_keys_89_);
v___x_94_ = lean_nat_dec_lt(v_i_91_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec(v_i_91_);
lean_dec_ref(v_f_88_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_acc_92_);
return v___x_95_;
}
else
{
lean_object* v_k_96_; lean_object* v_v_97_; lean_object* v___x_98_; 
v_k_96_ = lean_array_fget_borrowed(v_keys_89_, v_i_91_);
v_v_97_ = lean_array_fget_borrowed(v_vals_90_, v_i_91_);
lean_inc_ref(v_f_88_);
lean_inc(v_v_97_);
lean_inc(v_k_96_);
v___x_98_ = lean_apply_3(v_f_88_, v_acc_92_, v_k_96_, v_v_97_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_dec(v_i_91_);
lean_dec_ref(v_f_88_);
return v___x_98_;
}
else
{
lean_object* v_a_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_i_91_, v___x_100_);
lean_dec(v_i_91_);
v_i_91_ = v___x_101_;
v_acc_92_ = v_a_99_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_f_103_, lean_object* v_keys_104_, lean_object* v_vals_105_, lean_object* v_i_106_, lean_object* v_acc_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_103_, v_keys_104_, v_vals_105_, v_i_106_, v_acc_107_);
lean_dec_ref(v_vals_105_);
lean_dec_ref(v_keys_104_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_f_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v_es_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_132_; 
v_es_112_ = lean_ctor_get(v_x_110_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_110_);
if (v_isSharedCheck_132_ == 0)
{
v___x_114_ = v_x_110_;
v_isShared_115_ = v_isSharedCheck_132_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_es_112_);
lean_dec(v_x_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_132_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_array_get_size(v_es_112_);
v___x_118_ = lean_nat_dec_lt(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_120_; 
lean_dec_ref(v_es_112_);
lean_dec_ref(v_f_109_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 1);
lean_ctor_set(v___x_114_, 0, v_x_111_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_111_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_le(v___x_117_, v___x_117_);
if (v___x_122_ == 0)
{
if (v___x_118_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref(v_es_112_);
lean_dec_ref(v_f_109_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 1);
lean_ctor_set(v___x_114_, 0, v_x_111_);
v___x_124_ = v___x_114_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_x_111_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
lean_del_object(v___x_114_);
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_117_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_109_, v_es_112_, v___x_126_, v___x_127_, v_x_111_);
lean_dec_ref(v_es_112_);
return v___x_128_;
}
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_114_);
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_117_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_109_, v_es_112_, v___x_129_, v___x_130_, v_x_111_);
lean_dec_ref(v_es_112_);
return v___x_131_;
}
}
}
}
else
{
lean_object* v_ks_133_; lean_object* v_vs_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_ks_133_ = lean_ctor_get(v_x_110_, 0);
lean_inc_ref(v_ks_133_);
v_vs_134_ = lean_ctor_get(v_x_110_, 1);
lean_inc_ref(v_vs_134_);
lean_dec_ref_known(v_x_110_, 2);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_109_, v_ks_133_, v_vs_134_, v___x_135_, v_x_111_);
lean_dec_ref(v_vs_134_);
lean_dec_ref(v_ks_133_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_137_, lean_object* v_as_138_, size_t v_i_139_, size_t v_stop_140_, lean_object* v_b_141_){
_start:
{
lean_object* v_a_143_; lean_object* v___y_148_; uint8_t v___x_150_; 
v___x_150_ = lean_usize_dec_eq(v_i_139_, v_stop_140_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_array_uget_borrowed(v_as_138_, v_i_139_);
switch(lean_obj_tag(v___x_151_))
{
case 0:
{
lean_object* v_key_152_; lean_object* v_val_153_; lean_object* v___x_154_; 
v_key_152_ = lean_ctor_get(v___x_151_, 0);
v_val_153_ = lean_ctor_get(v___x_151_, 1);
lean_inc_ref(v_f_137_);
lean_inc(v_val_153_);
lean_inc(v_key_152_);
v___x_154_ = lean_apply_3(v_f_137_, v_b_141_, v_key_152_, v_val_153_);
v___y_148_ = v___x_154_;
goto v___jp_147_;
}
case 1:
{
lean_object* v_node_155_; lean_object* v___x_156_; 
v_node_155_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_node_155_);
lean_inc_ref(v_f_137_);
v___x_156_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_137_, v_node_155_, v_b_141_);
v___y_148_ = v___x_156_;
goto v___jp_147_;
}
default: 
{
v_a_143_ = v_b_141_;
goto v___jp_142_;
}
}
}
else
{
lean_object* v___x_157_; 
lean_dec_ref(v_f_137_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_b_141_);
return v___x_157_;
}
v___jp_142_:
{
size_t v___x_144_; size_t v___x_145_; 
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_add(v_i_139_, v___x_144_);
v_i_139_ = v___x_145_;
v_b_141_ = v_a_143_;
goto _start;
}
v___jp_147_:
{
if (lean_obj_tag(v___y_148_) == 0)
{
lean_dec_ref(v_f_137_);
return v___y_148_;
}
else
{
lean_object* v_a_149_; 
v_a_149_ = lean_ctor_get(v___y_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___y_148_, 1);
v_a_143_ = v_a_149_;
goto v___jp_142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_158_, lean_object* v_as_159_, lean_object* v_i_160_, lean_object* v_stop_161_, lean_object* v_b_162_){
_start:
{
size_t v_i_boxed_163_; size_t v_stop_boxed_164_; lean_object* v_res_165_; 
v_i_boxed_163_ = lean_unbox_usize(v_i_160_);
lean_dec(v_i_160_);
v_stop_boxed_164_ = lean_unbox_usize(v_stop_161_);
lean_dec(v_stop_161_);
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_158_, v_as_159_, v_i_boxed_163_, v_stop_boxed_164_, v_b_162_);
lean_dec_ref(v_as_159_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(lean_object* v_map_166_, lean_object* v_init_167_, lean_object* v_f_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v_a_171_; 
v___f_169_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_169_, 0, v_f_168_);
lean_inc_ref(v_map_166_);
v___x_170_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v___f_169_, v_map_166_, v_init_167_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
return v_a_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___boxed(lean_object* v_map_172_, lean_object* v_init_173_, lean_object* v_f_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_172_, v_init_173_, v_f_174_);
lean_dec_ref(v_map_172_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(lean_object* v_lt_176_, lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v_fst_181_; lean_object* v_snd_182_; uint8_t v___x_183_; 
v_fst_179_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_snd_180_);
lean_dec_ref(v_x_177_);
v_fst_181_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_fst_181_);
v_snd_182_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_snd_182_);
lean_dec_ref(v_x_178_);
v___x_183_ = lean_nat_dec_eq(v_snd_180_, v_snd_182_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; 
lean_dec(v_fst_181_);
lean_dec(v_fst_179_);
lean_dec_ref(v_lt_176_);
v___x_184_ = lean_nat_dec_lt(v_snd_182_, v_snd_180_);
lean_dec(v_snd_180_);
lean_dec(v_snd_182_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
lean_dec(v_snd_182_);
lean_dec(v_snd_180_);
v___x_185_ = lean_apply_2(v_lt_176_, v_fst_179_, v_fst_181_);
v___x_186_ = lean_unbox(v___x_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_lt_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_187_, v_x_188_, v_x_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(lean_object* v_lt_192_, lean_object* v_hi_193_, lean_object* v_pivot_194_, lean_object* v_as_195_, lean_object* v_i_196_, lean_object* v_k_197_){
_start:
{
uint8_t v___y_199_; uint8_t v___x_208_; 
v___x_208_ = lean_nat_dec_lt(v_k_197_, v_hi_193_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_k_197_);
lean_dec_ref(v_pivot_194_);
lean_dec_ref(v_lt_192_);
v___x_209_ = lean_array_fswap(v_as_195_, v_i_196_, v_hi_193_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_i_196_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v_fst_214_; lean_object* v_snd_215_; uint8_t v___x_216_; 
v___x_211_ = lean_array_fget_borrowed(v_as_195_, v_k_197_);
v_fst_212_ = lean_ctor_get(v___x_211_, 0);
v_snd_213_ = lean_ctor_get(v___x_211_, 1);
v_fst_214_ = lean_ctor_get(v_pivot_194_, 0);
v_snd_215_ = lean_ctor_get(v_pivot_194_, 1);
v___x_216_ = lean_nat_dec_eq(v_snd_213_, v_snd_215_);
if (v___x_216_ == 0)
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_lt(v_snd_215_, v_snd_213_);
v___y_199_ = v___x_217_;
goto v___jp_198_;
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; 
lean_inc_ref(v_lt_192_);
lean_inc(v_fst_214_);
lean_inc(v_fst_212_);
v___x_218_ = lean_apply_2(v_lt_192_, v_fst_212_, v_fst_214_);
v___x_219_ = lean_unbox(v___x_218_);
v___y_199_ = v___x_219_;
goto v___jp_198_;
}
}
v___jp_198_:
{
if (v___y_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_k_197_, v___x_200_);
lean_dec(v_k_197_);
v_k_197_ = v___x_201_;
goto _start;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_203_ = lean_array_fswap(v_as_195_, v_i_196_, v_k_197_);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_add(v_i_196_, v___x_204_);
lean_dec(v_i_196_);
v___x_206_ = lean_nat_add(v_k_197_, v___x_204_);
lean_dec(v_k_197_);
v_as_195_ = v___x_203_;
v_i_196_ = v___x_205_;
v_k_197_ = v___x_206_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_lt_220_, lean_object* v_hi_221_, lean_object* v_pivot_222_, lean_object* v_as_223_, lean_object* v_i_224_, lean_object* v_k_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_220_, v_hi_221_, v_pivot_222_, v_as_223_, v_i_224_, v_k_225_);
lean_dec(v_hi_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(lean_object* v_lt_227_, lean_object* v_n_228_, lean_object* v_as_229_, lean_object* v_lo_230_, lean_object* v_hi_231_){
_start:
{
lean_object* v___y_233_; uint8_t v___x_243_; 
v___x_243_ = lean_nat_dec_lt(v_lo_230_, v_hi_231_);
if (v___x_243_ == 0)
{
lean_dec(v_lo_230_);
lean_dec_ref(v_lt_227_);
return v_as_229_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_mid_246_; lean_object* v___y_248_; lean_object* v___y_254_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_244_ = lean_nat_add(v_lo_230_, v_hi_231_);
v___x_245_ = lean_unsigned_to_nat(1u);
v_mid_246_ = lean_nat_shiftr(v___x_244_, v___x_245_);
lean_dec(v___x_244_);
v___x_259_ = lean_array_fget_borrowed(v_as_229_, v_mid_246_);
v___x_260_ = lean_array_fget_borrowed(v_as_229_, v_lo_230_);
lean_inc(v___x_260_);
lean_inc(v___x_259_);
lean_inc_ref(v_lt_227_);
v___x_261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_227_, v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
v___y_254_ = v_as_229_;
goto v___jp_253_;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = lean_array_fswap(v_as_229_, v_lo_230_, v_mid_246_);
v___y_254_ = v___x_262_;
goto v___jp_253_;
}
v___jp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = lean_array_fget_borrowed(v___y_248_, v_mid_246_);
v___x_250_ = lean_array_fget_borrowed(v___y_248_, v_hi_231_);
lean_inc(v___x_250_);
lean_inc(v___x_249_);
lean_inc_ref(v_lt_227_);
v___x_251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_227_, v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v_mid_246_);
v___y_233_ = v___y_248_;
goto v___jp_232_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_array_fswap(v___y_248_, v_mid_246_, v_hi_231_);
lean_dec(v_mid_246_);
v___y_233_ = v___x_252_;
goto v___jp_232_;
}
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_array_fget_borrowed(v___y_254_, v_hi_231_);
v___x_256_ = lean_array_fget_borrowed(v___y_254_, v_lo_230_);
lean_inc(v___x_256_);
lean_inc(v___x_255_);
lean_inc_ref(v_lt_227_);
v___x_257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_227_, v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
v___y_248_ = v___y_254_;
goto v___jp_247_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_array_fswap(v___y_254_, v_lo_230_, v_hi_231_);
v___y_248_ = v___x_258_;
goto v___jp_247_;
}
}
}
v___jp_232_:
{
lean_object* v_pivot_234_; lean_object* v___x_235_; lean_object* v_fst_236_; lean_object* v_snd_237_; uint8_t v___x_238_; 
v_pivot_234_ = lean_array_fget(v___y_233_, v_hi_231_);
lean_inc_n(v_lo_230_, 2);
lean_inc_ref(v_lt_227_);
v___x_235_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_227_, v_hi_231_, v_pivot_234_, v___y_233_, v_lo_230_, v_lo_230_);
v_fst_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_fst_236_);
v_snd_237_ = lean_ctor_get(v___x_235_, 1);
lean_inc(v_snd_237_);
lean_dec_ref(v___x_235_);
v___x_238_ = lean_nat_dec_le(v_hi_231_, v_fst_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
lean_inc_ref(v_lt_227_);
v___x_239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_227_, v_n_228_, v_snd_237_, v_lo_230_, v_fst_236_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_fst_236_, v___x_240_);
lean_dec(v_fst_236_);
v_as_229_ = v___x_239_;
v_lo_230_ = v___x_241_;
goto _start;
}
else
{
lean_dec(v_fst_236_);
lean_dec(v_lo_230_);
lean_dec_ref(v_lt_227_);
return v_snd_237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___boxed(lean_object* v_lt_263_, lean_object* v_n_264_, lean_object* v_as_265_, lean_object* v_lo_266_, lean_object* v_hi_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_263_, v_n_264_, v_as_265_, v_lo_266_, v_hi_267_);
lean_dec(v_hi_267_);
lean_dec(v_n_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(lean_object* v_threshold_269_, lean_object* v_p_270_, lean_object* v_x_271_, lean_object* v_____s_272_){
_start:
{
lean_object* v_fst_273_; lean_object* v_snd_274_; uint8_t v___x_275_; 
v_fst_273_ = lean_ctor_get(v_x_271_, 0);
v_snd_274_ = lean_ctor_get(v_x_271_, 1);
v___x_275_ = lean_nat_dec_lt(v_threshold_269_, v_snd_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v_x_271_);
lean_dec_ref(v_p_270_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_____s_272_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; uint8_t v___x_278_; 
lean_inc(v_fst_273_);
v___x_277_ = lean_apply_1(v_p_270_, v_fst_273_);
v___x_278_ = lean_unbox(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec_ref(v_x_271_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_____s_272_);
return v___x_279_;
}
else
{
lean_object* v_r_280_; lean_object* v___x_281_; 
v_r_280_ = lean_array_push(v_____s_272_, v_x_271_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_r_280_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed(lean_object* v_threshold_282_, lean_object* v_p_283_, lean_object* v_x_284_, lean_object* v_____s_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(v_threshold_282_, v_p_283_, v_x_284_, v_____s_285_);
lean_dec(v_threshold_282_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(lean_object* v_counters_289_, lean_object* v_threshold_290_, lean_object* v_p_291_, lean_object* v_lt_292_){
_start:
{
lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v_r_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___f_293_ = lean_alloc_closure((void*)(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed), 4, 2);
lean_closure_set(v___f_293_, 0, v_threshold_290_);
lean_closure_set(v___f_293_, 1, v_p_291_);
v___x_294_ = lean_unsigned_to_nat(0u);
v_r_295_ = ((lean_object*)(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0));
v___x_296_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_counters_289_, v_r_295_, v___f_293_);
v___x_297_ = lean_array_get_size(v___x_296_);
v___x_298_ = lean_nat_dec_eq(v___x_297_, v___x_294_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___y_302_; uint8_t v___x_306_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_sub(v___x_297_, v___x_299_);
v___x_306_ = lean_nat_dec_le(v___x_294_, v___x_300_);
if (v___x_306_ == 0)
{
lean_inc(v___x_300_);
v___y_302_ = v___x_300_;
goto v___jp_301_;
}
else
{
v___y_302_ = v___x_294_;
goto v___jp_301_;
}
v___jp_301_:
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_le(v___y_302_, v___x_300_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec(v___x_300_);
lean_inc(v___y_302_);
v___x_304_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_292_, v___x_297_, v___x_296_, v___y_302_, v___y_302_);
lean_dec(v___y_302_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_292_, v___x_297_, v___x_296_, v___y_302_, v___x_300_);
lean_dec(v___x_300_);
return v___x_305_;
}
}
}
else
{
lean_dec_ref(v_lt_292_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___boxed(lean_object* v_counters_307_, lean_object* v_threshold_308_, lean_object* v_p_309_, lean_object* v_lt_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(v_counters_307_, v_threshold_308_, v_p_309_, v_lt_310_);
lean_dec_ref(v_counters_307_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(lean_object* v_keys_312_, lean_object* v_vals_313_, lean_object* v_i_314_, lean_object* v_k_315_){
_start:
{
uint8_t v___y_321_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_get_size(v_keys_312_);
v___x_325_ = lean_nat_dec_lt(v_i_314_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_i_314_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v_k_x27_327_; 
v_k_x27_327_ = lean_array_fget_borrowed(v_keys_312_, v_i_314_);
if (lean_obj_tag(v_k_315_) == 0)
{
if (lean_obj_tag(v_k_x27_327_) == 0)
{
lean_object* v_declName_328_; uint8_t v_inv_329_; lean_object* v_declName_330_; uint8_t v_inv_331_; uint8_t v___x_332_; 
v_declName_328_ = lean_ctor_get(v_k_315_, 0);
v_inv_329_ = lean_ctor_get_uint8(v_k_315_, sizeof(void*)*1 + 1);
v_declName_330_ = lean_ctor_get(v_k_x27_327_, 0);
v_inv_331_ = lean_ctor_get_uint8(v_k_x27_327_, sizeof(void*)*1 + 1);
v___x_332_ = lean_name_eq(v_declName_328_, v_declName_330_);
if (v___x_332_ == 0)
{
v___y_321_ = v___x_332_;
goto v___jp_320_;
}
else
{
if (v_inv_329_ == 0)
{
if (v_inv_331_ == 0)
{
v___y_321_ = v___x_332_;
goto v___jp_320_;
}
else
{
goto v___jp_316_;
}
}
else
{
v___y_321_ = v_inv_331_;
goto v___jp_320_;
}
}
}
else
{
goto v___jp_316_;
}
}
else
{
if (lean_obj_tag(v_k_x27_327_) == 0)
{
goto v___jp_316_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_333_ = l_Lean_Meta_Origin_key(v_k_315_);
v___x_334_ = l_Lean_Meta_Origin_key(v_k_x27_327_);
v___x_335_ = lean_name_eq(v___x_333_, v___x_334_);
lean_dec(v___x_334_);
lean_dec(v___x_333_);
v___y_321_ = v___x_335_;
goto v___jp_320_;
}
}
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_i_314_, v___x_317_);
lean_dec(v_i_314_);
v_i_314_ = v___x_318_;
goto _start;
}
v___jp_320_:
{
if (v___y_321_ == 0)
{
goto v___jp_316_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_array_fget_borrowed(v_vals_313_, v_i_314_);
lean_dec(v_i_314_);
lean_inc(v___x_322_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_keys_336_, lean_object* v_vals_337_, lean_object* v_i_338_, lean_object* v_k_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_336_, v_vals_337_, v_i_338_, v_k_339_);
lean_dec_ref(v_k_339_);
lean_dec_ref(v_vals_337_);
lean_dec_ref(v_keys_336_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(lean_object* v_x_341_, size_t v_x_342_, lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v_es_344_; lean_object* v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v_j_348_; lean_object* v___x_349_; 
v_es_344_ = lean_ctor_get(v_x_341_, 0);
v___x_345_ = lean_box(2);
v___x_346_ = ((size_t)31ULL);
v___x_347_ = lean_usize_land(v_x_342_, v___x_346_);
v_j_348_ = lean_usize_to_nat(v___x_347_);
v___x_349_ = lean_array_get_borrowed(v___x_345_, v_es_344_, v_j_348_);
lean_dec(v_j_348_);
switch(lean_obj_tag(v___x_349_))
{
case 0:
{
lean_object* v_key_350_; lean_object* v_val_351_; uint8_t v___y_353_; 
v_key_350_ = lean_ctor_get(v___x_349_, 0);
v_val_351_ = lean_ctor_get(v___x_349_, 1);
if (lean_obj_tag(v_x_343_) == 0)
{
if (lean_obj_tag(v_key_350_) == 0)
{
lean_object* v_declName_356_; uint8_t v_inv_357_; lean_object* v_declName_358_; uint8_t v_inv_359_; uint8_t v___x_360_; 
v_declName_356_ = lean_ctor_get(v_x_343_, 0);
v_inv_357_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*1 + 1);
v_declName_358_ = lean_ctor_get(v_key_350_, 0);
v_inv_359_ = lean_ctor_get_uint8(v_key_350_, sizeof(void*)*1 + 1);
v___x_360_ = lean_name_eq(v_declName_356_, v_declName_358_);
if (v___x_360_ == 0)
{
v___y_353_ = v___x_360_;
goto v___jp_352_;
}
else
{
if (v_inv_357_ == 0)
{
if (v_inv_359_ == 0)
{
v___y_353_ = v___x_360_;
goto v___jp_352_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
}
else
{
v___y_353_ = v_inv_359_;
goto v___jp_352_;
}
}
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(0);
return v___x_362_;
}
}
else
{
if (lean_obj_tag(v_key_350_) == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_box(0);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_364_ = l_Lean_Meta_Origin_key(v_x_343_);
v___x_365_ = l_Lean_Meta_Origin_key(v_key_350_);
v___x_366_ = lean_name_eq(v___x_364_, v___x_365_);
lean_dec(v___x_365_);
lean_dec(v___x_364_);
v___y_353_ = v___x_366_;
goto v___jp_352_;
}
}
v___jp_352_:
{
if (v___y_353_ == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_box(0);
return v___x_354_;
}
else
{
lean_object* v___x_355_; 
lean_inc(v_val_351_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_val_351_);
return v___x_355_;
}
}
}
case 1:
{
lean_object* v_node_367_; size_t v___x_368_; size_t v___x_369_; 
v_node_367_ = lean_ctor_get(v___x_349_, 0);
v___x_368_ = ((size_t)5ULL);
v___x_369_ = lean_usize_shift_right(v_x_342_, v___x_368_);
v_x_341_ = v_node_367_;
v_x_342_ = v___x_369_;
goto _start;
}
default: 
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
}
else
{
lean_object* v_ks_372_; lean_object* v_vs_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_ks_372_ = lean_ctor_get(v_x_341_, 0);
v_vs_373_ = lean_ctor_get(v_x_341_, 1);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_ks_372_, v_vs_373_, v___x_374_, v_x_343_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___boxed(lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
size_t v_x_4628__boxed_379_; lean_object* v_res_380_; 
v_x_4628__boxed_379_ = lean_unbox_usize(v_x_377_);
lean_dec(v_x_377_);
v_res_380_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_376_, v_x_4628__boxed_379_, v_x_378_);
lean_dec_ref(v_x_378_);
lean_dec_ref(v_x_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
uint64_t v___y_384_; uint64_t v___y_388_; uint64_t v___y_392_; 
if (lean_obj_tag(v_x_382_) == 0)
{
uint8_t v_inv_395_; 
v_inv_395_ = lean_ctor_get_uint8(v_x_382_, sizeof(void*)*1 + 1);
if (v_inv_395_ == 0)
{
lean_object* v_declName_396_; 
v_declName_396_ = lean_ctor_get(v_x_382_, 0);
if (lean_obj_tag(v_declName_396_) == 0)
{
uint64_t v___x_397_; 
v___x_397_ = 1723ULL;
v___y_388_ = v___x_397_;
goto v___jp_387_;
}
else
{
uint64_t v_hash_398_; 
v_hash_398_ = lean_ctor_get_uint64(v_declName_396_, sizeof(void*)*2);
v___y_388_ = v_hash_398_;
goto v___jp_387_;
}
}
else
{
lean_object* v_declName_399_; 
v_declName_399_ = lean_ctor_get(v_x_382_, 0);
if (lean_obj_tag(v_declName_399_) == 0)
{
uint64_t v___x_400_; 
v___x_400_ = 1723ULL;
v___y_392_ = v___x_400_;
goto v___jp_391_;
}
else
{
uint64_t v_hash_401_; 
v_hash_401_ = lean_ctor_get_uint64(v_declName_399_, sizeof(void*)*2);
v___y_392_ = v_hash_401_;
goto v___jp_391_;
}
}
}
else
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Origin_key(v_x_382_);
if (lean_obj_tag(v___x_402_) == 0)
{
uint64_t v___x_403_; 
v___x_403_ = 1723ULL;
v___y_384_ = v___x_403_;
goto v___jp_383_;
}
else
{
uint64_t v_hash_404_; 
v_hash_404_ = lean_ctor_get_uint64(v___x_402_, sizeof(void*)*2);
lean_dec(v___x_402_);
v___y_384_ = v_hash_404_;
goto v___jp_383_;
}
}
v___jp_383_:
{
size_t v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_uint64_to_usize(v___y_384_);
v___x_386_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_381_, v___x_385_, v_x_382_);
return v___x_386_;
}
v___jp_387_:
{
uint64_t v___x_389_; uint64_t v___x_390_; 
v___x_389_ = 13ULL;
v___x_390_ = lean_uint64_mix_hash(v___y_388_, v___x_389_);
v___y_384_ = v___x_390_;
goto v___jp_383_;
}
v___jp_391_:
{
uint64_t v___x_393_; uint64_t v___x_394_; 
v___x_393_ = 11ULL;
v___x_394_ = lean_uint64_mix_hash(v___y_392_, v___x_393_);
v___y_384_ = v___x_394_;
goto v___jp_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___boxed(lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_405_, v_x_406_);
lean_dec_ref(v_x_406_);
lean_dec_ref(v_x_405_);
return v_res_407_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_413_; double v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_float_of_nat(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l_Lean_crossEmoji;
v___x_422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8));
v___x_423_ = lean_string_append(v___x_422_, v___x_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(lean_object* v_usedCounters_x3f_424_, lean_object* v_as_425_, size_t v_sz_426_, size_t v_i_427_, lean_object* v_b_428_, lean_object* v___y_429_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v_b_428_);
return v___x_432_;
}
else
{
lean_object* v_a_433_; lean_object* v_fst_434_; lean_object* v_snd_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_480_; 
v_a_433_ = lean_array_uget(v_as_425_, v_i_427_);
v_fst_434_ = lean_ctor_get(v_a_433_, 0);
v_snd_435_ = lean_ctor_get(v_a_433_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_433_);
if (v_isSharedCheck_480_ == 0)
{
v___x_437_ = v_a_433_;
v_isShared_438_ = v_isSharedCheck_480_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_snd_435_);
lean_inc(v_fst_434_);
lean_dec(v_a_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_480_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; 
lean_inc(v_fst_434_);
v___x_439_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_fst_434_, v___y_429_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v_usedMsg_443_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
if (lean_obj_tag(v_usedCounters_x3f_424_) == 1)
{
lean_object* v_val_464_; lean_object* v___x_465_; 
v_val_464_ = lean_ctor_get(v_usedCounters_x3f_424_, 0);
v___x_465_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_val_464_, v_fst_434_);
lean_dec(v_fst_434_);
if (lean_obj_tag(v___x_465_) == 1)
{
lean_object* v_val_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7));
v___x_468_ = l_Nat_reprFast(v_val_466_);
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
lean_dec_ref(v___x_468_);
v_usedMsg_443_ = v___x_469_;
goto v___jp_442_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v___x_465_);
v___x_470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9);
v_usedMsg_443_ = v___x_470_;
goto v___jp_442_;
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_fst_434_);
v___x_471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v_usedMsg_443_ = v___x_471_;
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; double v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_445_ = lean_box(0);
v___x_446_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_448_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_445_);
lean_ctor_set(v___x_448_, 2, v___x_447_);
lean_ctor_set_float(v___x_448_, sizeof(void*)*3, v___x_446_);
lean_ctor_set_float(v___x_448_, sizeof(void*)*3 + 8, v___x_446_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*3 + 16, v___x_431_);
v___x_449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 7);
lean_ctor_set(v___x_437_, 1, v___x_449_);
lean_ctor_set(v___x_437_, 0, v_a_440_);
v___x_451_ = v___x_437_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_440_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_463_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; size_t v___x_460_; size_t v___x_461_; 
v___x_452_ = l_Nat_reprFast(v_snd_435_);
v___x_453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
v___x_454_ = l_Lean_MessageData_ofFormat(v___x_453_);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_451_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_Lean_stringToMessageData(v_usedMsg_443_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_448_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
lean_ctor_set(v___x_458_, 2, v___x_441_);
v___x_459_ = lean_array_push(v_b_428_, v___x_458_);
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_427_, v___x_460_);
v_i_427_ = v___x_461_;
v_b_428_ = v___x_459_;
goto _start;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_437_);
lean_dec(v_snd_435_);
lean_dec(v_fst_434_);
lean_dec_ref(v_b_428_);
v_a_472_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_439_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_439_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary(lean_object* v_counters_499_, lean_object* v_usedCounters_x3f_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_options_506_; lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_options_506_ = lean_ctor_get(v_a_503_, 2);
v___f_507_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0));
v___f_508_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1));
v___x_509_ = l_Lean_diagnostics_threshold;
v___x_510_ = l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(v_options_506_, v___x_509_);
v___x_511_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(v_counters_499_, v___x_510_, v___f_508_, v___f_507_);
v___x_512_ = lean_array_get_size(v___x_511_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_nat_dec_eq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; size_t v_sz_516_; size_t v___x_517_; lean_object* v___x_518_; 
v___x_515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v_sz_516_ = lean_array_size(v___x_511_);
v___x_517_ = ((size_t)0ULL);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_500_, v___x_511_, v_sz_516_, v___x_517_, v___x_515_, v_a_504_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_537_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_537_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_537_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_537_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_snd_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_535_; 
v___x_523_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2, &l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2_once, _init_l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2);
v___x_524_ = lean_array_get(v___x_523_, v___x_511_, v___x_513_);
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
lean_ctor_set(v___x_527_, 0, v_a_519_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_519_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_snd_525_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_530_);
v___x_532_ = v___x_521_;
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
v_a_538_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_518_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_518_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___boxed(lean_object* v_counters_548_, lean_object* v_usedCounters_x3f_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_counters_548_, v_usedCounters_x3f_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_usedCounters_x3f_549_);
lean_dec_ref(v_counters_548_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(lean_object* v_00_u03b2_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_557_, v_x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___boxed(lean_object* v_00_u03b2_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(v_00_u03b2_560_, v_x_561_, v_x_562_);
lean_dec_ref(v_x_562_);
lean_dec_ref(v_x_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(lean_object* v_usedCounters_x3f_564_, lean_object* v_as_565_, size_t v_sz_566_, size_t v_i_567_, lean_object* v_b_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_564_, v_as_565_, v_sz_566_, v_i_567_, v_b_568_, v___y_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___boxed(lean_object* v_usedCounters_x3f_575_, lean_object* v_as_576_, lean_object* v_sz_577_, lean_object* v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_577_);
lean_dec(v_sz_577_);
v_i_boxed_586_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(v_usedCounters_x3f_575_, v_as_576_, v_sz_boxed_585_, v_i_boxed_586_, v_b_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_as_576_);
lean_dec(v_usedCounters_x3f_575_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(lean_object* v_00_u03c3_588_, lean_object* v_00_u03b2_589_, lean_object* v_map_590_, lean_object* v_init_591_, lean_object* v_f_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_590_, v_init_591_, v_f_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___boxed(lean_object* v_00_u03c3_594_, lean_object* v_00_u03b2_595_, lean_object* v_map_596_, lean_object* v_init_597_, lean_object* v_f_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(v_00_u03c3_594_, v_00_u03b2_595_, v_map_596_, v_init_597_, v_f_598_);
lean_dec_ref(v_map_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(lean_object* v_lt_600_, lean_object* v_n_601_, lean_object* v_as_602_, lean_object* v_lo_603_, lean_object* v_hi_604_, lean_object* v_w_605_, lean_object* v_hlo_606_, lean_object* v_hhi_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_600_, v_n_601_, v_as_602_, v_lo_603_, v_hi_604_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___boxed(lean_object* v_lt_609_, lean_object* v_n_610_, lean_object* v_as_611_, lean_object* v_lo_612_, lean_object* v_hi_613_, lean_object* v_w_614_, lean_object* v_hlo_615_, lean_object* v_hhi_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(v_lt_609_, v_n_610_, v_as_611_, v_lo_612_, v_hi_613_, v_w_614_, v_hlo_615_, v_hhi_616_);
lean_dec(v_hi_613_);
lean_dec(v_n_610_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(lean_object* v_00_u03b2_618_, lean_object* v_x_619_, size_t v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_619_, v_x_620_, v_x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___boxed(lean_object* v_00_u03b2_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
size_t v_x_5036__boxed_627_; lean_object* v_res_628_; 
v_x_5036__boxed_627_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_res_628_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(v_00_u03b2_623_, v_x_624_, v_x_5036__boxed_627_, v_x_626_);
lean_dec_ref(v_x_626_);
lean_dec_ref(v_x_624_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2___redArg(lean_object* v_map_629_, lean_object* v_f_630_, lean_object* v_init_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_630_, v_map_629_, v_init_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_633_, lean_object* v_00_u03c3_634_, lean_object* v_00_u03b2_635_, lean_object* v_map_636_, lean_object* v_f_637_, lean_object* v_init_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_637_, v_map_636_, v_init_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(lean_object* v_lt_640_, lean_object* v_n_641_, lean_object* v_lo_642_, lean_object* v_hi_643_, lean_object* v_hhi_644_, lean_object* v_pivot_645_, lean_object* v_as_646_, lean_object* v_i_647_, lean_object* v_k_648_, lean_object* v_ilo_649_, lean_object* v_ik_650_, lean_object* v_w_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_640_, v_hi_643_, v_pivot_645_, v_as_646_, v_i_647_, v_k_648_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___boxed(lean_object* v_lt_653_, lean_object* v_n_654_, lean_object* v_lo_655_, lean_object* v_hi_656_, lean_object* v_hhi_657_, lean_object* v_pivot_658_, lean_object* v_as_659_, lean_object* v_i_660_, lean_object* v_k_661_, lean_object* v_ilo_662_, lean_object* v_ik_663_, lean_object* v_w_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(v_lt_653_, v_n_654_, v_lo_655_, v_hi_656_, v_hhi_657_, v_pivot_658_, v_as_659_, v_i_660_, v_k_661_, v_ilo_662_, v_ik_663_, v_w_664_);
lean_dec(v_hi_656_);
lean_dec(v_lo_655_);
lean_dec(v_n_654_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_666_, lean_object* v_keys_667_, lean_object* v_vals_668_, lean_object* v_heq_669_, lean_object* v_i_670_, lean_object* v_k_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_667_, v_vals_668_, v_i_670_, v_k_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_673_, lean_object* v_keys_674_, lean_object* v_vals_675_, lean_object* v_heq_676_, lean_object* v_i_677_, lean_object* v_k_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(v_00_u03b2_673_, v_keys_674_, v_vals_675_, v_heq_676_, v_i_677_, v_k_678_);
lean_dec_ref(v_k_678_);
lean_dec_ref(v_vals_675_);
lean_dec_ref(v_keys_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_680_, lean_object* v_00_u03c3_681_, lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_f_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_684_, v_x_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_00_u03c3_690_, lean_object* v_00_u03c3_691_, lean_object* v_f_692_, lean_object* v_as_693_, size_t v_i_694_, size_t v_stop_695_, lean_object* v_b_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_692_, v_as_693_, v_i_694_, v_stop_695_, v_b_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_00_u03c3_700_, lean_object* v_00_u03c3_701_, lean_object* v_f_702_, lean_object* v_as_703_, lean_object* v_i_704_, lean_object* v_stop_705_, lean_object* v_b_706_){
_start:
{
size_t v_i_boxed_707_; size_t v_stop_boxed_708_; lean_object* v_res_709_; 
v_i_boxed_707_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_stop_boxed_708_ = lean_unbox_usize(v_stop_705_);
lean_dec(v_stop_705_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b1_698_, v_00_u03b2_699_, v_00_u03c3_700_, v_00_u03c3_701_, v_f_702_, v_as_703_, v_i_boxed_707_, v_stop_boxed_708_, v_b_706_);
lean_dec_ref(v_as_703_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03c3_710_, lean_object* v_00_u03c3_711_, lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_f_714_, lean_object* v_keys_715_, lean_object* v_vals_716_, lean_object* v_heq_717_, lean_object* v_i_718_, lean_object* v_acc_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_714_, v_keys_715_, v_vals_716_, v_i_718_, v_acc_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03c3_721_, lean_object* v_00_u03c3_722_, lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_f_725_, lean_object* v_keys_726_, lean_object* v_vals_727_, lean_object* v_heq_728_, lean_object* v_i_729_, lean_object* v_acc_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(v_00_u03c3_721_, v_00_u03c3_722_, v_00_u03b1_723_, v_00_u03b2_724_, v_f_725_, v_keys_726_, v_vals_727_, v_heq_728_, v_i_729_, v_acc_730_);
lean_dec_ref(v_vals_727_);
lean_dec_ref(v_keys_726_);
return v_res_731_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_as_735_, size_t v_sz_736_, size_t v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_lt(v_i_737_, v_sz_736_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_b_738_);
return v___x_743_;
}
else
{
lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_788_; 
v_snd_744_ = lean_ctor_get(v_b_738_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_b_738_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_b_738_, 0);
lean_dec(v_unused_789_);
v___x_746_ = v_b_738_;
v_isShared_747_ = v_isSharedCheck_788_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_dec(v_b_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_788_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_a_748_; lean_object* v_keys_749_; lean_object* v_origin_750_; lean_object* v___x_751_; 
v_a_748_ = lean_array_uget_borrowed(v_as_735_, v_i_737_);
v_keys_749_ = lean_ctor_get(v_a_748_, 0);
v_origin_750_ = lean_ctor_get(v_a_748_, 4);
lean_inc_ref(v_origin_750_);
v___x_751_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_750_, v___y_740_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
lean_inc_ref(v_keys_749_);
v___x_753_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_749_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v_data_755_; lean_object* v___x_756_; lean_object* v___x_757_; double v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v_data_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_756_ = lean_box(0);
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_758_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_760_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_756_);
lean_ctor_set(v___x_760_, 2, v___x_759_);
lean_ctor_set_float(v___x_760_, sizeof(void*)*3, v___x_758_);
lean_ctor_set_float(v___x_760_, sizeof(void*)*3 + 8, v___x_758_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*3 + 16, v___x_742_);
v___x_761_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v_a_752_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_a_754_);
v___x_764_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_764_, 0, v___x_760_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
lean_ctor_set(v___x_764_, 2, v_data_755_);
v___x_765_ = lean_array_push(v_snd_744_, v___x_764_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_765_);
lean_ctor_set(v___x_746_, 0, v___x_756_);
v___x_767_ = v___x_746_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
size_t v___x_768_; size_t v___x_769_; 
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_add(v_i_737_, v___x_768_);
v_i_737_ = v___x_769_;
v_b_738_ = v___x_767_;
goto _start;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_a_752_);
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
v_a_772_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_753_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_753_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
v_a_780_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_751_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_751_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_as_790_, lean_object* v_sz_791_, lean_object* v_i_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v_sz_boxed_797_ = lean_unbox_usize(v_sz_791_);
lean_dec(v_sz_791_);
v_i_boxed_798_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_790_, v_sz_boxed_797_, v_i_boxed_798_, v_b_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v_as_790_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(lean_object* v_as_800_, size_t v_sz_801_, size_t v_i_802_, lean_object* v_b_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v_b_803_);
return v___x_810_;
}
else
{
lean_object* v_snd_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_855_; 
v_snd_811_ = lean_ctor_get(v_b_803_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_b_803_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v_b_803_, 0);
lean_dec(v_unused_856_);
v___x_813_ = v_b_803_;
v_isShared_814_ = v_isSharedCheck_855_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_snd_811_);
lean_dec(v_b_803_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_855_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_a_815_; lean_object* v_keys_816_; lean_object* v_origin_817_; lean_object* v___x_818_; 
v_a_815_ = lean_array_uget_borrowed(v_as_800_, v_i_802_);
v_keys_816_ = lean_ctor_get(v_a_815_, 0);
v_origin_817_ = lean_ctor_get(v_a_815_, 4);
lean_inc_ref(v_origin_817_);
v___x_818_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_817_, v___y_807_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
lean_inc_ref(v_keys_816_);
v___x_820_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_816_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v_data_822_; lean_object* v___x_823_; lean_object* v___x_824_; double v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v_data_822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_823_ = lean_box(0);
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_825_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_827_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_827_, 0, v___x_824_);
lean_ctor_set(v___x_827_, 1, v___x_823_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
lean_ctor_set_float(v___x_827_, sizeof(void*)*3, v___x_825_);
lean_ctor_set_float(v___x_827_, sizeof(void*)*3 + 8, v___x_825_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*3 + 16, v___x_809_);
v___x_828_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v_a_819_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_a_821_);
v___x_831_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_831_, 0, v___x_827_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
lean_ctor_set(v___x_831_, 2, v_data_822_);
v___x_832_ = lean_array_push(v_snd_811_, v___x_831_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_832_);
lean_ctor_set(v___x_813_, 0, v___x_823_);
v___x_834_ = v___x_813_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_832_);
v___x_834_ = v_reuseFailAlloc_838_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; 
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_802_, v___x_835_);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_800_, v_sz_801_, v___x_836_, v___x_834_, v___y_806_, v___y_807_);
return v___x_837_;
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_a_819_);
lean_del_object(v___x_813_);
lean_dec(v_snd_811_);
v_a_839_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_820_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_820_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_del_object(v___x_813_);
lean_dec(v_snd_811_);
v_a_847_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_818_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_818_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2___boxed(lean_object* v_as_857_, lean_object* v_sz_858_, lean_object* v_i_859_, lean_object* v_b_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
size_t v_sz_boxed_866_; size_t v_i_boxed_867_; lean_object* v_res_868_; 
v_sz_boxed_866_ = lean_unbox_usize(v_sz_858_);
lean_dec(v_sz_858_);
v_i_boxed_867_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_as_857_, v_sz_boxed_866_, v_i_boxed_867_, v_b_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec_ref(v_as_857_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(lean_object* v_init_869_, lean_object* v_n_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
if (lean_obj_tag(v_n_870_) == 0)
{
lean_object* v_cs_877_; lean_object* v___x_878_; lean_object* v___x_879_; size_t v_sz_880_; size_t v___x_881_; lean_object* v___x_882_; 
v_cs_877_ = lean_ctor_get(v_n_870_, 0);
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_b_871_);
v_sz_880_ = lean_array_size(v_cs_877_);
v___x_881_ = ((size_t)0ULL);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_869_, v_cs_877_, v_sz_880_, v___x_881_, v___x_879_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_897_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_897_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_fst_887_; 
v_fst_887_ = lean_ctor_get(v_a_883_, 0);
if (lean_obj_tag(v_fst_887_) == 0)
{
lean_object* v_snd_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v_snd_888_ = lean_ctor_get(v_a_883_, 1);
lean_inc(v_snd_888_);
lean_dec(v_a_883_);
v___x_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_889_, 0, v_snd_888_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_889_);
v___x_891_ = v___x_885_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
lean_object* v_val_893_; lean_object* v___x_895_; 
lean_inc_ref(v_fst_887_);
lean_dec(v_a_883_);
v_val_893_ = lean_ctor_get(v_fst_887_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_fst_887_, 1);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_val_893_);
v___x_895_ = v___x_885_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_val_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_898_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_882_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_882_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v_vs_906_; lean_object* v___x_907_; lean_object* v___x_908_; size_t v_sz_909_; size_t v___x_910_; lean_object* v___x_911_; 
v_vs_906_ = lean_ctor_get(v_n_870_, 0);
v___x_907_ = lean_box(0);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v_b_871_);
v_sz_909_ = lean_array_size(v_vs_906_);
v___x_910_ = ((size_t)0ULL);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_vs_906_, v_sz_909_, v___x_910_, v___x_908_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_926_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_926_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_fst_916_; 
v_fst_916_ = lean_ctor_get(v_a_912_, 0);
if (lean_obj_tag(v_fst_916_) == 0)
{
lean_object* v_snd_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v_snd_917_ = lean_ctor_get(v_a_912_, 1);
lean_inc(v_snd_917_);
lean_dec(v_a_912_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v_snd_917_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_918_);
v___x_920_ = v___x_914_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v_val_922_; lean_object* v___x_924_; 
lean_inc_ref(v_fst_916_);
lean_dec(v_a_912_);
v_val_922_ = lean_ctor_get(v_fst_916_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v_fst_916_, 1);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v_val_922_);
v___x_924_ = v___x_914_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_val_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_911_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_911_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(lean_object* v_init_935_, lean_object* v_as_936_, size_t v_sz_937_, size_t v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_938_, v_sz_937_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_b_939_);
return v___x_946_;
}
else
{
lean_object* v_snd_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_981_; 
v_snd_947_ = lean_ctor_get(v_b_939_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_b_939_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v_b_939_, 0);
lean_dec(v_unused_982_);
v___x_949_ = v_b_939_;
v_isShared_950_ = v_isSharedCheck_981_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_snd_947_);
lean_dec(v_b_939_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_981_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_a_951_; lean_object* v___x_952_; 
v_a_951_ = lean_array_uget_borrowed(v_as_936_, v_i_938_);
lean_inc(v_snd_947_);
v___x_952_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_935_, v_a_951_, v_snd_947_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_972_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_972_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_972_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_972_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
if (lean_obj_tag(v_a_953_) == 0)
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_a_953_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_957_);
v___x_959_ = v___x_949_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_snd_947_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_959_);
v___x_961_ = v___x_955_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
lean_del_object(v___x_955_);
lean_dec(v_snd_947_);
v_a_964_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v_a_953_, 1);
v___x_965_ = lean_box(0);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_a_964_);
lean_ctor_set(v___x_949_, 0, v___x_965_);
v___x_967_ = v___x_949_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_a_964_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
size_t v___x_968_; size_t v___x_969_; 
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_add(v_i_938_, v___x_968_);
v_i_938_ = v___x_969_;
v_b_939_ = v___x_967_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_del_object(v___x_949_);
lean_dec(v_snd_947_);
v_a_973_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_952_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_952_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1___boxed(lean_object* v_init_983_, lean_object* v_as_984_, lean_object* v_sz_985_, lean_object* v_i_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_985_);
lean_dec(v_sz_985_);
v_i_boxed_994_ = lean_unbox_usize(v_i_986_);
lean_dec(v_i_986_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_983_, v_as_984_, v_sz_boxed_993_, v_i_boxed_994_, v_b_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_as_984_);
lean_dec_ref(v_init_983_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0___boxed(lean_object* v_init_996_, lean_object* v_n_997_, lean_object* v_b_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_996_, v_n_997_, v_b_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec_ref(v_n_997_);
lean_dec_ref(v_init_996_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1005_, size_t v_sz_1006_, size_t v_i_1007_, lean_object* v_b_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_usize_dec_lt(v_i_1007_, v_sz_1006_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_b_1008_);
return v___x_1013_;
}
else
{
lean_object* v_snd_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1058_; 
v_snd_1014_ = lean_ctor_get(v_b_1008_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_b_1008_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v_b_1008_, 0);
lean_dec(v_unused_1059_);
v___x_1016_ = v_b_1008_;
v_isShared_1017_ = v_isSharedCheck_1058_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_snd_1014_);
lean_dec(v_b_1008_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1058_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_a_1018_; lean_object* v_keys_1019_; lean_object* v_origin_1020_; lean_object* v___x_1021_; 
v_a_1018_ = lean_array_uget_borrowed(v_as_1005_, v_i_1007_);
v_keys_1019_ = lean_ctor_get(v_a_1018_, 0);
v_origin_1020_ = lean_ctor_get(v_a_1018_, 4);
lean_inc_ref(v_origin_1020_);
v___x_1021_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_1020_, v___y_1010_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
lean_inc_ref(v_keys_1019_);
v___x_1023_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1019_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v_data_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; double v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v_data_1025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1026_ = lean_box(0);
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1028_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1030_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1030_, 0, v___x_1027_);
lean_ctor_set(v___x_1030_, 1, v___x_1026_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
lean_ctor_set_float(v___x_1030_, sizeof(void*)*3, v___x_1028_);
lean_ctor_set_float(v___x_1030_, sizeof(void*)*3 + 8, v___x_1028_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*3 + 16, v___x_1012_);
v___x_1031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_a_1022_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v_a_1024_);
v___x_1034_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1030_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
lean_ctor_set(v___x_1034_, 2, v_data_1025_);
v___x_1035_ = lean_array_push(v_snd_1014_, v___x_1034_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1035_);
lean_ctor_set(v___x_1016_, 0, v___x_1026_);
v___x_1037_ = v___x_1016_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
size_t v___x_1038_; size_t v___x_1039_; 
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_add(v_i_1007_, v___x_1038_);
v_i_1007_ = v___x_1039_;
v_b_1008_ = v___x_1037_;
goto _start;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_1022_);
lean_del_object(v___x_1016_);
lean_dec(v_snd_1014_);
v_a_1042_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1023_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1023_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_del_object(v___x_1016_);
lean_dec(v_snd_1014_);
v_a_1050_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1021_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1021_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1060_, lean_object* v_sz_1061_, lean_object* v_i_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
size_t v_sz_boxed_1067_; size_t v_i_boxed_1068_; lean_object* v_res_1069_; 
v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1061_);
lean_dec(v_sz_1061_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1062_);
lean_dec(v_i_1062_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1060_, v_sz_boxed_1067_, v_i_boxed_1068_, v_b_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec_ref(v_as_1060_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(lean_object* v_as_1070_, size_t v_sz_1071_, size_t v_i_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_usize_dec_lt(v_i_1072_, v_sz_1071_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_b_1073_);
return v___x_1080_;
}
else
{
lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1125_; 
v_snd_1081_ = lean_ctor_get(v_b_1073_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_b_1073_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_b_1073_, 0);
lean_dec(v_unused_1126_);
v___x_1083_ = v_b_1073_;
v_isShared_1084_ = v_isSharedCheck_1125_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_dec(v_b_1073_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1125_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_a_1085_; lean_object* v_keys_1086_; lean_object* v_origin_1087_; lean_object* v___x_1088_; 
v_a_1085_ = lean_array_uget_borrowed(v_as_1070_, v_i_1072_);
v_keys_1086_ = lean_ctor_get(v_a_1085_, 0);
v_origin_1087_ = lean_ctor_get(v_a_1085_, 4);
lean_inc_ref(v_origin_1087_);
v___x_1088_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_1087_, v___y_1077_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
lean_inc_ref(v_keys_1086_);
v___x_1090_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1086_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v_data_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; double v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v_data_1092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1093_ = lean_box(0);
v___x_1094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1095_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1097_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1097_, 0, v___x_1094_);
lean_ctor_set(v___x_1097_, 1, v___x_1093_);
lean_ctor_set(v___x_1097_, 2, v___x_1096_);
lean_ctor_set_float(v___x_1097_, sizeof(void*)*3, v___x_1095_);
lean_ctor_set_float(v___x_1097_, sizeof(void*)*3 + 8, v___x_1095_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*3 + 16, v___x_1079_);
v___x_1098_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1089_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_a_1091_);
v___x_1101_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1097_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
lean_ctor_set(v___x_1101_, 2, v_data_1092_);
v___x_1102_ = lean_array_push(v_snd_1081_, v___x_1101_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1102_);
lean_ctor_set(v___x_1083_, 0, v___x_1093_);
v___x_1104_ = v___x_1083_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_add(v_i_1072_, v___x_1105_);
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1070_, v_sz_1071_, v___x_1106_, v___x_1104_, v___y_1076_, v___y_1077_);
return v___x_1107_;
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_a_1089_);
lean_del_object(v___x_1083_);
lean_dec(v_snd_1081_);
v_a_1109_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1090_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1090_);
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
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1083_);
lean_dec(v_snd_1081_);
v_a_1117_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1088_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1088_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1___boxed(lean_object* v_as_1127_, lean_object* v_sz_1128_, lean_object* v_i_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
size_t v_sz_boxed_1136_; size_t v_i_boxed_1137_; lean_object* v_res_1138_; 
v_sz_boxed_1136_ = lean_unbox_usize(v_sz_1128_);
lean_dec(v_sz_1128_);
v_i_boxed_1137_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_as_1127_, v_sz_boxed_1136_, v_i_boxed_1137_, v_b_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec_ref(v_as_1127_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(lean_object* v_t_1139_, lean_object* v_init_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_root_1146_; lean_object* v_tail_1147_; lean_object* v___x_1148_; 
v_root_1146_ = lean_ctor_get(v_t_1139_, 0);
v_tail_1147_ = lean_ctor_get(v_t_1139_, 1);
lean_inc_ref(v_init_1140_);
v___x_1148_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_1140_, v_root_1146_, v_init_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec_ref(v_init_1140_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1185_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1185_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1185_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
if (lean_obj_tag(v_a_1149_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; 
v_a_1153_ = lean_ctor_get(v_a_1149_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v_a_1149_, 1);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_a_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; size_t v_sz_1160_; size_t v___x_1161_; lean_object* v___x_1162_; 
lean_del_object(v___x_1151_);
v_a_1157_ = lean_ctor_get(v_a_1149_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v_a_1149_, 1);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v_a_1157_);
v_sz_1160_ = lean_array_size(v_tail_1147_);
v___x_1161_ = ((size_t)0ULL);
v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_tail_1147_, v_sz_1160_, v___x_1161_, v___x_1159_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1176_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1176_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1176_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fst_1167_; 
v_fst_1167_ = lean_ctor_get(v_a_1163_, 0);
if (lean_obj_tag(v_fst_1167_) == 0)
{
lean_object* v_snd_1168_; lean_object* v___x_1170_; 
v_snd_1168_ = lean_ctor_get(v_a_1163_, 1);
lean_inc(v_snd_1168_);
lean_dec(v_a_1163_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_snd_1168_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_snd_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
else
{
lean_object* v_val_1172_; lean_object* v___x_1174_; 
lean_inc_ref(v_fst_1167_);
lean_dec(v_a_1163_);
v_val_1172_ = lean_ctor_get(v_fst_1167_, 0);
lean_inc(v_val_1172_);
lean_dec_ref_known(v_fst_1167_, 1);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_val_1172_);
v___x_1174_ = v___x_1165_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_val_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1162_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1162_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1148_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1148_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0___boxed(lean_object* v_t_1194_, lean_object* v_init_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_t_1194_, v_init_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_t_1194_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(lean_object* v_thms_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = l_Lean_PersistentArray_isEmpty___redArg(v_thms_1202_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v_data_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v_data_1210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1211_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_thms_1202_, v_data_1210_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_a_1212_);
lean_ctor_set(v___x_1216_, 1, v___x_1209_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1221_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1211_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1211_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3));
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary___boxed(lean_object* v_thms_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thms_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_thms_1231_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(lean_object* v_as_1238_, size_t v_sz_1239_, size_t v_i_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1238_, v_sz_1239_, v_i_1240_, v_b_1241_, v___y_1244_, v___y_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1248_, lean_object* v_sz_1249_, lean_object* v_i_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1249_);
lean_dec(v_sz_1249_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(v_as_1248_, v_sz_boxed_1257_, v_i_boxed_1258_, v_b_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_as_1248_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1260_, size_t v_sz_1261_, size_t v_i_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_1260_, v_sz_1261_, v_i_1262_, v_b_1263_, v___y_1266_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1270_, lean_object* v_sz_1271_, lean_object* v_i_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
size_t v_sz_boxed_1279_; size_t v_i_boxed_1280_; lean_object* v_res_1281_; 
v_sz_boxed_1279_ = lean_unbox_usize(v_sz_1271_);
lean_dec(v_sz_1271_);
v_i_boxed_1280_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_res_1281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(v_as_1270_, v_sz_boxed_1279_, v_i_boxed_1280_, v_b_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v_as_1270_);
return v_res_1281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_mkDiagMessages___lam__0(lean_object* v_x_1282_){
_start:
{
uint8_t v___x_1283_; 
v___x_1283_ = 1;
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___lam__0___boxed(lean_object* v_x_1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l_Lean_Meta_Simp_mkDiagMessages___lam__0(v_x_1284_);
lean_dec(v_x_1284_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__6));
v___x_1296_ = l_Lean_MessageData_ofFormat(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages(lean_object* v_diag_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_usedThmCounter_1303_; lean_object* v_triedThmCounter_1304_; lean_object* v_congrThmCounter_1305_; lean_object* v_thmsWithBadKeys_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_usedThmCounter_1303_ = lean_ctor_get(v_diag_1297_, 0);
v_triedThmCounter_1304_ = lean_ctor_get(v_diag_1297_, 1);
v_congrThmCounter_1305_ = lean_ctor_get(v_diag_1297_, 2);
v_thmsWithBadKeys_1306_ = lean_ctor_get(v_diag_1297_, 3);
v___x_1307_ = lean_box(0);
v___x_1308_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_usedThmCounter_1303_, v___x_1307_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
lean_inc_ref(v_usedThmCounter_1303_);
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v_usedThmCounter_1303_);
v___x_1311_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_triedThmCounter_1304_, v___x_1310_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec_ref_known(v___x_1310_, 1);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___f_1313_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__0));
v___x_1314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1315_ = l_Lean_Meta_mkDiagSummary(v___x_1314_, v_congrThmCounter_1305_, v___f_1313_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1361_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1361_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1361_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; 
v___x_1320_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thmsWithBadKeys_1306_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1352_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1352_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1352_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___y_1326_; uint8_t v___y_1343_; uint8_t v___x_1350_; 
v___x_1350_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1309_);
if (v___x_1350_ == 0)
{
v___y_1343_ = v___x_1350_;
goto v___jp_1342_;
}
else
{
uint8_t v___x_1351_; 
v___x_1351_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1312_);
v___y_1343_ = v___x_1351_;
goto v___jp_1342_;
}
v___jp_1325_:
{
uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1327_ = 1;
v___x_1328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1329_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__1));
v___x_1330_ = l_Lean_Meta_appendSection(v___x_1328_, v___x_1314_, v___x_1329_, v_a_1309_, v___x_1327_);
v___x_1331_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__2));
v___x_1332_ = l_Lean_Meta_appendSection(v___x_1330_, v___x_1314_, v___x_1331_, v_a_1312_, v___x_1327_);
v___x_1333_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__3));
v___x_1334_ = l_Lean_Meta_appendSection(v___x_1332_, v___x_1314_, v___x_1333_, v_a_1316_, v___x_1327_);
v___x_1335_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__4));
v___x_1336_ = l_Lean_Meta_appendSection(v___x_1334_, v___x_1314_, v___x_1335_, v_a_1321_, v___y_1326_);
v___x_1337_ = lean_obj_once(&l_Lean_Meta_Simp_mkDiagMessages___closed__7, &l_Lean_Meta_Simp_mkDiagMessages___closed__7_once, _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7);
v___x_1338_ = lean_array_push(v___x_1336_, v___x_1337_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1338_);
v___x_1340_ = v___x_1323_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
v___jp_1342_:
{
if (v___y_1343_ == 0)
{
lean_del_object(v___x_1318_);
v___y_1326_ = v___y_1343_;
goto v___jp_1325_;
}
else
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1316_);
if (v___x_1344_ == 0)
{
lean_del_object(v___x_1318_);
v___y_1326_ = v___x_1344_;
goto v___jp_1325_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1321_);
if (v___x_1345_ == 0)
{
lean_del_object(v___x_1318_);
v___y_1326_ = v___x_1345_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_del_object(v___x_1323_);
lean_dec(v_a_1321_);
lean_dec(v_a_1316_);
lean_dec(v_a_1312_);
lean_dec(v_a_1309_);
v___x_1346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1346_);
v___x_1348_ = v___x_1318_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_del_object(v___x_1318_);
lean_dec(v_a_1316_);
lean_dec(v_a_1312_);
lean_dec(v_a_1309_);
v_a_1353_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1320_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1320_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1312_);
lean_dec(v_a_1309_);
v_a_1362_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1315_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1315_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1309_);
v_a_1370_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1311_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1311_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1308_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1308_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___boxed(lean_object* v_diag_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_Simp_mkDiagMessages(v_diag_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec_ref(v_diag_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_1401_, uint8_t v_suppressElabErrors_1402_, lean_object* v_x_1403_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 1)
{
lean_object* v_pre_1404_; 
v_pre_1404_ = lean_ctor_get(v_x_1403_, 0);
switch(lean_obj_tag(v_pre_1404_))
{
case 1:
{
lean_object* v_pre_1405_; 
v_pre_1405_ = lean_ctor_get(v_pre_1404_, 0);
switch(lean_obj_tag(v_pre_1405_))
{
case 0:
{
lean_object* v_str_1406_; lean_object* v_str_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_str_1406_ = lean_ctor_get(v_x_1403_, 1);
v_str_1407_ = lean_ctor_get(v_pre_1404_, 1);
v___x_1408_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1409_ = lean_string_dec_eq(v_str_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1411_ = lean_string_dec_eq(v_str_1407_, v___x_1410_);
if (v___x_1411_ == 0)
{
return v___y_1401_;
}
else
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1413_ = lean_string_dec_eq(v_str_1406_, v___x_1412_);
if (v___x_1413_ == 0)
{
return v___y_1401_;
}
else
{
return v_suppressElabErrors_1402_;
}
}
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1415_ = lean_string_dec_eq(v_str_1406_, v___x_1414_);
if (v___x_1415_ == 0)
{
return v___y_1401_;
}
else
{
return v_suppressElabErrors_1402_;
}
}
}
case 1:
{
lean_object* v_pre_1416_; 
v_pre_1416_ = lean_ctor_get(v_pre_1405_, 0);
if (lean_obj_tag(v_pre_1416_) == 0)
{
lean_object* v_str_1417_; lean_object* v_str_1418_; lean_object* v_str_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_str_1417_ = lean_ctor_get(v_x_1403_, 1);
v_str_1418_ = lean_ctor_get(v_pre_1404_, 1);
v_str_1419_ = lean_ctor_get(v_pre_1405_, 1);
v___x_1420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1421_ = lean_string_dec_eq(v_str_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
return v___y_1401_;
}
else
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1423_ = lean_string_dec_eq(v_str_1418_, v___x_1422_);
if (v___x_1423_ == 0)
{
return v___y_1401_;
}
else
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_1425_ = lean_string_dec_eq(v_str_1417_, v___x_1424_);
if (v___x_1425_ == 0)
{
return v___y_1401_;
}
else
{
return v_suppressElabErrors_1402_;
}
}
}
}
else
{
return v___y_1401_;
}
}
default: 
{
return v___y_1401_;
}
}
}
case 0:
{
lean_object* v_str_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_str_1426_ = lean_ctor_get(v_x_1403_, 1);
v___x_1427_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_1428_ = lean_string_dec_eq(v_str_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
return v___y_1401_;
}
else
{
return v_suppressElabErrors_1402_;
}
}
default: 
{
return v___y_1401_;
}
}
}
else
{
return v___y_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_1429_, lean_object* v_suppressElabErrors_1430_, lean_object* v_x_1431_){
_start:
{
uint8_t v___y_6432__boxed_1432_; uint8_t v_suppressElabErrors_boxed_1433_; uint8_t v_res_1434_; lean_object* v_r_1435_; 
v___y_6432__boxed_1432_ = lean_unbox(v___y_1429_);
v_suppressElabErrors_boxed_1433_ = lean_unbox(v_suppressElabErrors_1430_);
v_res_1434_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(v___y_6432__boxed_1432_, v_suppressElabErrors_boxed_1433_, v_x_1431_);
lean_dec(v_x_1431_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_1436_, lean_object* v_opt_1437_){
_start:
{
lean_object* v_name_1438_; lean_object* v_defValue_1439_; lean_object* v_map_1440_; lean_object* v___x_1441_; 
v_name_1438_ = lean_ctor_get(v_opt_1437_, 0);
v_defValue_1439_ = lean_ctor_get(v_opt_1437_, 1);
v_map_1440_ = lean_ctor_get(v_opts_1436_, 0);
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1440_, v_name_1438_);
if (lean_obj_tag(v___x_1441_) == 0)
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_unbox(v_defValue_1439_);
return v___x_1442_;
}
else
{
lean_object* v_val_1443_; 
v_val_1443_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_val_1443_);
lean_dec_ref_known(v___x_1441_, 1);
if (lean_obj_tag(v_val_1443_) == 1)
{
uint8_t v_v_1444_; 
v_v_1444_ = lean_ctor_get_uint8(v_val_1443_, 0);
lean_dec_ref_known(v_val_1443_, 0);
return v_v_1444_;
}
else
{
uint8_t v___x_1445_; 
lean_dec(v_val_1443_);
v___x_1445_ = lean_unbox(v_defValue_1439_);
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_1446_, lean_object* v_opt_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_opts_1446_, v_opt_1447_);
lean_dec_ref(v_opt_1447_);
lean_dec_ref(v_opts_1446_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v_env_1457_; lean_object* v___x_1458_; lean_object* v_mctx_1459_; lean_object* v_lctx_1460_; lean_object* v_options_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1456_ = lean_st_ref_get(v___y_1454_);
v_env_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = lean_st_ref_get(v___y_1452_);
v_mctx_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc_ref(v_mctx_1459_);
lean_dec(v___x_1458_);
v_lctx_1460_ = lean_ctor_get(v___y_1451_, 2);
v_options_1461_ = lean_ctor_get(v___y_1453_, 2);
lean_inc_ref(v_options_1461_);
lean_inc_ref(v_lctx_1460_);
v___x_1462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1462_, 0, v_env_1457_);
lean_ctor_set(v___x_1462_, 1, v_mctx_1459_);
lean_ctor_set(v___x_1462_, 2, v_lctx_1460_);
lean_ctor_set(v___x_1462_, 3, v_options_1461_);
v___x_1463_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v_msgData_1450_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v_msgData_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(lean_object* v_ref_1472_, lean_object* v_msgData_1473_, uint8_t v_severity_1474_, uint8_t v_isSilent_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___y_1482_; uint8_t v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; uint8_t v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1518_; lean_object* v___y_1519_; uint8_t v___y_1520_; uint8_t v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1543_; uint8_t v___y_1544_; uint8_t v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1554_; uint8_t v___y_1555_; uint8_t v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1560_; uint8_t v___x_1565_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v___y_1572_; uint8_t v___y_1573_; uint8_t v___y_1575_; uint8_t v___x_1590_; 
v___x_1565_ = 2;
v___x_1590_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1474_, v___x_1565_);
if (v___x_1590_ == 0)
{
v___y_1575_ = v___x_1590_;
goto v___jp_1574_;
}
else
{
uint8_t v___x_1591_; 
lean_inc_ref(v_msgData_1473_);
v___x_1591_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1473_);
v___y_1575_ = v___x_1591_;
goto v___jp_1574_;
}
v___jp_1481_:
{
lean_object* v___x_1491_; lean_object* v_currNamespace_1492_; lean_object* v_openDecls_1493_; lean_object* v_env_1494_; lean_object* v_nextMacroScope_1495_; lean_object* v_ngen_1496_; lean_object* v_auxDeclNGen_1497_; lean_object* v_traceState_1498_; lean_object* v_cache_1499_; lean_object* v_messages_1500_; lean_object* v_infoState_1501_; lean_object* v_snapshotTasks_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1516_; 
v___x_1491_ = lean_st_ref_take(v___y_1490_);
v_currNamespace_1492_ = lean_ctor_get(v___y_1489_, 6);
v_openDecls_1493_ = lean_ctor_get(v___y_1489_, 7);
v_env_1494_ = lean_ctor_get(v___x_1491_, 0);
v_nextMacroScope_1495_ = lean_ctor_get(v___x_1491_, 1);
v_ngen_1496_ = lean_ctor_get(v___x_1491_, 2);
v_auxDeclNGen_1497_ = lean_ctor_get(v___x_1491_, 3);
v_traceState_1498_ = lean_ctor_get(v___x_1491_, 4);
v_cache_1499_ = lean_ctor_get(v___x_1491_, 5);
v_messages_1500_ = lean_ctor_get(v___x_1491_, 6);
v_infoState_1501_ = lean_ctor_get(v___x_1491_, 7);
v_snapshotTasks_1502_ = lean_ctor_get(v___x_1491_, 8);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1504_ = v___x_1491_;
v_isShared_1505_ = v_isSharedCheck_1516_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_snapshotTasks_1502_);
lean_inc(v_infoState_1501_);
lean_inc(v_messages_1500_);
lean_inc(v_cache_1499_);
lean_inc(v_traceState_1498_);
lean_inc(v_auxDeclNGen_1497_);
lean_inc(v_ngen_1496_);
lean_inc(v_nextMacroScope_1495_);
lean_inc(v_env_1494_);
lean_dec(v___x_1491_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1516_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_inc(v_openDecls_1493_);
lean_inc(v_currNamespace_1492_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_currNamespace_1492_);
lean_ctor_set(v___x_1506_, 1, v_openDecls_1493_);
v___x_1507_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v___y_1486_);
lean_inc_ref(v___y_1488_);
lean_inc_ref(v___y_1484_);
v___x_1508_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1508_, 0, v___y_1484_);
lean_ctor_set(v___x_1508_, 1, v___y_1482_);
lean_ctor_set(v___x_1508_, 2, v___y_1485_);
lean_ctor_set(v___x_1508_, 3, v___y_1488_);
lean_ctor_set(v___x_1508_, 4, v___x_1507_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*5, v___y_1483_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*5 + 1, v___y_1487_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*5 + 2, v_isSilent_1475_);
v___x_1509_ = l_Lean_MessageLog_add(v___x_1508_, v_messages_1500_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 6, v___x_1509_);
v___x_1511_ = v___x_1504_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_env_1494_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_nextMacroScope_1495_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_ngen_1496_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_auxDeclNGen_1497_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_traceState_1498_);
lean_ctor_set(v_reuseFailAlloc_1515_, 5, v_cache_1499_);
lean_ctor_set(v_reuseFailAlloc_1515_, 6, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1515_, 7, v_infoState_1501_);
lean_ctor_set(v_reuseFailAlloc_1515_, 8, v_snapshotTasks_1502_);
v___x_1511_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_st_ref_set(v___y_1490_, v___x_1511_);
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
}
v___jp_1517_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1541_; 
v___x_1526_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1473_);
v___x_1527_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v___x_1526_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1541_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1541_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_inc_ref_n(v___y_1522_, 2);
v___x_1532_ = l_Lean_FileMap_toPosition(v___y_1522_, v___y_1519_);
lean_dec(v___y_1519_);
v___x_1533_ = l_Lean_FileMap_toPosition(v___y_1522_, v___y_1525_);
lean_dec(v___y_1525_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
v___x_1535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
if (v___y_1520_ == 0)
{
lean_del_object(v___x_1530_);
lean_dec_ref(v___y_1518_);
v___y_1482_ = v___x_1532_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1523_;
v___y_1485_ = v___x_1534_;
v___y_1486_ = v_a_1528_;
v___y_1487_ = v___y_1524_;
v___y_1488_ = v___x_1535_;
v___y_1489_ = v___y_1478_;
v___y_1490_ = v___y_1479_;
goto v___jp_1481_;
}
else
{
uint8_t v___x_1536_; 
lean_inc(v_a_1528_);
v___x_1536_ = l_Lean_MessageData_hasTag(v___y_1518_, v_a_1528_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_dec_ref_known(v___x_1534_, 1);
lean_dec_ref(v___x_1532_);
lean_dec(v_a_1528_);
v___x_1537_ = lean_box(0);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1537_);
v___x_1539_ = v___x_1530_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
else
{
lean_del_object(v___x_1530_);
v___y_1482_ = v___x_1532_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1523_;
v___y_1485_ = v___x_1534_;
v___y_1486_ = v_a_1528_;
v___y_1487_ = v___y_1524_;
v___y_1488_ = v___x_1535_;
v___y_1489_ = v___y_1478_;
v___y_1490_ = v___y_1479_;
goto v___jp_1481_;
}
}
}
}
v___jp_1542_:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Syntax_getTailPos_x3f(v___y_1548_, v___y_1544_);
lean_dec(v___y_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_inc(v___y_1550_);
v___y_1518_ = v___y_1543_;
v___y_1519_ = v___y_1550_;
v___y_1520_ = v___y_1545_;
v___y_1521_ = v___y_1544_;
v___y_1522_ = v___y_1546_;
v___y_1523_ = v___y_1547_;
v___y_1524_ = v___y_1549_;
v___y_1525_ = v___y_1550_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___y_1518_ = v___y_1543_;
v___y_1519_ = v___y_1550_;
v___y_1520_ = v___y_1545_;
v___y_1521_ = v___y_1544_;
v___y_1522_ = v___y_1546_;
v___y_1523_ = v___y_1547_;
v___y_1524_ = v___y_1549_;
v___y_1525_ = v_val_1552_;
goto v___jp_1517_;
}
}
v___jp_1553_:
{
lean_object* v_ref_1561_; lean_object* v___x_1562_; 
v_ref_1561_ = l_Lean_replaceRef(v_ref_1472_, v___y_1557_);
v___x_1562_ = l_Lean_Syntax_getPos_x3f(v_ref_1561_, v___y_1556_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___y_1543_ = v___y_1554_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1555_;
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1559_;
v___y_1548_ = v_ref_1561_;
v___y_1549_ = v___y_1560_;
v___y_1550_ = v___x_1563_;
goto v___jp_1542_;
}
else
{
lean_object* v_val_1564_; 
v_val_1564_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v___x_1562_, 1);
v___y_1543_ = v___y_1554_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1555_;
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1559_;
v___y_1548_ = v_ref_1561_;
v___y_1549_ = v___y_1560_;
v___y_1550_ = v_val_1564_;
goto v___jp_1542_;
}
}
v___jp_1566_:
{
if (v___y_1573_ == 0)
{
v___y_1554_ = v___y_1569_;
v___y_1555_ = v___y_1567_;
v___y_1556_ = v___y_1572_;
v___y_1557_ = v___y_1568_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v_severity_1474_;
goto v___jp_1553_;
}
else
{
v___y_1554_ = v___y_1569_;
v___y_1555_ = v___y_1567_;
v___y_1556_ = v___y_1572_;
v___y_1557_ = v___y_1568_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___x_1565_;
goto v___jp_1553_;
}
}
v___jp_1574_:
{
if (v___y_1575_ == 0)
{
lean_object* v_fileName_1576_; lean_object* v_fileMap_1577_; lean_object* v_options_1578_; lean_object* v_ref_1579_; uint8_t v_suppressElabErrors_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___f_1583_; uint8_t v___x_1584_; uint8_t v___x_1585_; 
v_fileName_1576_ = lean_ctor_get(v___y_1478_, 0);
v_fileMap_1577_ = lean_ctor_get(v___y_1478_, 1);
v_options_1578_ = lean_ctor_get(v___y_1478_, 2);
v_ref_1579_ = lean_ctor_get(v___y_1478_, 5);
v_suppressElabErrors_1580_ = lean_ctor_get_uint8(v___y_1478_, sizeof(void*)*14 + 1);
v___x_1581_ = lean_box(v___y_1575_);
v___x_1582_ = lean_box(v_suppressElabErrors_1580_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1583_, 0, v___x_1581_);
lean_closure_set(v___f_1583_, 1, v___x_1582_);
v___x_1584_ = 1;
v___x_1585_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1474_, v___x_1584_);
if (v___x_1585_ == 0)
{
v___y_1567_ = v_suppressElabErrors_1580_;
v___y_1568_ = v_ref_1579_;
v___y_1569_ = v___f_1583_;
v___y_1570_ = v_fileMap_1577_;
v___y_1571_ = v_fileName_1576_;
v___y_1572_ = v___y_1575_;
v___y_1573_ = v___x_1585_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = l_Lean_warningAsError;
v___x_1587_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_options_1578_, v___x_1586_);
v___y_1567_ = v_suppressElabErrors_1580_;
v___y_1568_ = v_ref_1579_;
v___y_1569_ = v___f_1583_;
v___y_1570_ = v_fileMap_1577_;
v___y_1571_ = v_fileName_1576_;
v___y_1572_ = v___y_1575_;
v___y_1573_ = v___x_1587_;
goto v___jp_1566_;
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v_msgData_1473_);
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1592_, lean_object* v_msgData_1593_, lean_object* v_severity_1594_, lean_object* v_isSilent_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_severity_boxed_1601_; uint8_t v_isSilent_boxed_1602_; lean_object* v_res_1603_; 
v_severity_boxed_1601_ = lean_unbox(v_severity_1594_);
v_isSilent_boxed_1602_ = lean_unbox(v_isSilent_1595_);
v_res_1603_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_1592_, v_msgData_1593_, v_severity_boxed_1601_, v_isSilent_boxed_1602_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v_ref_1592_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(lean_object* v_msgData_1604_, uint8_t v_severity_1605_, uint8_t v_isSilent_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_ref_1612_; lean_object* v___x_1613_; 
v_ref_1612_ = lean_ctor_get(v___y_1609_, 5);
v___x_1613_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_1612_, v_msgData_1604_, v_severity_1605_, v_isSilent_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0___boxed(lean_object* v_msgData_1614_, lean_object* v_severity_1615_, lean_object* v_isSilent_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v_severity_boxed_1622_; uint8_t v_isSilent_boxed_1623_; lean_object* v_res_1624_; 
v_severity_boxed_1622_ = lean_unbox(v_severity_1615_);
v_isSilent_boxed_1623_ = lean_unbox(v_isSilent_1616_);
v_res_1624_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(v_msgData_1614_, v_severity_boxed_1622_, v_isSilent_boxed_1623_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(lean_object* v_msgData_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = 0;
v___x_1632_ = 0;
v___x_1633_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(v_msgData_1625_, v___x_1631_, v___x_1632_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0___boxed(lean_object* v_msgData_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(v_msgData_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1640_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Meta_Simp_reportDiag___lam__0___closed__1));
v___x_1645_ = l_Lean_MessageData_ofFormat(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___lam__0(lean_object* v_diag_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Meta_Simp_mkDiagMessages(v_diag_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1672_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1672_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1672_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1657_ = lean_array_get_size(v_a_1653_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_nat_dec_eq(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; double v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_del_object(v___x_1655_);
v___x_1660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1664_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1664_, 0, v___x_1660_);
lean_ctor_set(v___x_1664_, 1, v___x_1661_);
lean_ctor_set(v___x_1664_, 2, v___x_1663_);
lean_ctor_set_float(v___x_1664_, sizeof(void*)*3, v___x_1662_);
lean_ctor_set_float(v___x_1664_, sizeof(void*)*3 + 8, v___x_1662_);
lean_ctor_set_uint8(v___x_1664_, sizeof(void*)*3 + 16, v___x_1659_);
v___x_1665_ = lean_obj_once(&l_Lean_Meta_Simp_reportDiag___lam__0___closed__2, &l_Lean_Meta_Simp_reportDiag___lam__0___closed__2_once, _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2);
v___x_1666_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
lean_ctor_set(v___x_1666_, 2, v_a_1653_);
v___x_1667_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(v___x_1666_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
lean_dec(v_a_1653_);
v___x_1668_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1668_);
v___x_1670_ = v___x_1655_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_a_1673_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1652_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1652_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___lam__0___boxed(lean_object* v_diag_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Meta_Simp_reportDiag___lam__0(v_diag_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v_diag_1681_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(lean_object* v___y_1688_, uint8_t v_isExporting_1689_, lean_object* v___x_1690_, lean_object* v___y_1691_, lean_object* v___x_1692_, lean_object* v_a_x3f_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v_env_1696_; lean_object* v_nextMacroScope_1697_; lean_object* v_ngen_1698_; lean_object* v_auxDeclNGen_1699_; lean_object* v_traceState_1700_; lean_object* v_messages_1701_; lean_object* v_infoState_1702_; lean_object* v_snapshotTasks_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1728_; 
v___x_1695_ = lean_st_ref_take(v___y_1688_);
v_env_1696_ = lean_ctor_get(v___x_1695_, 0);
v_nextMacroScope_1697_ = lean_ctor_get(v___x_1695_, 1);
v_ngen_1698_ = lean_ctor_get(v___x_1695_, 2);
v_auxDeclNGen_1699_ = lean_ctor_get(v___x_1695_, 3);
v_traceState_1700_ = lean_ctor_get(v___x_1695_, 4);
v_messages_1701_ = lean_ctor_get(v___x_1695_, 6);
v_infoState_1702_ = lean_ctor_get(v___x_1695_, 7);
v_snapshotTasks_1703_ = lean_ctor_get(v___x_1695_, 8);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v___x_1695_, 5);
lean_dec(v_unused_1729_);
v___x_1705_ = v___x_1695_;
v_isShared_1706_ = v_isSharedCheck_1728_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_snapshotTasks_1703_);
lean_inc(v_infoState_1702_);
lean_inc(v_messages_1701_);
lean_inc(v_traceState_1700_);
lean_inc(v_auxDeclNGen_1699_);
lean_inc(v_ngen_1698_);
lean_inc(v_nextMacroScope_1697_);
lean_inc(v_env_1696_);
lean_dec(v___x_1695_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1728_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = l_Lean_Environment_setExporting(v_env_1696_, v_isExporting_1689_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 5, v___x_1690_);
lean_ctor_set(v___x_1705_, 0, v___x_1707_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_nextMacroScope_1697_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_ngen_1698_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_auxDeclNGen_1699_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v_traceState_1700_);
lean_ctor_set(v_reuseFailAlloc_1727_, 5, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1727_, 6, v_messages_1701_);
lean_ctor_set(v_reuseFailAlloc_1727_, 7, v_infoState_1702_);
lean_ctor_set(v_reuseFailAlloc_1727_, 8, v_snapshotTasks_1703_);
v___x_1709_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_mctx_1712_; lean_object* v_zetaDeltaFVarIds_1713_; lean_object* v_postponed_1714_; lean_object* v_diag_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
v___x_1710_ = lean_st_ref_set(v___y_1688_, v___x_1709_);
v___x_1711_ = lean_st_ref_take(v___y_1691_);
v_mctx_1712_ = lean_ctor_get(v___x_1711_, 0);
v_zetaDeltaFVarIds_1713_ = lean_ctor_get(v___x_1711_, 2);
v_postponed_1714_ = lean_ctor_get(v___x_1711_, 3);
v_diag_1715_ = lean_ctor_get(v___x_1711_, 4);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v___x_1711_, 1);
lean_dec(v_unused_1726_);
v___x_1717_ = v___x_1711_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_diag_1715_);
lean_inc(v_postponed_1714_);
lean_inc(v_zetaDeltaFVarIds_1713_);
lean_inc(v_mctx_1712_);
lean_dec(v___x_1711_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1692_);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_mctx_1712_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_zetaDeltaFVarIds_1713_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_postponed_1714_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_diag_1715_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_st_ref_set(v___y_1691_, v___x_1720_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_1730_, lean_object* v_isExporting_1731_, lean_object* v___x_1732_, lean_object* v___y_1733_, lean_object* v___x_1734_, lean_object* v_a_x3f_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v_isExporting_boxed_1737_; lean_object* v_res_1738_; 
v_isExporting_boxed_1737_ = lean_unbox(v_isExporting_1731_);
v_res_1738_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1730_, v_isExporting_boxed_1737_, v___x_1732_, v___y_1733_, v___x_1734_, v_a_x3f_1735_);
lean_dec(v_a_x3f_1735_);
lean_dec(v___y_1733_);
lean_dec(v___y_1730_);
return v_res_1738_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1739_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
v___x_1745_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
lean_ctor_set(v___x_1745_, 2, v___x_1744_);
lean_ctor_set(v___x_1745_, 3, v___x_1744_);
lean_ctor_set(v___x_1745_, 4, v___x_1744_);
lean_ctor_set(v___x_1745_, 5, v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(lean_object* v_x_1746_, uint8_t v_isExporting_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v_env_1754_; uint8_t v_isExporting_1755_; lean_object* v___x_1821_; uint8_t v_isModule_1822_; 
v___x_1753_ = lean_st_ref_get(v___y_1751_);
v_env_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_ref(v_env_1754_);
lean_dec(v___x_1753_);
v_isExporting_1755_ = lean_ctor_get_uint8(v_env_1754_, sizeof(void*)*8);
v___x_1821_ = l_Lean_Environment_header(v_env_1754_);
lean_dec_ref(v_env_1754_);
v_isModule_1822_ = lean_ctor_get_uint8(v___x_1821_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1821_);
if (v_isModule_1822_ == 0)
{
lean_object* v___x_1823_; 
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
v___x_1823_ = lean_apply_5(v_x_1746_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, lean_box(0));
return v___x_1823_;
}
else
{
if (v_isExporting_1755_ == 0)
{
if (v_isExporting_1747_ == 0)
{
lean_object* v___x_1824_; 
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
v___x_1824_ = lean_apply_5(v_x_1746_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, lean_box(0));
return v___x_1824_;
}
else
{
goto v___jp_1756_;
}
}
else
{
if (v_isExporting_1747_ == 0)
{
goto v___jp_1756_;
}
else
{
lean_object* v___x_1825_; 
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
v___x_1825_ = lean_apply_5(v_x_1746_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, lean_box(0));
return v___x_1825_;
}
}
}
v___jp_1756_:
{
lean_object* v___x_1757_; lean_object* v_env_1758_; lean_object* v_nextMacroScope_1759_; lean_object* v_ngen_1760_; lean_object* v_auxDeclNGen_1761_; lean_object* v_traceState_1762_; lean_object* v_messages_1763_; lean_object* v_infoState_1764_; lean_object* v_snapshotTasks_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1819_; 
v___x_1757_ = lean_st_ref_take(v___y_1751_);
v_env_1758_ = lean_ctor_get(v___x_1757_, 0);
v_nextMacroScope_1759_ = lean_ctor_get(v___x_1757_, 1);
v_ngen_1760_ = lean_ctor_get(v___x_1757_, 2);
v_auxDeclNGen_1761_ = lean_ctor_get(v___x_1757_, 3);
v_traceState_1762_ = lean_ctor_get(v___x_1757_, 4);
v_messages_1763_ = lean_ctor_get(v___x_1757_, 6);
v_infoState_1764_ = lean_ctor_get(v___x_1757_, 7);
v_snapshotTasks_1765_ = lean_ctor_get(v___x_1757_, 8);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1757_, 5);
lean_dec(v_unused_1820_);
v___x_1767_ = v___x_1757_;
v_isShared_1768_ = v_isSharedCheck_1819_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snapshotTasks_1765_);
lean_inc(v_infoState_1764_);
lean_inc(v_messages_1763_);
lean_inc(v_traceState_1762_);
lean_inc(v_auxDeclNGen_1761_);
lean_inc(v_ngen_1760_);
lean_inc(v_nextMacroScope_1759_);
lean_inc(v_env_1758_);
lean_dec(v___x_1757_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1819_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = l_Lean_Environment_setExporting(v_env_1758_, v_isExporting_1747_);
v___x_1770_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 5, v___x_1770_);
lean_ctor_set(v___x_1767_, 0, v___x_1769_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_nextMacroScope_1759_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_ngen_1760_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_auxDeclNGen_1761_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_traceState_1762_);
lean_ctor_set(v_reuseFailAlloc_1818_, 5, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1818_, 6, v_messages_1763_);
lean_ctor_set(v_reuseFailAlloc_1818_, 7, v_infoState_1764_);
lean_ctor_set(v_reuseFailAlloc_1818_, 8, v_snapshotTasks_1765_);
v___x_1772_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_mctx_1775_; lean_object* v_zetaDeltaFVarIds_1776_; lean_object* v_postponed_1777_; lean_object* v_diag_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1816_; 
v___x_1773_ = lean_st_ref_set(v___y_1751_, v___x_1772_);
v___x_1774_ = lean_st_ref_take(v___y_1749_);
v_mctx_1775_ = lean_ctor_get(v___x_1774_, 0);
v_zetaDeltaFVarIds_1776_ = lean_ctor_get(v___x_1774_, 2);
v_postponed_1777_ = lean_ctor_get(v___x_1774_, 3);
v_diag_1778_ = lean_ctor_get(v___x_1774_, 4);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1774_, 1);
lean_dec(v_unused_1817_);
v___x_1780_ = v___x_1774_;
v_isShared_1781_ = v_isSharedCheck_1816_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_diag_1778_);
lean_inc(v_postponed_1777_);
lean_inc(v_zetaDeltaFVarIds_1776_);
lean_inc(v_mctx_1775_);
lean_dec(v___x_1774_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1816_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___x_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_mctx_1775_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_zetaDeltaFVarIds_1776_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_postponed_1777_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v_diag_1778_);
v___x_1784_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v_r_1786_; 
v___x_1785_ = lean_st_ref_set(v___y_1749_, v___x_1784_);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
v_r_1786_ = lean_apply_5(v_x_1746_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, lean_box(0));
if (lean_obj_tag(v_r_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1803_; 
v_a_1787_ = lean_ctor_get(v_r_1786_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_r_1786_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1789_ = v_r_1786_;
v_isShared_1790_ = v_isSharedCheck_1803_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v_r_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1803_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
lean_inc(v_a_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 1);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v___x_1793_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1751_, v_isExporting_1755_, v___x_1770_, v___y_1749_, v___x_1782_, v___x_1792_);
lean_dec_ref(v___x_1792_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1793_, 0);
lean_dec(v_unused_1801_);
v___x_1795_ = v___x_1793_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v___x_1793_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v_a_1787_);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1787_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1804_ = lean_ctor_get(v_r_1786_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v_r_1786_, 1);
v___x_1805_ = lean_box(0);
v___x_1806_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1751_, v_isExporting_1755_, v___x_1770_, v___y_1749_, v___x_1782_, v___x_1805_);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1806_, 0);
lean_dec(v_unused_1814_);
v___x_1808_ = v___x_1806_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v___x_1806_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 1);
lean_ctor_set(v___x_1808_, 0, v_a_1804_);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1804_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___boxed(lean_object* v_x_1826_, lean_object* v_isExporting_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
uint8_t v_isExporting_boxed_1833_; lean_object* v_res_1834_; 
v_isExporting_boxed_1833_ = lean_unbox(v_isExporting_1827_);
v_res_1834_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1826_, v_isExporting_boxed_1833_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(lean_object* v_x_1835_, uint8_t v_when_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
if (v_when_1836_ == 0)
{
lean_object* v___x_1842_; 
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
v___x_1842_ = lean_apply_5(v_x_1835_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, lean_box(0));
return v___x_1842_;
}
else
{
uint8_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = 0;
v___x_1844_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1835_, v___x_1843_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg___boxed(lean_object* v_x_1845_, lean_object* v_when_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
uint8_t v_when_boxed_1852_; lean_object* v_res_1853_; 
v_when_boxed_1852_ = lean_unbox(v_when_1846_);
v_res_1853_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v_x_1845_, v_when_boxed_1852_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag(lean_object* v_diag_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_isDiagnosticsEnabled___redArg(v_a_1857_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1873_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1873_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1873_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_unbox(v_a_1861_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_dec(v_a_1861_);
lean_dec_ref(v_diag_1854_);
v___x_1866_ = lean_box(0);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1866_);
v___x_1868_ = v___x_1863_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
else
{
lean_object* v___f_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; 
lean_del_object(v___x_1863_);
v___f_1870_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_reportDiag___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1870_, 0, v_diag_1854_);
v___x_1871_ = lean_unbox(v_a_1861_);
lean_dec(v_a_1861_);
v___x_1872_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v___f_1870_, v___x_1871_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
return v___x_1872_;
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_diag_1854_);
v_a_1874_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1860_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1860_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___boxed(lean_object* v_diag_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Meta_Simp_reportDiag(v_diag_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(lean_object* v_00_u03b1_1889_, lean_object* v_x_1890_, uint8_t v_isExporting_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1890_, v_isExporting_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_x_1899_, lean_object* v_isExporting_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
uint8_t v_isExporting_boxed_1906_; lean_object* v_res_1907_; 
v_isExporting_boxed_1906_ = lean_unbox(v_isExporting_1900_);
v_res_1907_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(v_00_u03b1_1898_, v_x_1899_, v_isExporting_boxed_1906_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(lean_object* v_00_u03b1_1908_, lean_object* v_x_1909_, uint8_t v_when_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v_x_1909_, v_when_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___boxed(lean_object* v_00_u03b1_1917_, lean_object* v_x_1918_, lean_object* v_when_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v_when_boxed_1925_; lean_object* v_res_1926_; 
v_when_boxed_1925_ = lean_unbox(v_when_1919_);
v_res_1926_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(v_00_u03b1_1917_, v_x_1918_, v_when_boxed_1925_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1926_;
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
