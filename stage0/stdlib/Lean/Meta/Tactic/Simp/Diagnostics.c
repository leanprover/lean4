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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_109_, lean_object* v_as_110_, size_t v_i_111_, size_t v_stop_112_, lean_object* v_b_113_){
_start:
{
lean_object* v_a_115_; lean_object* v___y_120_; uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_111_, v_stop_112_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_array_uget_borrowed(v_as_110_, v_i_111_);
switch(lean_obj_tag(v___x_123_))
{
case 0:
{
lean_object* v_key_124_; lean_object* v_val_125_; lean_object* v___x_126_; 
v_key_124_ = lean_ctor_get(v___x_123_, 0);
v_val_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_f_109_);
lean_inc(v_val_125_);
lean_inc(v_key_124_);
v___x_126_ = lean_apply_3(v_f_109_, v_b_113_, v_key_124_, v_val_125_);
v___y_120_ = v___x_126_;
goto v___jp_119_;
}
case 1:
{
lean_object* v_node_127_; lean_object* v___x_128_; 
v_node_127_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_node_127_);
lean_inc_ref(v_f_109_);
v___x_128_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_109_, v_node_127_, v_b_113_);
v___y_120_ = v___x_128_;
goto v___jp_119_;
}
default: 
{
v_a_115_ = v_b_113_;
goto v___jp_114_;
}
}
}
else
{
lean_object* v___x_129_; 
lean_dec_ref(v_f_109_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_b_113_);
return v___x_129_;
}
v___jp_114_:
{
size_t v___x_116_; size_t v___x_117_; 
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_add(v_i_111_, v___x_116_);
v_i_111_ = v___x_117_;
v_b_113_ = v_a_115_;
goto _start;
}
v___jp_119_:
{
if (lean_obj_tag(v___y_120_) == 0)
{
lean_dec_ref(v_f_109_);
return v___y_120_;
}
else
{
lean_object* v_a_121_; 
v_a_121_ = lean_ctor_get(v___y_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___y_120_, 1);
v_a_115_ = v_a_121_;
goto v___jp_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_f_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_object* v_es_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_146_; 
v_es_133_ = lean_ctor_get(v_x_131_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_146_ == 0)
{
v___x_135_ = v_x_131_;
v_isShared_136_ = v_isSharedCheck_146_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_es_133_);
lean_dec(v_x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_146_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get_size(v_es_133_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; 
lean_dec_ref(v_es_133_);
lean_dec_ref(v_f_130_);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 1);
lean_ctor_set(v___x_135_, 0, v_x_132_);
v___x_141_ = v___x_135_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_x_132_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
else
{
size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
lean_del_object(v___x_135_);
v___x_143_ = ((size_t)0ULL);
v___x_144_ = lean_usize_of_nat(v___x_138_);
v___x_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_130_, v_es_133_, v___x_143_, v___x_144_, v_x_132_);
lean_dec_ref(v_es_133_);
return v___x_145_;
}
}
}
else
{
lean_object* v_ks_147_; lean_object* v_vs_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_ks_147_ = lean_ctor_get(v_x_131_, 0);
lean_inc_ref(v_ks_147_);
v_vs_148_ = lean_ctor_get(v_x_131_, 1);
lean_inc_ref(v_vs_148_);
lean_dec_ref_known(v_x_131_, 2);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_130_, v_ks_147_, v_vs_148_, v___x_149_, v_x_132_);
lean_dec_ref(v_vs_148_);
lean_dec_ref(v_ks_147_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_151_, lean_object* v_as_152_, lean_object* v_i_153_, lean_object* v_stop_154_, lean_object* v_b_155_){
_start:
{
size_t v_i_boxed_156_; size_t v_stop_boxed_157_; lean_object* v_res_158_; 
v_i_boxed_156_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_stop_boxed_157_ = lean_unbox_usize(v_stop_154_);
lean_dec(v_stop_154_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_151_, v_as_152_, v_i_boxed_156_, v_stop_boxed_157_, v_b_155_);
lean_dec_ref(v_as_152_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(lean_object* v_map_159_, lean_object* v_init_160_, lean_object* v_f_161_){
_start:
{
lean_object* v___f_162_; lean_object* v___x_163_; lean_object* v_a_164_; 
v___f_162_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_162_, 0, v_f_161_);
lean_inc_ref(v_map_159_);
v___x_163_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v___f_162_, v_map_159_, v_init_160_);
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref(v___x_163_);
return v_a_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg___boxed(lean_object* v_map_165_, lean_object* v_init_166_, lean_object* v_f_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_165_, v_init_166_, v_f_167_);
lean_dec_ref(v_map_165_);
return v_res_168_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(lean_object* v_lt_169_, lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v_fst_174_; lean_object* v_snd_175_; uint8_t v___x_176_; 
v_fst_172_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_fst_172_);
v_snd_173_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_snd_173_);
lean_dec_ref(v_x_170_);
v_fst_174_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_fst_174_);
v_snd_175_ = lean_ctor_get(v_x_171_, 1);
lean_inc(v_snd_175_);
lean_dec_ref(v_x_171_);
v___x_176_ = lean_nat_dec_eq(v_snd_173_, v_snd_175_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
lean_dec(v_fst_174_);
lean_dec(v_fst_172_);
lean_dec_ref(v_lt_169_);
v___x_177_ = lean_nat_dec_lt(v_snd_175_, v_snd_173_);
lean_dec(v_snd_173_);
lean_dec(v_snd_175_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
lean_dec(v_snd_175_);
lean_dec(v_snd_173_);
v___x_178_ = lean_apply_2(v_lt_169_, v_fst_172_, v_fst_174_);
v___x_179_ = lean_unbox(v___x_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_lt_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_180_, v_x_181_, v_x_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(lean_object* v_lt_185_, lean_object* v_hi_186_, lean_object* v_pivot_187_, lean_object* v_as_188_, lean_object* v_i_189_, lean_object* v_k_190_){
_start:
{
uint8_t v___y_192_; uint8_t v___x_201_; 
v___x_201_ = lean_nat_dec_lt(v_k_190_, v_hi_186_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_k_190_);
lean_dec_ref(v_pivot_187_);
lean_dec_ref(v_lt_185_);
v___x_202_ = lean_array_fswap(v_as_188_, v_i_189_, v_hi_186_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_i_189_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; lean_object* v_fst_207_; lean_object* v_snd_208_; uint8_t v___x_209_; 
v___x_204_ = lean_array_fget_borrowed(v_as_188_, v_k_190_);
v_fst_205_ = lean_ctor_get(v___x_204_, 0);
v_snd_206_ = lean_ctor_get(v___x_204_, 1);
v_fst_207_ = lean_ctor_get(v_pivot_187_, 0);
v_snd_208_ = lean_ctor_get(v_pivot_187_, 1);
v___x_209_ = lean_nat_dec_eq(v_snd_206_, v_snd_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
v___x_210_ = lean_nat_dec_lt(v_snd_208_, v_snd_206_);
v___y_192_ = v___x_210_;
goto v___jp_191_;
}
else
{
lean_object* v___x_211_; uint8_t v___x_212_; 
lean_inc_ref(v_lt_185_);
lean_inc(v_fst_207_);
lean_inc(v_fst_205_);
v___x_211_ = lean_apply_2(v_lt_185_, v_fst_205_, v_fst_207_);
v___x_212_ = lean_unbox(v___x_211_);
v___y_192_ = v___x_212_;
goto v___jp_191_;
}
}
v___jp_191_:
{
if (v___y_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_k_190_, v___x_193_);
lean_dec(v_k_190_);
v_k_190_ = v___x_194_;
goto _start;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_196_ = lean_array_fswap(v_as_188_, v_i_189_, v_k_190_);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_add(v_i_189_, v___x_197_);
lean_dec(v_i_189_);
v___x_199_ = lean_nat_add(v_k_190_, v___x_197_);
lean_dec(v_k_190_);
v_as_188_ = v___x_196_;
v_i_189_ = v___x_198_;
v_k_190_ = v___x_199_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_lt_213_, lean_object* v_hi_214_, lean_object* v_pivot_215_, lean_object* v_as_216_, lean_object* v_i_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_213_, v_hi_214_, v_pivot_215_, v_as_216_, v_i_217_, v_k_218_);
lean_dec(v_hi_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(lean_object* v_lt_220_, lean_object* v_n_221_, lean_object* v_as_222_, lean_object* v_lo_223_, lean_object* v_hi_224_){
_start:
{
lean_object* v___y_226_; uint8_t v___x_236_; 
v___x_236_ = lean_nat_dec_lt(v_lo_223_, v_hi_224_);
if (v___x_236_ == 0)
{
lean_dec(v_lo_223_);
lean_dec_ref(v_lt_220_);
return v_as_222_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_mid_239_; lean_object* v___y_241_; lean_object* v___y_247_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_237_ = lean_nat_add(v_lo_223_, v_hi_224_);
v___x_238_ = lean_unsigned_to_nat(1u);
v_mid_239_ = lean_nat_shiftr(v___x_237_, v___x_238_);
lean_dec(v___x_237_);
v___x_252_ = lean_array_fget_borrowed(v_as_222_, v_mid_239_);
v___x_253_ = lean_array_fget_borrowed(v_as_222_, v_lo_223_);
lean_inc(v___x_253_);
lean_inc(v___x_252_);
lean_inc_ref(v_lt_220_);
v___x_254_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_220_, v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
v___y_247_ = v_as_222_;
goto v___jp_246_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = lean_array_fswap(v_as_222_, v_lo_223_, v_mid_239_);
v___y_247_ = v___x_255_;
goto v___jp_246_;
}
v___jp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = lean_array_fget_borrowed(v___y_241_, v_mid_239_);
v___x_243_ = lean_array_fget_borrowed(v___y_241_, v_hi_224_);
lean_inc(v___x_243_);
lean_inc(v___x_242_);
lean_inc_ref(v_lt_220_);
v___x_244_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_220_, v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v_mid_239_);
v___y_226_ = v___y_241_;
goto v___jp_225_;
}
else
{
lean_object* v___x_245_; 
v___x_245_ = lean_array_fswap(v___y_241_, v_mid_239_, v_hi_224_);
lean_dec(v_mid_239_);
v___y_226_ = v___x_245_;
goto v___jp_225_;
}
}
v___jp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_248_ = lean_array_fget_borrowed(v___y_247_, v_hi_224_);
v___x_249_ = lean_array_fget_borrowed(v___y_247_, v_lo_223_);
lean_inc(v___x_249_);
lean_inc(v___x_248_);
lean_inc_ref(v_lt_220_);
v___x_250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___lam__0(v_lt_220_, v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
v___y_241_ = v___y_247_;
goto v___jp_240_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_array_fswap(v___y_247_, v_lo_223_, v_hi_224_);
v___y_241_ = v___x_251_;
goto v___jp_240_;
}
}
}
v___jp_225_:
{
lean_object* v_pivot_227_; lean_object* v___x_228_; lean_object* v_fst_229_; lean_object* v_snd_230_; uint8_t v___x_231_; 
v_pivot_227_ = lean_array_fget(v___y_226_, v_hi_224_);
lean_inc_n(v_lo_223_, 2);
lean_inc_ref(v_lt_220_);
v___x_228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_220_, v_hi_224_, v_pivot_227_, v___y_226_, v_lo_223_, v_lo_223_);
v_fst_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_fst_229_);
v_snd_230_ = lean_ctor_get(v___x_228_, 1);
lean_inc(v_snd_230_);
lean_dec_ref(v___x_228_);
v___x_231_ = lean_nat_dec_le(v_hi_224_, v_fst_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc_ref(v_lt_220_);
v___x_232_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_220_, v_n_221_, v_snd_230_, v_lo_223_, v_fst_229_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_fst_229_, v___x_233_);
lean_dec(v_fst_229_);
v_as_222_ = v___x_232_;
v_lo_223_ = v___x_234_;
goto _start;
}
else
{
lean_dec(v_fst_229_);
lean_dec(v_lo_223_);
lean_dec_ref(v_lt_220_);
return v_snd_230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg___boxed(lean_object* v_lt_256_, lean_object* v_n_257_, lean_object* v_as_258_, lean_object* v_lo_259_, lean_object* v_hi_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_256_, v_n_257_, v_as_258_, v_lo_259_, v_hi_260_);
lean_dec(v_hi_260_);
lean_dec(v_n_257_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(lean_object* v_threshold_262_, lean_object* v_p_263_, lean_object* v_x_264_, lean_object* v_____s_265_){
_start:
{
lean_object* v_fst_266_; lean_object* v_snd_267_; uint8_t v___x_268_; 
v_fst_266_ = lean_ctor_get(v_x_264_, 0);
v_snd_267_ = lean_ctor_get(v_x_264_, 1);
v___x_268_ = lean_nat_dec_lt(v_threshold_262_, v_snd_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec_ref(v_x_264_);
lean_dec_ref(v_p_263_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_____s_265_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; uint8_t v___x_271_; 
lean_inc(v_fst_266_);
v___x_270_ = lean_apply_1(v_p_263_, v_fst_266_);
v___x_271_ = lean_unbox(v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
lean_dec_ref(v_x_264_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_____s_265_);
return v___x_272_;
}
else
{
lean_object* v_r_273_; lean_object* v___x_274_; 
v_r_273_ = lean_array_push(v_____s_265_, v_x_264_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_r_273_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed(lean_object* v_threshold_275_, lean_object* v_p_276_, lean_object* v_x_277_, lean_object* v_____s_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0(v_threshold_275_, v_p_276_, v_x_277_, v_____s_278_);
lean_dec(v_threshold_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(lean_object* v_counters_282_, lean_object* v_threshold_283_, lean_object* v_p_284_, lean_object* v_lt_285_){
_start:
{
lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v_r_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___f_286_ = lean_alloc_closure((void*)(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___lam__0___boxed), 4, 2);
lean_closure_set(v___f_286_, 0, v_threshold_283_);
lean_closure_set(v___f_286_, 1, v_p_284_);
v___x_287_ = lean_unsigned_to_nat(0u);
v_r_288_ = ((lean_object*)(l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___closed__0));
v___x_289_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_counters_282_, v_r_288_, v___f_286_);
v___x_290_ = lean_array_get_size(v___x_289_);
v___x_291_ = lean_nat_dec_eq(v___x_290_, v___x_287_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___y_295_; uint8_t v___x_299_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_sub(v___x_290_, v___x_292_);
v___x_299_ = lean_nat_dec_le(v___x_287_, v___x_293_);
if (v___x_299_ == 0)
{
lean_inc(v___x_293_);
v___y_295_ = v___x_293_;
goto v___jp_294_;
}
else
{
v___y_295_ = v___x_287_;
goto v___jp_294_;
}
v___jp_294_:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_le(v___y_295_, v___x_293_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
lean_dec(v___x_293_);
lean_inc(v___y_295_);
v___x_297_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_285_, v___x_290_, v___x_289_, v___y_295_, v___y_295_);
lean_dec(v___y_295_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_285_, v___x_290_, v___x_289_, v___y_295_, v___x_293_);
lean_dec(v___x_293_);
return v___x_298_;
}
}
}
else
{
lean_dec_ref(v_lt_285_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1___boxed(lean_object* v_counters_300_, lean_object* v_threshold_301_, lean_object* v_p_302_, lean_object* v_lt_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(v_counters_300_, v_threshold_301_, v_p_302_, v_lt_303_);
lean_dec_ref(v_counters_300_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(lean_object* v_keys_305_, lean_object* v_vals_306_, lean_object* v_i_307_, lean_object* v_k_308_){
_start:
{
uint8_t v___y_314_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_keys_305_);
v___x_318_ = lean_nat_dec_lt(v_i_307_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
lean_dec(v_i_307_);
v___x_319_ = lean_box(0);
return v___x_319_;
}
else
{
lean_object* v_k_x27_320_; 
v_k_x27_320_ = lean_array_fget_borrowed(v_keys_305_, v_i_307_);
if (lean_obj_tag(v_k_308_) == 0)
{
if (lean_obj_tag(v_k_x27_320_) == 0)
{
lean_object* v_declName_321_; uint8_t v_inv_322_; lean_object* v_declName_323_; uint8_t v_inv_324_; uint8_t v___x_325_; 
v_declName_321_ = lean_ctor_get(v_k_308_, 0);
v_inv_322_ = lean_ctor_get_uint8(v_k_308_, sizeof(void*)*1 + 1);
v_declName_323_ = lean_ctor_get(v_k_x27_320_, 0);
v_inv_324_ = lean_ctor_get_uint8(v_k_x27_320_, sizeof(void*)*1 + 1);
v___x_325_ = lean_name_eq(v_declName_321_, v_declName_323_);
if (v___x_325_ == 0)
{
v___y_314_ = v___x_325_;
goto v___jp_313_;
}
else
{
if (v_inv_324_ == 0)
{
if (v_inv_322_ == 0)
{
v___y_314_ = v___x_325_;
goto v___jp_313_;
}
else
{
goto v___jp_309_;
}
}
else
{
v___y_314_ = v_inv_322_;
goto v___jp_313_;
}
}
}
else
{
goto v___jp_309_;
}
}
else
{
if (lean_obj_tag(v_k_x27_320_) == 0)
{
goto v___jp_309_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = l_Lean_Meta_Origin_key(v_k_308_);
v___x_327_ = l_Lean_Meta_Origin_key(v_k_x27_320_);
v___x_328_ = lean_name_eq(v___x_326_, v___x_327_);
lean_dec(v___x_327_);
lean_dec(v___x_326_);
v___y_314_ = v___x_328_;
goto v___jp_313_;
}
}
}
v___jp_309_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_i_307_, v___x_310_);
lean_dec(v_i_307_);
v_i_307_ = v___x_311_;
goto _start;
}
v___jp_313_:
{
if (v___y_314_ == 0)
{
goto v___jp_309_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_array_fget_borrowed(v_vals_306_, v_i_307_);
lean_dec(v_i_307_);
lean_inc(v___x_315_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_keys_329_, lean_object* v_vals_330_, lean_object* v_i_331_, lean_object* v_k_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_329_, v_vals_330_, v_i_331_, v_k_332_);
lean_dec_ref(v_k_332_);
lean_dec_ref(v_vals_330_);
lean_dec_ref(v_keys_329_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(lean_object* v_x_334_, size_t v_x_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v_es_337_; lean_object* v___x_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v_j_341_; lean_object* v___x_342_; 
v_es_337_ = lean_ctor_get(v_x_334_, 0);
v___x_338_ = lean_box(2);
v___x_339_ = ((size_t)31ULL);
v___x_340_ = lean_usize_land(v_x_335_, v___x_339_);
v_j_341_ = lean_usize_to_nat(v___x_340_);
v___x_342_ = lean_array_get_borrowed(v___x_338_, v_es_337_, v_j_341_);
lean_dec(v_j_341_);
switch(lean_obj_tag(v___x_342_))
{
case 0:
{
lean_object* v_key_343_; lean_object* v_val_344_; uint8_t v___y_346_; 
v_key_343_ = lean_ctor_get(v___x_342_, 0);
v_val_344_ = lean_ctor_get(v___x_342_, 1);
if (lean_obj_tag(v_x_336_) == 0)
{
if (lean_obj_tag(v_key_343_) == 0)
{
lean_object* v_declName_349_; uint8_t v_inv_350_; lean_object* v_declName_351_; uint8_t v_inv_352_; uint8_t v___x_353_; 
v_declName_349_ = lean_ctor_get(v_x_336_, 0);
v_inv_350_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*1 + 1);
v_declName_351_ = lean_ctor_get(v_key_343_, 0);
v_inv_352_ = lean_ctor_get_uint8(v_key_343_, sizeof(void*)*1 + 1);
v___x_353_ = lean_name_eq(v_declName_349_, v_declName_351_);
if (v___x_353_ == 0)
{
v___y_346_ = v___x_353_;
goto v___jp_345_;
}
else
{
if (v_inv_352_ == 0)
{
if (v_inv_350_ == 0)
{
v___y_346_ = v___x_353_;
goto v___jp_345_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_box(0);
return v___x_354_;
}
}
else
{
v___y_346_ = v_inv_350_;
goto v___jp_345_;
}
}
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_box(0);
return v___x_355_;
}
}
else
{
if (lean_obj_tag(v_key_343_) == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = l_Lean_Meta_Origin_key(v_x_336_);
v___x_358_ = l_Lean_Meta_Origin_key(v_key_343_);
v___x_359_ = lean_name_eq(v___x_357_, v___x_358_);
lean_dec(v___x_358_);
lean_dec(v___x_357_);
v___y_346_ = v___x_359_;
goto v___jp_345_;
}
}
v___jp_345_:
{
if (v___y_346_ == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_box(0);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
lean_inc(v_val_344_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v_val_344_);
return v___x_348_;
}
}
}
case 1:
{
lean_object* v_node_360_; size_t v___x_361_; size_t v___x_362_; 
v_node_360_ = lean_ctor_get(v___x_342_, 0);
v___x_361_ = ((size_t)5ULL);
v___x_362_ = lean_usize_shift_right(v_x_335_, v___x_361_);
v_x_334_ = v_node_360_;
v_x_335_ = v___x_362_;
goto _start;
}
default: 
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
}
}
else
{
lean_object* v_ks_365_; lean_object* v_vs_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_ks_365_ = lean_ctor_get(v_x_334_, 0);
v_vs_366_ = lean_ctor_get(v_x_334_, 1);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_ks_365_, v_vs_366_, v___x_367_, v_x_336_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg___boxed(lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
size_t v_x_4296__boxed_372_; lean_object* v_res_373_; 
v_x_4296__boxed_372_ = lean_unbox_usize(v_x_370_);
lean_dec(v_x_370_);
v_res_373_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_369_, v_x_4296__boxed_372_, v_x_371_);
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_369_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
uint64_t v___y_377_; uint64_t v___y_381_; uint64_t v___y_385_; 
if (lean_obj_tag(v_x_375_) == 0)
{
uint8_t v_inv_388_; 
v_inv_388_ = lean_ctor_get_uint8(v_x_375_, sizeof(void*)*1 + 1);
if (v_inv_388_ == 0)
{
lean_object* v_declName_389_; 
v_declName_389_ = lean_ctor_get(v_x_375_, 0);
if (lean_obj_tag(v_declName_389_) == 0)
{
uint64_t v___x_390_; 
v___x_390_ = 1723ULL;
v___y_381_ = v___x_390_;
goto v___jp_380_;
}
else
{
uint64_t v_hash_391_; 
v_hash_391_ = lean_ctor_get_uint64(v_declName_389_, sizeof(void*)*2);
v___y_381_ = v_hash_391_;
goto v___jp_380_;
}
}
else
{
lean_object* v_declName_392_; 
v_declName_392_ = lean_ctor_get(v_x_375_, 0);
if (lean_obj_tag(v_declName_392_) == 0)
{
uint64_t v___x_393_; 
v___x_393_ = 1723ULL;
v___y_385_ = v___x_393_;
goto v___jp_384_;
}
else
{
uint64_t v_hash_394_; 
v_hash_394_ = lean_ctor_get_uint64(v_declName_392_, sizeof(void*)*2);
v___y_385_ = v_hash_394_;
goto v___jp_384_;
}
}
}
else
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Meta_Origin_key(v_x_375_);
if (lean_obj_tag(v___x_395_) == 0)
{
uint64_t v___x_396_; 
v___x_396_ = 1723ULL;
v___y_377_ = v___x_396_;
goto v___jp_376_;
}
else
{
uint64_t v_hash_397_; 
v_hash_397_ = lean_ctor_get_uint64(v___x_395_, sizeof(void*)*2);
lean_dec(v___x_395_);
v___y_377_ = v_hash_397_;
goto v___jp_376_;
}
}
v___jp_376_:
{
size_t v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_uint64_to_usize(v___y_377_);
v___x_379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_374_, v___x_378_, v_x_375_);
return v___x_379_;
}
v___jp_380_:
{
uint64_t v___x_382_; uint64_t v___x_383_; 
v___x_382_ = 13ULL;
v___x_383_ = lean_uint64_mix_hash(v___y_381_, v___x_382_);
v___y_377_ = v___x_383_;
goto v___jp_376_;
}
v___jp_384_:
{
uint64_t v___x_386_; uint64_t v___x_387_; 
v___x_386_ = 11ULL;
v___x_387_ = lean_uint64_mix_hash(v___y_385_, v___x_386_);
v___y_377_ = v___x_387_;
goto v___jp_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg___boxed(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_398_, v_x_399_);
lean_dec_ref(v_x_399_);
lean_dec_ref(v_x_398_);
return v_res_400_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_406_; double v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_float_of_nat(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__5));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = l_Lean_crossEmoji;
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__8));
v___x_416_ = lean_string_append(v___x_415_, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(lean_object* v_usedCounters_x3f_417_, lean_object* v_as_418_, size_t v_sz_419_, size_t v_i_420_, lean_object* v_b_421_, lean_object* v___y_422_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_lt(v_i_420_, v_sz_419_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_b_421_);
return v___x_425_;
}
else
{
lean_object* v_a_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_473_; 
v_a_426_ = lean_array_uget(v_as_418_, v_i_420_);
v_fst_427_ = lean_ctor_get(v_a_426_, 0);
v_snd_428_ = lean_ctor_get(v_a_426_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_426_);
if (v_isSharedCheck_473_ == 0)
{
v___x_430_ = v_a_426_;
v_isShared_431_ = v_isSharedCheck_473_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_inc(v_fst_427_);
lean_dec(v_a_426_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_473_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
lean_inc(v_fst_427_);
v___x_433_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_fst_427_, v___y_422_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_usedMsg_436_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
if (lean_obj_tag(v_usedCounters_x3f_417_) == 1)
{
lean_object* v_val_457_; lean_object* v___x_458_; 
v_val_457_ = lean_ctor_get(v_usedCounters_x3f_417_, 0);
v___x_458_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_val_457_, v_fst_427_);
lean_dec(v_fst_427_);
if (lean_obj_tag(v___x_458_) == 1)
{
lean_object* v_val_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_val_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__7));
v___x_461_ = l_Nat_reprFast(v_val_459_);
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
lean_dec_ref(v___x_461_);
v_usedMsg_436_ = v___x_462_;
goto v___jp_435_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v___x_458_);
v___x_463_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__9);
v_usedMsg_436_ = v___x_463_;
goto v___jp_435_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v_fst_427_);
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v_usedMsg_436_ = v___x_464_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; double v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_438_ = lean_box(0);
v___x_439_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_441_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_441_, 0, v___x_437_);
lean_ctor_set(v___x_441_, 1, v___x_438_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
lean_ctor_set_float(v___x_441_, sizeof(void*)*3, v___x_439_);
lean_ctor_set_float(v___x_441_, sizeof(void*)*3 + 8, v___x_439_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*3 + 16, v___x_424_);
v___x_442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__6);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 7);
lean_ctor_set(v___x_430_, 1, v___x_442_);
lean_ctor_set(v___x_430_, 0, v_a_434_);
v___x_444_ = v___x_430_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_434_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_442_);
v___x_444_ = v_reuseFailAlloc_456_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; size_t v___x_453_; size_t v___x_454_; 
v___x_445_ = l_Nat_reprFast(v_snd_428_);
v___x_446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___x_447_ = l_Lean_MessageData_ofFormat(v___x_446_);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_stringToMessageData(v_usedMsg_436_);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_441_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_ctor_set(v___x_451_, 2, v___x_432_);
v___x_452_ = lean_array_push(v_b_421_, v___x_451_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_add(v_i_420_, v___x_453_);
v_i_420_ = v___x_454_;
v_b_421_ = v___x_452_;
goto _start;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_del_object(v___x_430_);
lean_dec(v_snd_428_);
lean_dec(v_fst_427_);
lean_dec_ref(v_b_421_);
v_a_465_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_433_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_433_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___boxed(lean_object* v_usedCounters_x3f_474_, lean_object* v_as_475_, lean_object* v_sz_476_, lean_object* v_i_477_, lean_object* v_b_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_476_);
lean_dec(v_sz_476_);
v_i_boxed_482_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_474_, v_as_475_, v_sz_boxed_481_, v_i_boxed_482_, v_b_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v_as_475_);
lean_dec(v_usedCounters_x3f_474_);
return v_res_483_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = l_Lean_Meta_instInhabitedOrigin_default;
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary(lean_object* v_counters_492_, lean_object* v_usedCounters_x3f_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_toCold_499_; lean_object* v_options_500_; lean_object* v___f_501_; lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_toCold_499_ = lean_ctor_get(v_a_496_, 0);
v_options_500_ = lean_ctor_get(v_toCold_499_, 2);
v___f_501_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__0));
v___f_502_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__1));
v___x_503_ = l_Lean_diagnostics_threshold;
v___x_504_ = l_Lean_Option_get___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__0(v_options_500_, v___x_503_);
v___x_505_ = l_Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1(v_counters_492_, v___x_504_, v___f_502_, v___f_501_);
v___x_506_ = lean_array_get_size(v___x_505_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_nat_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; size_t v_sz_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_509_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2, &l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2_once, _init_l_Lean_Meta_Simp_mkSimpDiagSummary___closed__2);
v___x_510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v_sz_511_ = lean_array_size(v___x_505_);
v___x_512_ = ((size_t)0ULL);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_493_, v___x_505_, v_sz_511_, v___x_512_, v___x_510_, v_a_497_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_531_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_531_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_531_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_531_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v_snd_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
v___x_518_ = lean_array_get(v___x_509_, v___x_505_, v___x_507_);
lean_dec_ref(v___x_505_);
v_snd_519_ = lean_ctor_get(v___x_518_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v___x_518_, 0);
lean_dec(v_unused_530_);
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v_a_514_);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_514_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_snd_519_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_524_);
v___x_526_ = v___x_516_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v___x_505_);
v_a_532_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_513_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_513_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec_ref(v___x_505_);
v___x_540_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3));
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpDiagSummary___boxed(lean_object* v_counters_542_, lean_object* v_usedCounters_x3f_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_counters_542_, v_usedCounters_x3f_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_usedCounters_x3f_543_);
lean_dec_ref(v_counters_542_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(lean_object* v_00_u03b2_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___redArg(v_x_551_, v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2___boxed(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2(v_00_u03b2_554_, v_x_555_, v_x_556_);
lean_dec_ref(v_x_556_);
lean_dec_ref(v_x_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(lean_object* v_usedCounters_x3f_558_, lean_object* v_as_559_, size_t v_sz_560_, size_t v_i_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg(v_usedCounters_x3f_558_, v_as_559_, v_sz_560_, v_i_561_, v_b_562_, v___y_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___boxed(lean_object* v_usedCounters_x3f_569_, lean_object* v_as_570_, lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_580_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3(v_usedCounters_x3f_569_, v_as_570_, v_sz_boxed_579_, v_i_boxed_580_, v_b_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_as_570_);
lean_dec(v_usedCounters_x3f_569_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(lean_object* v_00_u03c3_582_, lean_object* v_00_u03b2_583_, lean_object* v_map_584_, lean_object* v_init_585_, lean_object* v_f_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___redArg(v_map_584_, v_init_585_, v_f_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1___boxed(lean_object* v_00_u03c3_588_, lean_object* v_00_u03b2_589_, lean_object* v_map_590_, lean_object* v_init_591_, lean_object* v_f_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1(v_00_u03c3_588_, v_00_u03b2_589_, v_map_590_, v_init_591_, v_f_592_);
lean_dec_ref(v_map_590_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(lean_object* v_lt_594_, lean_object* v_n_595_, lean_object* v_as_596_, lean_object* v_lo_597_, lean_object* v_hi_598_, lean_object* v_w_599_, lean_object* v_hlo_600_, lean_object* v_hhi_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___redArg(v_lt_594_, v_n_595_, v_as_596_, v_lo_597_, v_hi_598_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2___boxed(lean_object* v_lt_603_, lean_object* v_n_604_, lean_object* v_as_605_, lean_object* v_lo_606_, lean_object* v_hi_607_, lean_object* v_w_608_, lean_object* v_hlo_609_, lean_object* v_hhi_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2(v_lt_603_, v_n_604_, v_as_605_, v_lo_606_, v_hi_607_, v_w_608_, v_hlo_609_, v_hhi_610_);
lean_dec(v_hi_607_);
lean_dec(v_n_604_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, size_t v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___redArg(v_x_613_, v_x_614_, v_x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4___boxed(lean_object* v_00_u03b2_617_, lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
size_t v_x_4704__boxed_621_; lean_object* v_res_622_; 
v_x_4704__boxed_621_ = lean_unbox_usize(v_x_619_);
lean_dec(v_x_619_);
v_res_622_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4(v_00_u03b2_617_, v_x_618_, v_x_4704__boxed_621_, v_x_620_);
lean_dec_ref(v_x_620_);
lean_dec_ref(v_x_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2___redArg(lean_object* v_map_623_, lean_object* v_f_624_, lean_object* v_init_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_624_, v_map_623_, v_init_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_627_, lean_object* v_00_u03c3_628_, lean_object* v_00_u03b2_629_, lean_object* v_map_630_, lean_object* v_f_631_, lean_object* v_init_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_631_, v_map_630_, v_init_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(lean_object* v_lt_634_, lean_object* v_n_635_, lean_object* v_lo_636_, lean_object* v_hi_637_, lean_object* v_hhi_638_, lean_object* v_pivot_639_, lean_object* v_as_640_, lean_object* v_i_641_, lean_object* v_k_642_, lean_object* v_ilo_643_, lean_object* v_ik_644_, lean_object* v_w_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___redArg(v_lt_634_, v_hi_637_, v_pivot_639_, v_as_640_, v_i_641_, v_k_642_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4___boxed(lean_object* v_lt_647_, lean_object* v_n_648_, lean_object* v_lo_649_, lean_object* v_hi_650_, lean_object* v_hhi_651_, lean_object* v_pivot_652_, lean_object* v_as_653_, lean_object* v_i_654_, lean_object* v_k_655_, lean_object* v_ilo_656_, lean_object* v_ik_657_, lean_object* v_w_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__2_spec__4(v_lt_647_, v_n_648_, v_lo_649_, v_hi_650_, v_hhi_651_, v_pivot_652_, v_as_653_, v_i_654_, v_k_655_, v_ilo_656_, v_ik_657_, v_w_658_);
lean_dec(v_hi_650_);
lean_dec(v_lo_649_);
lean_dec(v_n_648_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_660_, lean_object* v_keys_661_, lean_object* v_vals_662_, lean_object* v_heq_663_, lean_object* v_i_664_, lean_object* v_k_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___redArg(v_keys_661_, v_vals_662_, v_i_664_, v_k_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_667_, lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_heq_670_, lean_object* v_i_671_, lean_object* v_k_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__2_spec__4_spec__7(v_00_u03b2_667_, v_keys_668_, v_vals_669_, v_heq_670_, v_i_671_, v_k_672_);
lean_dec_ref(v_k_672_);
lean_dec_ref(v_vals_669_);
lean_dec_ref(v_keys_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_674_, lean_object* v_00_u03c3_675_, lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_f_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5___redArg(v_f_678_, v_x_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_00_u03c3_684_, lean_object* v_00_u03c3_685_, lean_object* v_f_686_, lean_object* v_as_687_, size_t v_i_688_, size_t v_stop_689_, lean_object* v_b_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_f_686_, v_as_687_, v_i_688_, v_stop_689_, v_b_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_00_u03c3_694_, lean_object* v_00_u03c3_695_, lean_object* v_f_696_, lean_object* v_as_697_, lean_object* v_i_698_, lean_object* v_stop_699_, lean_object* v_b_700_){
_start:
{
size_t v_i_boxed_701_; size_t v_stop_boxed_702_; lean_object* v_res_703_; 
v_i_boxed_701_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_stop_boxed_702_ = lean_unbox_usize(v_stop_699_);
lean_dec(v_stop_699_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b1_692_, v_00_u03b2_693_, v_00_u03c3_694_, v_00_u03c3_695_, v_f_696_, v_as_697_, v_i_boxed_701_, v_stop_boxed_702_, v_b_700_);
lean_dec_ref(v_as_697_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03c3_704_, lean_object* v_00_u03c3_705_, lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_f_708_, lean_object* v_keys_709_, lean_object* v_vals_710_, lean_object* v_heq_711_, lean_object* v_i_712_, lean_object* v_acc_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_f_708_, v_keys_709_, v_vals_710_, v_i_712_, v_acc_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03c3_715_, lean_object* v_00_u03c3_716_, lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_f_719_, lean_object* v_keys_720_, lean_object* v_vals_721_, lean_object* v_heq_722_, lean_object* v_i_723_, lean_object* v_acc_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_collectAboveThreshold___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__1_spec__1_spec__2_spec__5_spec__9(v_00_u03c3_715_, v_00_u03c3_716_, v_00_u03b1_717_, v_00_u03b2_718_, v_f_719_, v_keys_720_, v_vals_721_, v_heq_722_, v_i_723_, v_acc_724_);
lean_dec_ref(v_vals_721_);
lean_dec_ref(v_keys_720_);
return v_res_725_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_728_ = l_Lean_stringToMessageData(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_as_729_, size_t v_sz_730_, size_t v_i_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_lt(v_i_731_, v_sz_730_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v_b_732_);
return v___x_737_;
}
else
{
lean_object* v_snd_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_782_; 
v_snd_738_ = lean_ctor_get(v_b_732_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_b_732_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v_b_732_, 0);
lean_dec(v_unused_783_);
v___x_740_ = v_b_732_;
v_isShared_741_ = v_isSharedCheck_782_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snd_738_);
lean_dec(v_b_732_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_782_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_a_742_; lean_object* v_keys_743_; lean_object* v_origin_744_; lean_object* v_data_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_a_742_ = lean_array_uget_borrowed(v_as_729_, v_i_731_);
v_keys_743_ = lean_ctor_get(v_a_742_, 0);
v_origin_744_ = lean_ctor_get(v_a_742_, 4);
v_data_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_746_ = lean_box(0);
lean_inc_ref(v_origin_744_);
v___x_747_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_744_, v___y_734_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
lean_inc_ref(v_keys_743_);
v___x_749_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_743_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; double v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_752_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_754_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_754_, 0, v___x_751_);
lean_ctor_set(v___x_754_, 1, v___x_746_);
lean_ctor_set(v___x_754_, 2, v___x_753_);
lean_ctor_set_float(v___x_754_, sizeof(void*)*3, v___x_752_);
lean_ctor_set_float(v___x_754_, sizeof(void*)*3 + 8, v___x_752_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*3 + 16, v___x_736_);
v___x_755_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v_a_748_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v_a_750_);
v___x_758_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_758_, 0, v___x_754_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
lean_ctor_set(v___x_758_, 2, v_data_745_);
v___x_759_ = lean_array_push(v_snd_738_, v___x_758_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_759_);
lean_ctor_set(v___x_740_, 0, v___x_746_);
v___x_761_ = v___x_740_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
size_t v___x_762_; size_t v___x_763_; 
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_731_, v___x_762_);
v_i_731_ = v___x_763_;
v_b_732_ = v___x_761_;
goto _start;
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_748_);
lean_del_object(v___x_740_);
lean_dec(v_snd_738_);
v_a_766_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_749_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_749_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_del_object(v___x_740_);
lean_dec(v_snd_738_);
v_a_774_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_747_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_747_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_as_784_, lean_object* v_sz_785_, lean_object* v_i_786_, lean_object* v_b_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
size_t v_sz_boxed_791_; size_t v_i_boxed_792_; lean_object* v_res_793_; 
v_sz_boxed_791_ = lean_unbox_usize(v_sz_785_);
lean_dec(v_sz_785_);
v_i_boxed_792_ = lean_unbox_usize(v_i_786_);
lean_dec(v_i_786_);
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_784_, v_sz_boxed_791_, v_i_boxed_792_, v_b_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec_ref(v_as_784_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(lean_object* v_as_794_, size_t v_sz_795_, size_t v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_796_, v_sz_795_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_b_797_);
return v___x_804_;
}
else
{
lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_849_; 
v_snd_805_ = lean_ctor_get(v_b_797_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_b_797_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_b_797_, 0);
lean_dec(v_unused_850_);
v___x_807_ = v_b_797_;
v_isShared_808_ = v_isSharedCheck_849_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_dec(v_b_797_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_849_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_a_809_; lean_object* v_keys_810_; lean_object* v_origin_811_; lean_object* v_data_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_a_809_ = lean_array_uget_borrowed(v_as_794_, v_i_796_);
v_keys_810_ = lean_ctor_get(v_a_809_, 0);
v_origin_811_ = lean_ctor_get(v_a_809_, 4);
v_data_812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_813_ = lean_box(0);
lean_inc_ref(v_origin_811_);
v___x_814_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_811_, v___y_801_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
lean_inc_ref(v_keys_810_);
v___x_816_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_810_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; double v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_819_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_821_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_821_, 0, v___x_818_);
lean_ctor_set(v___x_821_, 1, v___x_813_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
lean_ctor_set_float(v___x_821_, sizeof(void*)*3, v___x_819_);
lean_ctor_set_float(v___x_821_, sizeof(void*)*3 + 8, v___x_819_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*3 + 16, v___x_803_);
v___x_822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v_a_815_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v_a_817_);
v___x_825_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_825_, 0, v___x_821_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
lean_ctor_set(v___x_825_, 2, v_data_812_);
v___x_826_ = lean_array_push(v_snd_805_, v___x_825_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_826_);
lean_ctor_set(v___x_807_, 0, v___x_813_);
v___x_828_ = v___x_807_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_832_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
v___x_829_ = ((size_t)1ULL);
v___x_830_ = lean_usize_add(v_i_796_, v___x_829_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_794_, v_sz_795_, v___x_830_, v___x_828_, v___y_800_, v___y_801_);
return v___x_831_;
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_a_815_);
lean_del_object(v___x_807_);
lean_dec(v_snd_805_);
v_a_833_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_816_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_816_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_del_object(v___x_807_);
lean_dec(v_snd_805_);
v_a_841_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_814_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_814_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2___boxed(lean_object* v_as_851_, lean_object* v_sz_852_, lean_object* v_i_853_, lean_object* v_b_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
size_t v_sz_boxed_860_; size_t v_i_boxed_861_; lean_object* v_res_862_; 
v_sz_boxed_860_ = lean_unbox_usize(v_sz_852_);
lean_dec(v_sz_852_);
v_i_boxed_861_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_as_851_, v_sz_boxed_860_, v_i_boxed_861_, v_b_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec_ref(v_as_851_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(lean_object* v_init_863_, lean_object* v_n_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
if (lean_obj_tag(v_n_864_) == 0)
{
lean_object* v_cs_871_; lean_object* v___x_872_; lean_object* v___x_873_; size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; 
v_cs_871_ = lean_ctor_get(v_n_864_, 0);
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_b_865_);
v_sz_874_ = lean_array_size(v_cs_871_);
v___x_875_ = ((size_t)0ULL);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_863_, v_cs_871_, v_sz_874_, v___x_875_, v___x_873_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_891_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_891_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_fst_881_; 
v_fst_881_ = lean_ctor_get(v_a_877_, 0);
if (lean_obj_tag(v_fst_881_) == 0)
{
lean_object* v_snd_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v_snd_882_ = lean_ctor_get(v_a_877_, 1);
lean_inc(v_snd_882_);
lean_dec(v_a_877_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v_snd_882_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_883_);
v___x_885_ = v___x_879_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v_val_887_; lean_object* v___x_889_; 
lean_inc_ref(v_fst_881_);
lean_dec(v_a_877_);
v_val_887_ = lean_ctor_get(v_fst_881_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v_fst_881_, 1);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_val_887_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_val_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_876_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_876_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v_vs_900_; lean_object* v___x_901_; lean_object* v___x_902_; size_t v_sz_903_; size_t v___x_904_; lean_object* v___x_905_; 
v_vs_900_ = lean_ctor_get(v_n_864_, 0);
v___x_901_ = lean_box(0);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v_b_865_);
v_sz_903_ = lean_array_size(v_vs_900_);
v___x_904_ = ((size_t)0ULL);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2(v_vs_900_, v_sz_903_, v___x_904_, v___x_902_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_920_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_920_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_fst_910_; 
v_fst_910_ = lean_ctor_get(v_a_906_, 0);
if (lean_obj_tag(v_fst_910_) == 0)
{
lean_object* v_snd_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v_snd_911_ = lean_ctor_get(v_a_906_, 1);
lean_inc(v_snd_911_);
lean_dec(v_a_906_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_snd_911_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_912_);
v___x_914_ = v___x_908_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_object* v_val_916_; lean_object* v___x_918_; 
lean_inc_ref(v_fst_910_);
lean_dec(v_a_906_);
v_val_916_ = lean_ctor_get(v_fst_910_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v_fst_910_, 1);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v_val_916_);
v___x_918_ = v___x_908_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_val_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_905_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_905_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(lean_object* v_init_929_, lean_object* v_as_930_, size_t v_sz_931_, size_t v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
uint8_t v___x_939_; 
v___x_939_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_933_);
return v___x_940_;
}
else
{
lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_975_; 
v_snd_941_ = lean_ctor_get(v_b_933_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_b_933_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v_b_933_, 0);
lean_dec(v_unused_976_);
v___x_943_ = v_b_933_;
v_isShared_944_ = v_isSharedCheck_975_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_dec(v_b_933_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_975_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v_a_946_; lean_object* v___x_947_; 
v___x_945_ = lean_box(0);
v_a_946_ = lean_array_uget_borrowed(v_as_930_, v_i_932_);
lean_inc(v_snd_941_);
v___x_947_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_929_, v_a_946_, v_snd_941_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_966_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_966_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_966_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_966_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
if (lean_obj_tag(v_a_948_) == 0)
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_a_948_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_952_);
v___x_954_ = v___x_943_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_snd_941_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_954_);
v___x_956_ = v___x_950_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; 
lean_del_object(v___x_950_);
lean_dec(v_snd_941_);
v_a_959_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v_a_948_, 1);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_a_959_);
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_961_ = v___x_943_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
size_t v___x_962_; size_t v___x_963_; 
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_932_, v___x_962_);
v_i_932_ = v___x_963_;
v_b_933_ = v___x_961_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
v_a_967_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_947_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_947_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1___boxed(lean_object* v_init_977_, lean_object* v_as_978_, lean_object* v_sz_979_, lean_object* v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
size_t v_sz_boxed_987_; size_t v_i_boxed_988_; lean_object* v_res_989_; 
v_sz_boxed_987_ = lean_unbox_usize(v_sz_979_);
lean_dec(v_sz_979_);
v_i_boxed_988_ = lean_unbox_usize(v_i_980_);
lean_dec(v_i_980_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__1(v_init_977_, v_as_978_, v_sz_boxed_987_, v_i_boxed_988_, v_b_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_as_978_);
lean_dec_ref(v_init_977_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0___boxed(lean_object* v_init_990_, lean_object* v_n_991_, lean_object* v_b_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_990_, v_n_991_, v_b_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec_ref(v_n_991_);
lean_dec_ref(v_init_990_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(lean_object* v_as_999_, size_t v_sz_1000_, size_t v_i_1001_, lean_object* v_b_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_lt(v_i_1001_, v_sz_1000_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_b_1002_);
return v___x_1007_;
}
else
{
lean_object* v_snd_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1052_; 
v_snd_1008_ = lean_ctor_get(v_b_1002_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_b_1002_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_b_1002_, 0);
lean_dec(v_unused_1053_);
v___x_1010_ = v_b_1002_;
v_isShared_1011_ = v_isSharedCheck_1052_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_snd_1008_);
lean_dec(v_b_1002_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1052_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_a_1012_; lean_object* v_keys_1013_; lean_object* v_origin_1014_; lean_object* v_data_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1012_ = lean_array_uget_borrowed(v_as_999_, v_i_1001_);
v_keys_1013_ = lean_ctor_get(v_a_1012_, 0);
v_origin_1014_ = lean_ctor_get(v_a_1012_, 4);
v_data_1015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1016_ = lean_box(0);
lean_inc_ref(v_origin_1014_);
v___x_1017_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_1014_, v___y_1004_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
lean_inc_ref(v_keys_1013_);
v___x_1019_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1013_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; double v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1022_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1024_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1024_, 0, v___x_1021_);
lean_ctor_set(v___x_1024_, 1, v___x_1016_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
lean_ctor_set_float(v___x_1024_, sizeof(void*)*3, v___x_1022_);
lean_ctor_set_float(v___x_1024_, sizeof(void*)*3 + 8, v___x_1022_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*3 + 16, v___x_1006_);
v___x_1025_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_a_1018_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v_a_1020_);
v___x_1028_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
lean_ctor_set(v___x_1028_, 2, v_data_1015_);
v___x_1029_ = lean_array_push(v_snd_1008_, v___x_1028_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v___x_1029_);
lean_ctor_set(v___x_1010_, 0, v___x_1016_);
v___x_1031_ = v___x_1010_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
size_t v___x_1032_; size_t v___x_1033_; 
v___x_1032_ = ((size_t)1ULL);
v___x_1033_ = lean_usize_add(v_i_1001_, v___x_1032_);
v_i_1001_ = v___x_1033_;
v_b_1002_ = v___x_1031_;
goto _start;
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_a_1018_);
lean_del_object(v___x_1010_);
lean_dec(v_snd_1008_);
v_a_1036_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1019_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1019_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_del_object(v___x_1010_);
lean_dec(v_snd_1008_);
v_a_1044_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1017_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1017_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1054_, lean_object* v_sz_1055_, lean_object* v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; lean_object* v_res_1063_; 
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1055_);
lean_dec(v_sz_1055_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1054_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_as_1054_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(lean_object* v_as_1064_, size_t v_sz_1065_, size_t v_i_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_usize_dec_lt(v_i_1066_, v_sz_1065_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_b_1067_);
return v___x_1074_;
}
else
{
lean_object* v_snd_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1119_; 
v_snd_1075_ = lean_ctor_get(v_b_1067_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_b_1067_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_b_1067_, 0);
lean_dec(v_unused_1120_);
v___x_1077_ = v_b_1067_;
v_isShared_1078_ = v_isSharedCheck_1119_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_snd_1075_);
lean_dec(v_b_1067_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1119_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_a_1079_; lean_object* v_keys_1080_; lean_object* v_origin_1081_; lean_object* v_data_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_a_1079_ = lean_array_uget_borrowed(v_as_1064_, v_i_1066_);
v_keys_1080_ = lean_ctor_get(v_a_1079_, 0);
v_origin_1081_ = lean_ctor_get(v_a_1079_, 4);
v_data_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1083_ = lean_box(0);
lean_inc_ref(v_origin_1081_);
v___x_1084_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_originToKey___redArg(v_origin_1081_, v___y_1071_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
lean_inc_ref(v_keys_1080_);
v___x_1086_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1080_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; double v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1089_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1091_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1091_, 0, v___x_1088_);
lean_ctor_set(v___x_1091_, 1, v___x_1083_);
lean_ctor_set(v___x_1091_, 2, v___x_1090_);
lean_ctor_set_float(v___x_1091_, sizeof(void*)*3, v___x_1089_);
lean_ctor_set_float(v___x_1091_, sizeof(void*)*3 + 8, v___x_1089_);
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*3 + 16, v___x_1073_);
v___x_1092_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_a_1085_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_a_1087_);
v___x_1095_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1091_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_ctor_set(v___x_1095_, 2, v_data_1082_);
v___x_1096_ = lean_array_push(v_snd_1075_, v___x_1095_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1096_);
lean_ctor_set(v___x_1077_, 0, v___x_1083_);
v___x_1098_ = v___x_1077_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((size_t)1ULL);
v___x_1100_ = lean_usize_add(v_i_1066_, v___x_1099_);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1064_, v_sz_1065_, v___x_1100_, v___x_1098_, v___y_1070_, v___y_1071_);
return v___x_1101_;
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_a_1085_);
lean_del_object(v___x_1077_);
lean_dec(v_snd_1075_);
v_a_1103_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1086_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1086_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_del_object(v___x_1077_);
lean_dec(v_snd_1075_);
v_a_1111_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1084_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1084_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1___boxed(lean_object* v_as_1121_, lean_object* v_sz_1122_, lean_object* v_i_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
size_t v_sz_boxed_1130_; size_t v_i_boxed_1131_; lean_object* v_res_1132_; 
v_sz_boxed_1130_ = lean_unbox_usize(v_sz_1122_);
lean_dec(v_sz_1122_);
v_i_boxed_1131_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_as_1121_, v_sz_boxed_1130_, v_i_boxed_1131_, v_b_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v_as_1121_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(lean_object* v_t_1133_, lean_object* v_init_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_root_1140_; lean_object* v_tail_1141_; lean_object* v___x_1142_; 
v_root_1140_ = lean_ctor_get(v_t_1133_, 0);
v_tail_1141_ = lean_ctor_get(v_t_1133_, 1);
lean_inc_ref(v_init_1134_);
v___x_1142_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0(v_init_1134_, v_root_1140_, v_init_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec_ref(v_init_1134_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1179_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1179_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1179_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
if (lean_obj_tag(v_a_1143_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; 
v_a_1147_ = lean_ctor_get(v_a_1143_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v_a_1143_, 1);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_a_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; size_t v_sz_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
lean_del_object(v___x_1145_);
v_a_1151_ = lean_ctor_get(v_a_1143_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v_a_1143_, 1);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_a_1151_);
v_sz_1154_ = lean_array_size(v_tail_1141_);
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1(v_tail_1141_, v_sz_1154_, v___x_1155_, v___x_1153_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1170_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_fst_1161_; 
v_fst_1161_ = lean_ctor_get(v_a_1157_, 0);
if (lean_obj_tag(v_fst_1161_) == 0)
{
lean_object* v_snd_1162_; lean_object* v___x_1164_; 
v_snd_1162_ = lean_ctor_get(v_a_1157_, 1);
lean_inc(v_snd_1162_);
lean_dec(v_a_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_snd_1162_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_snd_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
else
{
lean_object* v_val_1166_; lean_object* v___x_1168_; 
lean_inc_ref(v_fst_1161_);
lean_dec(v_a_1157_);
v_val_1166_ = lean_ctor_get(v_fst_1161_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v_fst_1161_, 1);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_val_1166_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_val_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1156_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1156_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_a_1180_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1142_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1142_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0___boxed(lean_object* v_t_1188_, lean_object* v_init_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_t_1188_, v_init_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v_t_1188_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(lean_object* v_thms_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
uint8_t v___x_1202_; 
v___x_1202_ = l_Lean_PersistentArray_isEmpty___redArg(v_thms_1196_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v_data_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_unsigned_to_nat(0u);
v_data_1204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1205_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0(v_thms_1196_, v_data_1204_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_a_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1203_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1205_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1205_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimpDiagSummary___closed__3));
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary___boxed(lean_object* v_thms_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thms_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_thms_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(lean_object* v_as_1232_, size_t v_sz_1233_, size_t v_i_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___redArg(v_as_1232_, v_sz_1233_, v_i_1234_, v_b_1235_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1242_, lean_object* v_sz_1243_, lean_object* v_i_1244_, lean_object* v_b_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
size_t v_sz_boxed_1251_; size_t v_i_boxed_1252_; lean_object* v_res_1253_; 
v_sz_boxed_1251_ = lean_unbox_usize(v_sz_1243_);
lean_dec(v_sz_1243_);
v_i_boxed_1252_ = lean_unbox_usize(v_i_1244_);
lean_dec(v_i_1244_);
v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__1_spec__4(v_as_1242_, v_sz_boxed_1251_, v_i_boxed_1252_, v_b_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_as_1242_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1254_, size_t v_sz_1255_, size_t v_i_1256_, lean_object* v_b_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___redArg(v_as_1254_, v_sz_1255_, v_i_1256_, v_b_1257_, v___y_1260_, v___y_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1264_, lean_object* v_sz_1265_, lean_object* v_i_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
size_t v_sz_boxed_1273_; size_t v_i_boxed_1274_; lean_object* v_res_1275_; 
v_sz_boxed_1273_ = lean_unbox_usize(v_sz_1265_);
lean_dec(v_sz_1265_);
v_i_boxed_1274_ = lean_unbox_usize(v_i_1266_);
lean_dec(v_i_1266_);
v_res_1275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary_spec__0_spec__0_spec__2_spec__3(v_as_1264_, v_sz_boxed_1273_, v_i_boxed_1274_, v_b_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v_as_1264_);
return v_res_1275_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_mkDiagMessages___lam__0(lean_object* v_x_1276_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = 1;
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___lam__0___boxed(lean_object* v_x_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_Lean_Meta_Simp_mkDiagMessages___lam__0(v_x_1278_);
lean_dec(v_x_1278_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__6));
v___x_1290_ = l_Lean_MessageData_ofFormat(v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages(lean_object* v_diag_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_usedThmCounter_1297_; lean_object* v_triedThmCounter_1298_; lean_object* v_congrThmCounter_1299_; lean_object* v_thmsWithBadKeys_1300_; lean_object* v___f_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_usedThmCounter_1297_ = lean_ctor_get(v_diag_1291_, 0);
v_triedThmCounter_1298_ = lean_ctor_get(v_diag_1291_, 1);
v_congrThmCounter_1299_ = lean_ctor_get(v_diag_1291_, 2);
v_thmsWithBadKeys_1300_ = lean_ctor_get(v_diag_1291_, 3);
v___f_1301_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__0));
v___x_1302_ = lean_box(0);
v___x_1303_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_usedThmCounter_1297_, v___x_1302_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
lean_inc_ref(v_usedThmCounter_1297_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_usedThmCounter_1297_);
v___x_1306_ = l_Lean_Meta_Simp_mkSimpDiagSummary(v_triedThmCounter_1298_, v___x_1305_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec_ref_known(v___x_1305_, 1);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1309_ = l_Lean_Meta_mkDiagSummary(v___x_1308_, v_congrThmCounter_1299_, v___f_1301_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1355_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1355_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1355_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; 
v___x_1314_ = l___private_Lean_Meta_Tactic_Simp_Diagnostics_0__Lean_Meta_Simp_mkTheoremsWithBadKeySummary(v_thmsWithBadKeys_1300_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1346_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1346_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1346_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint8_t v___y_1320_; uint8_t v___y_1337_; uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1304_);
if (v___x_1344_ == 0)
{
v___y_1337_ = v___x_1344_;
goto v___jp_1336_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1307_);
v___y_1337_ = v___x_1345_;
goto v___jp_1336_;
}
v___jp_1319_:
{
uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1321_ = 1;
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
v___x_1323_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__1));
v___x_1324_ = l_Lean_Meta_appendSection(v___x_1322_, v___x_1308_, v___x_1323_, v_a_1304_, v___x_1321_);
v___x_1325_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__2));
v___x_1326_ = l_Lean_Meta_appendSection(v___x_1324_, v___x_1308_, v___x_1325_, v_a_1307_, v___x_1321_);
v___x_1327_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__3));
v___x_1328_ = l_Lean_Meta_appendSection(v___x_1326_, v___x_1308_, v___x_1327_, v_a_1310_, v___x_1321_);
v___x_1329_ = ((lean_object*)(l_Lean_Meta_Simp_mkDiagMessages___closed__4));
v___x_1330_ = l_Lean_Meta_appendSection(v___x_1328_, v___x_1308_, v___x_1329_, v_a_1315_, v___y_1320_);
v___x_1331_ = lean_obj_once(&l_Lean_Meta_Simp_mkDiagMessages___closed__7, &l_Lean_Meta_Simp_mkDiagMessages___closed__7_once, _init_l_Lean_Meta_Simp_mkDiagMessages___closed__7);
v___x_1332_ = lean_array_push(v___x_1330_, v___x_1331_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1332_);
v___x_1334_ = v___x_1317_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
v___jp_1336_:
{
if (v___y_1337_ == 0)
{
lean_del_object(v___x_1312_);
v___y_1320_ = v___y_1337_;
goto v___jp_1319_;
}
else
{
uint8_t v___x_1338_; 
v___x_1338_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1310_);
if (v___x_1338_ == 0)
{
lean_del_object(v___x_1312_);
v___y_1320_ = v___x_1338_;
goto v___jp_1319_;
}
else
{
uint8_t v___x_1339_; 
v___x_1339_ = l_Lean_Meta_DiagSummary_isEmpty(v_a_1315_);
if (v___x_1339_ == 0)
{
lean_del_object(v___x_1312_);
v___y_1320_ = v___x_1339_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_del_object(v___x_1317_);
lean_dec(v_a_1315_);
lean_dec(v_a_1310_);
lean_dec(v_a_1307_);
lean_dec(v_a_1304_);
v___x_1340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__0));
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1340_);
v___x_1342_ = v___x_1312_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_del_object(v___x_1312_);
lean_dec(v_a_1310_);
lean_dec(v_a_1307_);
lean_dec(v_a_1304_);
v_a_1347_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1314_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1314_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_a_1307_);
lean_dec(v_a_1304_);
v_a_1356_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1309_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1309_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_a_1304_);
v_a_1364_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1306_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1306_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1303_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1303_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDiagMessages___boxed(lean_object* v_diag_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Meta_Simp_mkDiagMessages(v_diag_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec_ref(v_diag_1380_);
return v_res_1386_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1395_, uint8_t v___y_1396_, lean_object* v_x_1397_){
_start:
{
if (lean_obj_tag(v_x_1397_) == 1)
{
lean_object* v_pre_1398_; 
v_pre_1398_ = lean_ctor_get(v_x_1397_, 0);
switch(lean_obj_tag(v_pre_1398_))
{
case 1:
{
lean_object* v_pre_1399_; 
v_pre_1399_ = lean_ctor_get(v_pre_1398_, 0);
switch(lean_obj_tag(v_pre_1399_))
{
case 0:
{
lean_object* v_str_1400_; lean_object* v_str_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_str_1400_ = lean_ctor_get(v_x_1397_, 1);
v_str_1401_ = lean_ctor_get(v_pre_1398_, 1);
v___x_1402_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1403_ = lean_string_dec_eq(v_str_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1405_ = lean_string_dec_eq(v_str_1401_, v___x_1404_);
if (v___x_1405_ == 0)
{
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1407_ = lean_string_dec_eq(v_str_1400_, v___x_1406_);
if (v___x_1407_ == 0)
{
return v___x_1407_;
}
else
{
return v_suppressElabErrors_1395_;
}
}
}
else
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1409_ = lean_string_dec_eq(v_str_1400_, v___x_1408_);
if (v___x_1409_ == 0)
{
return v___x_1409_;
}
else
{
return v_suppressElabErrors_1395_;
}
}
}
case 1:
{
lean_object* v_pre_1410_; 
v_pre_1410_ = lean_ctor_get(v_pre_1399_, 0);
if (lean_obj_tag(v_pre_1410_) == 0)
{
lean_object* v_str_1411_; lean_object* v_str_1412_; lean_object* v_str_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_str_1411_ = lean_ctor_get(v_x_1397_, 1);
v_str_1412_ = lean_ctor_get(v_pre_1398_, 1);
v_str_1413_ = lean_ctor_get(v_pre_1399_, 1);
v___x_1414_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1415_ = lean_string_dec_eq(v_str_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1417_ = lean_string_dec_eq(v_str_1412_, v___x_1416_);
if (v___x_1417_ == 0)
{
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_1419_ = lean_string_dec_eq(v_str_1411_, v___x_1418_);
if (v___x_1419_ == 0)
{
return v___x_1419_;
}
else
{
return v_suppressElabErrors_1395_;
}
}
}
}
else
{
return v___y_1396_;
}
}
default: 
{
return v___y_1396_;
}
}
}
case 0:
{
lean_object* v_str_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_str_1420_ = lean_ctor_get(v_x_1397_, 1);
v___x_1421_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_1422_ = lean_string_dec_eq(v_str_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
return v___x_1422_;
}
else
{
return v_suppressElabErrors_1395_;
}
}
default: 
{
return v___y_1396_;
}
}
}
else
{
return v___y_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1423_, lean_object* v___y_1424_, lean_object* v_x_1425_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1426_; uint8_t v___y_6601__boxed_1427_; uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_suppressElabErrors_boxed_1426_ = lean_unbox(v_suppressElabErrors_1423_);
v___y_6601__boxed_1427_ = lean_unbox(v___y_1424_);
v_res_1428_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1426_, v___y_6601__boxed_1427_, v_x_1425_);
lean_dec(v_x_1425_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_1430_, lean_object* v_opt_1431_){
_start:
{
lean_object* v_name_1432_; lean_object* v_defValue_1433_; lean_object* v_map_1434_; lean_object* v___x_1435_; 
v_name_1432_ = lean_ctor_get(v_opt_1431_, 0);
v_defValue_1433_ = lean_ctor_get(v_opt_1431_, 1);
v_map_1434_ = lean_ctor_get(v_opts_1430_, 0);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1434_, v_name_1432_);
if (lean_obj_tag(v___x_1435_) == 0)
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_unbox(v_defValue_1433_);
return v___x_1436_;
}
else
{
lean_object* v_val_1437_; 
v_val_1437_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v___x_1435_, 1);
if (lean_obj_tag(v_val_1437_) == 1)
{
uint8_t v_v_1438_; 
v_v_1438_ = lean_ctor_get_uint8(v_val_1437_, 0);
lean_dec_ref_known(v_val_1437_, 0);
return v_v_1438_;
}
else
{
uint8_t v___x_1439_; 
lean_dec(v_val_1437_);
v___x_1439_ = lean_unbox(v_defValue_1433_);
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_1440_, lean_object* v_opt_1441_){
_start:
{
uint8_t v_res_1442_; lean_object* v_r_1443_; 
v_res_1442_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_opts_1440_, v_opt_1441_);
lean_dec_ref(v_opt_1441_);
lean_dec_ref(v_opts_1440_);
v_r_1443_ = lean_box(v_res_1442_);
return v_r_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v_env_1451_; lean_object* v___x_1452_; lean_object* v_toCold_1453_; lean_object* v_mctx_1454_; lean_object* v_lctx_1455_; lean_object* v_options_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1450_ = lean_st_ref_get(v___y_1448_);
v_env_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_env_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = lean_st_ref_get(v___y_1446_);
v_toCold_1453_ = lean_ctor_get(v___y_1447_, 0);
v_mctx_1454_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_mctx_1454_);
lean_dec(v___x_1452_);
v_lctx_1455_ = lean_ctor_get(v___y_1445_, 2);
v_options_1456_ = lean_ctor_get(v_toCold_1453_, 2);
lean_inc_ref(v_options_1456_);
lean_inc_ref(v_lctx_1455_);
v___x_1457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1457_, 0, v_env_1451_);
lean_ctor_set(v___x_1457_, 1, v_mctx_1454_);
lean_ctor_set(v___x_1457_, 2, v_lctx_1455_);
lean_ctor_set(v___x_1457_, 3, v_options_1456_);
v___x_1458_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v_msgData_1444_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v_msgData_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(lean_object* v_ref_1467_, lean_object* v_msgData_1468_, uint8_t v_severity_1469_, uint8_t v_isSilent_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v_currNamespace_1484_; lean_object* v_openDecls_1485_; lean_object* v___y_1486_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; uint8_t v___y_1517_; uint8_t v___y_1518_; lean_object* v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; uint8_t v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1545_; uint8_t v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; uint8_t v___y_1558_; uint8_t v___y_1559_; uint8_t v___y_1560_; uint8_t v___x_1565_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; uint8_t v___y_1573_; uint8_t v___y_1574_; uint8_t v___y_1575_; uint8_t v___y_1577_; uint8_t v___x_1595_; 
v___x_1565_ = 2;
v___x_1595_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1469_, v___x_1565_);
if (v___x_1595_ == 0)
{
v___y_1577_ = v___x_1595_;
goto v___jp_1576_;
}
else
{
uint8_t v___x_1596_; 
lean_inc_ref(v_msgData_1468_);
v___x_1596_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1468_);
v___y_1577_ = v___x_1596_;
goto v___jp_1576_;
}
v___jp_1476_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_env_1491_; lean_object* v_nextMacroScope_1492_; lean_object* v_ngen_1493_; lean_object* v_auxDeclNGen_1494_; lean_object* v_traceState_1495_; lean_object* v_cache_1496_; lean_object* v_messages_1497_; lean_object* v_infoState_1498_; lean_object* v_snapshotTasks_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1510_; 
lean_inc(v_openDecls_1485_);
lean_inc(v_currNamespace_1484_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_currNamespace_1484_);
lean_ctor_set(v___x_1487_, 1, v_openDecls_1485_);
v___x_1488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___y_1479_);
lean_inc_ref(v___y_1482_);
lean_inc_ref(v___y_1478_);
v___x_1489_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1489_, 0, v___y_1478_);
lean_ctor_set(v___x_1489_, 1, v___y_1481_);
lean_ctor_set(v___x_1489_, 2, v___y_1483_);
lean_ctor_set(v___x_1489_, 3, v___y_1482_);
lean_ctor_set(v___x_1489_, 4, v___x_1488_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*5, v___y_1477_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*5 + 1, v___y_1480_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*5 + 2, v_isSilent_1470_);
v___x_1490_ = lean_st_ref_take(v___y_1486_);
v_env_1491_ = lean_ctor_get(v___x_1490_, 0);
v_nextMacroScope_1492_ = lean_ctor_get(v___x_1490_, 1);
v_ngen_1493_ = lean_ctor_get(v___x_1490_, 2);
v_auxDeclNGen_1494_ = lean_ctor_get(v___x_1490_, 3);
v_traceState_1495_ = lean_ctor_get(v___x_1490_, 4);
v_cache_1496_ = lean_ctor_get(v___x_1490_, 5);
v_messages_1497_ = lean_ctor_get(v___x_1490_, 6);
v_infoState_1498_ = lean_ctor_get(v___x_1490_, 7);
v_snapshotTasks_1499_ = lean_ctor_get(v___x_1490_, 8);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1501_ = v___x_1490_;
v_isShared_1502_ = v_isSharedCheck_1510_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snapshotTasks_1499_);
lean_inc(v_infoState_1498_);
lean_inc(v_messages_1497_);
lean_inc(v_cache_1496_);
lean_inc(v_traceState_1495_);
lean_inc(v_auxDeclNGen_1494_);
lean_inc(v_ngen_1493_);
lean_inc(v_nextMacroScope_1492_);
lean_inc(v_env_1491_);
lean_dec(v___x_1490_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1510_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Lean_MessageLog_add(v___x_1489_, v_messages_1497_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 6, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_env_1491_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_nextMacroScope_1492_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_ngen_1493_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_auxDeclNGen_1494_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_traceState_1495_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v_cache_1496_);
lean_ctor_set(v_reuseFailAlloc_1509_, 6, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1509_, 7, v_infoState_1498_);
lean_ctor_set(v_reuseFailAlloc_1509_, 8, v_snapshotTasks_1499_);
v___x_1506_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_st_ref_put(v___y_1486_, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1503_);
return v___x_1508_;
}
}
}
v___jp_1511_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1537_; 
v___x_1522_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1468_);
v___x_1523_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__4(v___x_1522_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1537_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1537_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_inc_ref_n(v___y_1515_, 2);
v___x_1528_ = l_Lean_FileMap_toPosition(v___y_1515_, v___y_1519_);
lean_dec(v___y_1519_);
v___x_1529_ = l_Lean_FileMap_toPosition(v___y_1515_, v___y_1521_);
lean_dec(v___y_1521_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___x_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
if (v___y_1520_ == 0)
{
lean_del_object(v___x_1526_);
lean_dec_ref(v___y_1513_);
v___y_1477_ = v___y_1517_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v_a_1524_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___x_1528_;
v___y_1482_ = v___x_1531_;
v___y_1483_ = v___x_1530_;
v_currNamespace_1484_ = v___y_1514_;
v_openDecls_1485_ = v___y_1512_;
v___y_1486_ = v___y_1474_;
goto v___jp_1476_;
}
else
{
uint8_t v___x_1532_; 
lean_inc(v_a_1524_);
v___x_1532_ = l_Lean_MessageData_hasTag(v___y_1513_, v_a_1524_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
lean_dec_ref_known(v___x_1530_, 1);
lean_dec_ref(v___x_1528_);
lean_dec(v_a_1524_);
v___x_1533_ = lean_box(0);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1533_);
v___x_1535_ = v___x_1526_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_del_object(v___x_1526_);
v___y_1477_ = v___y_1517_;
v___y_1478_ = v___y_1516_;
v___y_1479_ = v_a_1524_;
v___y_1480_ = v___y_1518_;
v___y_1481_ = v___x_1528_;
v___y_1482_ = v___x_1531_;
v___y_1483_ = v___x_1530_;
v_currNamespace_1484_ = v___y_1514_;
v_openDecls_1485_ = v___y_1512_;
v___y_1486_ = v___y_1474_;
goto v___jp_1476_;
}
}
}
}
v___jp_1538_:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Syntax_getTailPos_x3f(v___y_1547_, v___y_1543_);
lean_dec(v___y_1547_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_inc(v___y_1548_);
v___y_1512_ = v___y_1539_;
v___y_1513_ = v___y_1540_;
v___y_1514_ = v___y_1541_;
v___y_1515_ = v___y_1542_;
v___y_1516_ = v___y_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___y_1545_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___y_1546_;
v___y_1521_ = v___y_1548_;
goto v___jp_1511_;
}
else
{
lean_object* v_val_1550_; 
v_val_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___y_1512_ = v___y_1539_;
v___y_1513_ = v___y_1540_;
v___y_1514_ = v___y_1541_;
v___y_1515_ = v___y_1542_;
v___y_1516_ = v___y_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___y_1545_;
v___y_1519_ = v___y_1548_;
v___y_1520_ = v___y_1546_;
v___y_1521_ = v_val_1550_;
goto v___jp_1511_;
}
}
v___jp_1551_:
{
lean_object* v_ref_1561_; lean_object* v___x_1562_; 
v_ref_1561_ = l_Lean_replaceRef(v_ref_1467_, v___y_1556_);
v___x_1562_ = l_Lean_Syntax_getPos_x3f(v_ref_1561_, v___y_1558_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___y_1539_ = v___y_1552_;
v___y_1540_ = v___y_1553_;
v___y_1541_ = v___y_1554_;
v___y_1542_ = v___y_1555_;
v___y_1543_ = v___y_1558_;
v___y_1544_ = v___y_1557_;
v___y_1545_ = v___y_1560_;
v___y_1546_ = v___y_1559_;
v___y_1547_ = v_ref_1561_;
v___y_1548_ = v___x_1563_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1564_; 
v_val_1564_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v___x_1562_, 1);
v___y_1539_ = v___y_1552_;
v___y_1540_ = v___y_1553_;
v___y_1541_ = v___y_1554_;
v___y_1542_ = v___y_1555_;
v___y_1543_ = v___y_1558_;
v___y_1544_ = v___y_1557_;
v___y_1545_ = v___y_1560_;
v___y_1546_ = v___y_1559_;
v___y_1547_ = v_ref_1561_;
v___y_1548_ = v_val_1564_;
goto v___jp_1538_;
}
}
v___jp_1566_:
{
if (v___y_1575_ == 0)
{
v___y_1552_ = v___y_1567_;
v___y_1553_ = v___y_1570_;
v___y_1554_ = v___y_1571_;
v___y_1555_ = v___y_1568_;
v___y_1556_ = v___y_1572_;
v___y_1557_ = v___y_1569_;
v___y_1558_ = v___y_1573_;
v___y_1559_ = v___y_1574_;
v___y_1560_ = v_severity_1469_;
goto v___jp_1551_;
}
else
{
v___y_1552_ = v___y_1567_;
v___y_1553_ = v___y_1570_;
v___y_1554_ = v___y_1571_;
v___y_1555_ = v___y_1568_;
v___y_1556_ = v___y_1572_;
v___y_1557_ = v___y_1569_;
v___y_1558_ = v___y_1573_;
v___y_1559_ = v___y_1574_;
v___y_1560_ = v___x_1565_;
goto v___jp_1551_;
}
}
v___jp_1576_:
{
if (v___y_1577_ == 0)
{
lean_object* v_toCold_1578_; lean_object* v_ref_1579_; uint8_t v_suppressElabErrors_1580_; lean_object* v_fileName_1581_; lean_object* v_fileMap_1582_; lean_object* v_options_1583_; lean_object* v_currNamespace_1584_; lean_object* v_openDecls_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___f_1588_; uint8_t v___x_1589_; uint8_t v___x_1590_; 
v_toCold_1578_ = lean_ctor_get(v___y_1473_, 0);
v_ref_1579_ = lean_ctor_get(v___y_1473_, 2);
v_suppressElabErrors_1580_ = lean_ctor_get_uint8(v___y_1473_, sizeof(void*)*3 + 1);
v_fileName_1581_ = lean_ctor_get(v_toCold_1578_, 0);
v_fileMap_1582_ = lean_ctor_get(v_toCold_1578_, 1);
v_options_1583_ = lean_ctor_get(v_toCold_1578_, 2);
v_currNamespace_1584_ = lean_ctor_get(v_toCold_1578_, 4);
v_openDecls_1585_ = lean_ctor_get(v_toCold_1578_, 5);
v___x_1586_ = lean_box(v_suppressElabErrors_1580_);
v___x_1587_ = lean_box(v___y_1577_);
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1588_, 0, v___x_1586_);
lean_closure_set(v___f_1588_, 1, v___x_1587_);
v___x_1589_ = 1;
v___x_1590_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1469_, v___x_1589_);
if (v___x_1590_ == 0)
{
v___y_1567_ = v_openDecls_1585_;
v___y_1568_ = v_fileMap_1582_;
v___y_1569_ = v_fileName_1581_;
v___y_1570_ = v___f_1588_;
v___y_1571_ = v_currNamespace_1584_;
v___y_1572_ = v_ref_1579_;
v___y_1573_ = v___y_1577_;
v___y_1574_ = v_suppressElabErrors_1580_;
v___y_1575_ = v___x_1590_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = l_Lean_warningAsError;
v___x_1592_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1_spec__5(v_options_1583_, v___x_1591_);
v___y_1567_ = v_openDecls_1585_;
v___y_1568_ = v_fileMap_1582_;
v___y_1569_ = v_fileName_1581_;
v___y_1570_ = v___f_1588_;
v___y_1571_ = v_currNamespace_1584_;
v___y_1572_ = v_ref_1579_;
v___y_1573_ = v___y_1577_;
v___y_1574_ = v_suppressElabErrors_1580_;
v___y_1575_ = v___x_1592_;
goto v___jp_1566_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec_ref(v_msgData_1468_);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1597_, lean_object* v_msgData_1598_, lean_object* v_severity_1599_, lean_object* v_isSilent_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v_severity_boxed_1606_; uint8_t v_isSilent_boxed_1607_; lean_object* v_res_1608_; 
v_severity_boxed_1606_ = lean_unbox(v_severity_1599_);
v_isSilent_boxed_1607_ = lean_unbox(v_isSilent_1600_);
v_res_1608_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_1597_, v_msgData_1598_, v_severity_boxed_1606_, v_isSilent_boxed_1607_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v_ref_1597_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(lean_object* v_msgData_1609_, uint8_t v_severity_1610_, uint8_t v_isSilent_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_ref_1617_; lean_object* v___x_1618_; 
v_ref_1617_ = lean_ctor_get(v___y_1614_, 2);
v___x_1618_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0_spec__1(v_ref_1617_, v_msgData_1609_, v_severity_1610_, v_isSilent_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0___boxed(lean_object* v_msgData_1619_, lean_object* v_severity_1620_, lean_object* v_isSilent_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_severity_boxed_1627_; uint8_t v_isSilent_boxed_1628_; lean_object* v_res_1629_; 
v_severity_boxed_1627_ = lean_unbox(v_severity_1620_);
v_isSilent_boxed_1628_ = lean_unbox(v_isSilent_1621_);
v_res_1629_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(v_msgData_1619_, v_severity_boxed_1627_, v_isSilent_boxed_1628_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(lean_object* v_msgData_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = 0;
v___x_1637_ = 0;
v___x_1638_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0_spec__0(v_msgData_1630_, v___x_1636_, v___x_1637_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0___boxed(lean_object* v_msgData_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(v_msgData_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1645_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Meta_Simp_reportDiag___lam__0___closed__1));
v___x_1650_ = l_Lean_MessageData_ofFormat(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___lam__0(lean_object* v_diag_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Meta_Simp_mkDiagMessages(v_diag_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1677_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1677_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1677_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1662_ = lean_array_get_size(v_a_1658_);
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = lean_nat_dec_eq(v___x_1662_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; double v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_del_object(v___x_1660_);
v___x_1665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__2));
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__3);
v___x_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkSimpDiagSummary_spec__3___redArg___closed__4));
v___x_1669_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1669_, 0, v___x_1665_);
lean_ctor_set(v___x_1669_, 1, v___x_1666_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
lean_ctor_set_float(v___x_1669_, sizeof(void*)*3, v___x_1667_);
lean_ctor_set_float(v___x_1669_, sizeof(void*)*3 + 8, v___x_1667_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3 + 16, v___x_1664_);
v___x_1670_ = lean_obj_once(&l_Lean_Meta_Simp_reportDiag___lam__0___closed__2, &l_Lean_Meta_Simp_reportDiag___lam__0___closed__2_once, _init_l_Lean_Meta_Simp_reportDiag___lam__0___closed__2);
v___x_1671_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
lean_ctor_set(v___x_1671_, 2, v_a_1658_);
v___x_1672_ = l_Lean_logInfo___at___00Lean_Meta_Simp_reportDiag_spec__0(v___x_1671_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_dec(v_a_1658_);
v___x_1673_ = lean_box(0);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1673_);
v___x_1675_ = v___x_1660_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
v_a_1678_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1657_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1657_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___lam__0___boxed(lean_object* v_diag_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_Simp_reportDiag___lam__0(v_diag_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec_ref(v_diag_1686_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(lean_object* v___y_1693_, uint8_t v_isExporting_1694_, lean_object* v___x_1695_, lean_object* v___y_1696_, lean_object* v___x_1697_, lean_object* v_a_x3f_1698_){
_start:
{
lean_object* v___x_1700_; lean_object* v_env_1701_; lean_object* v_nextMacroScope_1702_; lean_object* v_ngen_1703_; lean_object* v_auxDeclNGen_1704_; lean_object* v_traceState_1705_; lean_object* v_messages_1706_; lean_object* v_infoState_1707_; lean_object* v_snapshotTasks_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1733_; 
v___x_1700_ = lean_st_ref_take(v___y_1693_);
v_env_1701_ = lean_ctor_get(v___x_1700_, 0);
v_nextMacroScope_1702_ = lean_ctor_get(v___x_1700_, 1);
v_ngen_1703_ = lean_ctor_get(v___x_1700_, 2);
v_auxDeclNGen_1704_ = lean_ctor_get(v___x_1700_, 3);
v_traceState_1705_ = lean_ctor_get(v___x_1700_, 4);
v_messages_1706_ = lean_ctor_get(v___x_1700_, 6);
v_infoState_1707_ = lean_ctor_get(v___x_1700_, 7);
v_snapshotTasks_1708_ = lean_ctor_get(v___x_1700_, 8);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1700_, 5);
lean_dec(v_unused_1734_);
v___x_1710_ = v___x_1700_;
v_isShared_1711_ = v_isSharedCheck_1733_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_snapshotTasks_1708_);
lean_inc(v_infoState_1707_);
lean_inc(v_messages_1706_);
lean_inc(v_traceState_1705_);
lean_inc(v_auxDeclNGen_1704_);
lean_inc(v_ngen_1703_);
lean_inc(v_nextMacroScope_1702_);
lean_inc(v_env_1701_);
lean_dec(v___x_1700_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1733_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = l_Lean_Environment_setExporting(v_env_1701_, v_isExporting_1694_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 5, v___x_1695_);
lean_ctor_set(v___x_1710_, 0, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_nextMacroScope_1702_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_ngen_1703_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_auxDeclNGen_1704_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_traceState_1705_);
lean_ctor_set(v_reuseFailAlloc_1732_, 5, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1732_, 6, v_messages_1706_);
lean_ctor_set(v_reuseFailAlloc_1732_, 7, v_infoState_1707_);
lean_ctor_set(v_reuseFailAlloc_1732_, 8, v_snapshotTasks_1708_);
v___x_1714_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v_mctx_1717_; lean_object* v_zetaDeltaFVarIds_1718_; lean_object* v_postponed_1719_; lean_object* v_diag_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1730_; 
v___x_1715_ = lean_st_ref_put(v___y_1693_, v___x_1714_);
v___x_1716_ = lean_st_ref_take(v___y_1696_);
v_mctx_1717_ = lean_ctor_get(v___x_1716_, 0);
v_zetaDeltaFVarIds_1718_ = lean_ctor_get(v___x_1716_, 2);
v_postponed_1719_ = lean_ctor_get(v___x_1716_, 3);
v_diag_1720_ = lean_ctor_get(v___x_1716_, 4);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v___x_1716_, 1);
lean_dec(v_unused_1731_);
v___x_1722_ = v___x_1716_;
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_diag_1720_);
lean_inc(v_postponed_1719_);
lean_inc(v_zetaDeltaFVarIds_1718_);
lean_inc(v_mctx_1717_);
lean_dec(v___x_1716_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(0);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v___x_1697_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_mctx_1717_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_zetaDeltaFVarIds_1718_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_postponed_1719_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_diag_1720_);
v___x_1726_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_st_ref_put(v___y_1696_, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1724_);
return v___x_1728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_1735_, lean_object* v_isExporting_1736_, lean_object* v___x_1737_, lean_object* v___y_1738_, lean_object* v___x_1739_, lean_object* v_a_x3f_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_isExporting_boxed_1742_; lean_object* v_res_1743_; 
v_isExporting_boxed_1742_ = lean_unbox(v_isExporting_1736_);
v_res_1743_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1735_, v_isExporting_boxed_1742_, v___x_1737_, v___y_1738_, v___x_1739_, v_a_x3f_1740_);
lean_dec(v_a_x3f_1740_);
lean_dec(v___y_1738_);
lean_dec(v___y_1735_);
return v_res_1743_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1744_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__0);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__1);
v___x_1750_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
lean_ctor_set(v___x_1750_, 2, v___x_1749_);
lean_ctor_set(v___x_1750_, 3, v___x_1749_);
lean_ctor_set(v___x_1750_, 4, v___x_1749_);
lean_ctor_set(v___x_1750_, 5, v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(lean_object* v_x_1751_, uint8_t v_isExporting_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; lean_object* v_env_1759_; lean_object* v___x_1760_; uint8_t v_isModule_1761_; 
v___x_1758_ = lean_st_ref_get(v___y_1756_);
v_env_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc_ref(v_env_1759_);
lean_dec(v___x_1758_);
v___x_1760_ = l_Lean_Environment_header(v_env_1759_);
v_isModule_1761_ = lean_ctor_get_uint8(v___x_1760_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1760_);
if (v_isModule_1761_ == 0)
{
lean_object* v___x_1762_; 
lean_dec_ref(v_env_1759_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
lean_inc(v___y_1754_);
lean_inc_ref(v___y_1753_);
v___x_1762_ = lean_apply_5(v_x_1751_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, lean_box(0));
return v___x_1762_;
}
else
{
uint8_t v_isExporting_1763_; 
v_isExporting_1763_ = lean_ctor_get_uint8(v_env_1759_, sizeof(void*)*8);
lean_dec_ref(v_env_1759_);
if (v_isExporting_1752_ == 0)
{
if (v_isExporting_1763_ == 0)
{
lean_object* v___x_1829_; 
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
lean_inc(v___y_1754_);
lean_inc_ref(v___y_1753_);
v___x_1829_ = lean_apply_5(v_x_1751_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, lean_box(0));
return v___x_1829_;
}
else
{
goto v___jp_1764_;
}
}
else
{
if (v_isExporting_1763_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1830_; 
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
lean_inc(v___y_1754_);
lean_inc_ref(v___y_1753_);
v___x_1830_ = lean_apply_5(v_x_1751_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, lean_box(0));
return v___x_1830_;
}
}
v___jp_1764_:
{
lean_object* v___x_1765_; lean_object* v_env_1766_; lean_object* v_nextMacroScope_1767_; lean_object* v_ngen_1768_; lean_object* v_auxDeclNGen_1769_; lean_object* v_traceState_1770_; lean_object* v_messages_1771_; lean_object* v_infoState_1772_; lean_object* v_snapshotTasks_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1827_; 
v___x_1765_ = lean_st_ref_take(v___y_1756_);
v_env_1766_ = lean_ctor_get(v___x_1765_, 0);
v_nextMacroScope_1767_ = lean_ctor_get(v___x_1765_, 1);
v_ngen_1768_ = lean_ctor_get(v___x_1765_, 2);
v_auxDeclNGen_1769_ = lean_ctor_get(v___x_1765_, 3);
v_traceState_1770_ = lean_ctor_get(v___x_1765_, 4);
v_messages_1771_ = lean_ctor_get(v___x_1765_, 6);
v_infoState_1772_ = lean_ctor_get(v___x_1765_, 7);
v_snapshotTasks_1773_ = lean_ctor_get(v___x_1765_, 8);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1765_, 5);
lean_dec(v_unused_1828_);
v___x_1775_ = v___x_1765_;
v_isShared_1776_ = v_isSharedCheck_1827_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_snapshotTasks_1773_);
lean_inc(v_infoState_1772_);
lean_inc(v_messages_1771_);
lean_inc(v_traceState_1770_);
lean_inc(v_auxDeclNGen_1769_);
lean_inc(v_ngen_1768_);
lean_inc(v_nextMacroScope_1767_);
lean_inc(v_env_1766_);
lean_dec(v___x_1765_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1827_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1777_ = l_Lean_Environment_setExporting(v_env_1766_, v_isExporting_1752_);
v___x_1778_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__2);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 5, v___x_1778_);
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1780_ = v___x_1775_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_nextMacroScope_1767_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_ngen_1768_);
lean_ctor_set(v_reuseFailAlloc_1826_, 3, v_auxDeclNGen_1769_);
lean_ctor_set(v_reuseFailAlloc_1826_, 4, v_traceState_1770_);
lean_ctor_set(v_reuseFailAlloc_1826_, 5, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1826_, 6, v_messages_1771_);
lean_ctor_set(v_reuseFailAlloc_1826_, 7, v_infoState_1772_);
lean_ctor_set(v_reuseFailAlloc_1826_, 8, v_snapshotTasks_1773_);
v___x_1780_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_mctx_1783_; lean_object* v_zetaDeltaFVarIds_1784_; lean_object* v_postponed_1785_; lean_object* v_diag_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1824_; 
v___x_1781_ = lean_st_ref_put(v___y_1756_, v___x_1780_);
v___x_1782_ = lean_st_ref_take(v___y_1754_);
v_mctx_1783_ = lean_ctor_get(v___x_1782_, 0);
v_zetaDeltaFVarIds_1784_ = lean_ctor_get(v___x_1782_, 2);
v_postponed_1785_ = lean_ctor_get(v___x_1782_, 3);
v_diag_1786_ = lean_ctor_get(v___x_1782_, 4);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1782_, 1);
lean_dec(v_unused_1825_);
v___x_1788_ = v___x_1782_;
v_isShared_1789_ = v_isSharedCheck_1824_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_diag_1786_);
lean_inc(v_postponed_1785_);
lean_inc(v_zetaDeltaFVarIds_1784_);
lean_inc(v_mctx_1783_);
lean_dec(v___x_1782_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1824_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1790_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___closed__3);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v___x_1790_);
v___x_1792_ = v___x_1788_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_mctx_1783_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_zetaDeltaFVarIds_1784_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_postponed_1785_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_diag_1786_);
v___x_1792_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v_r_1794_; 
v___x_1793_ = lean_st_ref_put(v___y_1754_, v___x_1792_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
lean_inc(v___y_1754_);
lean_inc_ref(v___y_1753_);
v_r_1794_ = lean_apply_5(v_x_1751_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, lean_box(0));
if (lean_obj_tag(v_r_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1811_; 
v_a_1795_ = lean_ctor_get(v_r_1794_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_r_1794_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1797_ = v_r_1794_;
v_isShared_1798_ = v_isSharedCheck_1811_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v_r_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1811_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
lean_inc(v_a_1795_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 1);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v___x_1801_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1756_, v_isExporting_1763_, v___x_1778_, v___y_1754_, v___x_1790_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1801_, 0);
lean_dec(v_unused_1809_);
v___x_1803_ = v___x_1801_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v___x_1801_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_a_1795_);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1795_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1812_ = lean_ctor_get(v_r_1794_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v_r_1794_, 1);
v___x_1813_ = lean_box(0);
v___x_1814_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___lam__0(v___y_1756_, v_isExporting_1763_, v___x_1778_, v___y_1754_, v___x_1790_, v___x_1813_);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1814_, 0);
lean_dec(v_unused_1822_);
v___x_1816_ = v___x_1814_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v___x_1814_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 1);
lean_ctor_set(v___x_1816_, 0, v_a_1812_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1812_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg___boxed(lean_object* v_x_1831_, lean_object* v_isExporting_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v_isExporting_boxed_1838_; lean_object* v_res_1839_; 
v_isExporting_boxed_1838_ = lean_unbox(v_isExporting_1832_);
v_res_1839_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1831_, v_isExporting_boxed_1838_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(lean_object* v_x_1840_, uint8_t v_when_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
if (v_when_1841_ == 0)
{
lean_object* v___x_1847_; 
lean_inc(v___y_1845_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1843_);
lean_inc_ref(v___y_1842_);
v___x_1847_ = lean_apply_5(v_x_1840_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, lean_box(0));
return v___x_1847_;
}
else
{
uint8_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = 0;
v___x_1849_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1840_, v___x_1848_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg___boxed(lean_object* v_x_1850_, lean_object* v_when_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v_when_boxed_1857_; lean_object* v_res_1858_; 
v_when_boxed_1857_ = lean_unbox(v_when_1851_);
v_res_1858_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v_x_1850_, v_when_boxed_1857_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag(lean_object* v_diag_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___f_1865_; lean_object* v___x_1866_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_reportDiag___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1865_, 0, v_diag_1859_);
v___x_1866_ = l_Lean_isDiagnosticsEnabled___redArg(v_a_1862_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1878_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_unbox(v_a_1867_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec(v_a_1867_);
lean_dec_ref(v___f_1865_);
v___x_1872_ = lean_box(0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
else
{
uint8_t v___x_1876_; lean_object* v___x_1877_; 
lean_del_object(v___x_1869_);
v___x_1876_ = lean_unbox(v_a_1867_);
lean_dec(v_a_1867_);
v___x_1877_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v___f_1865_, v___x_1876_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v___f_1865_);
v_a_1879_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1866_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1866_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_reportDiag___boxed(lean_object* v_diag_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Meta_Simp_reportDiag(v_diag_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(lean_object* v_00_u03b1_1894_, lean_object* v_x_1895_, uint8_t v_isExporting_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___redArg(v_x_1895_, v_isExporting_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_x_1904_, lean_object* v_isExporting_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v_isExporting_boxed_1911_; lean_object* v_res_1912_; 
v_isExporting_boxed_1911_ = lean_unbox(v_isExporting_1905_);
v_res_1912_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1_spec__2(v_00_u03b1_1903_, v_x_1904_, v_isExporting_boxed_1911_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(lean_object* v_00_u03b1_1913_, lean_object* v_x_1914_, uint8_t v_when_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___redArg(v_x_1914_, v_when_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1___boxed(lean_object* v_00_u03b1_1922_, lean_object* v_x_1923_, lean_object* v_when_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v_when_boxed_1930_; lean_object* v_res_1931_; 
v_when_boxed_1930_ = lean_unbox(v_when_1924_);
v_res_1931_ = l_Lean_withoutExporting___at___00Lean_Meta_Simp_reportDiag_spec__1(v_00_u03b1_1922_, v_x_1923_, v_when_boxed_1930_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1931_;
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
