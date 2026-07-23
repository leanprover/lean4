// Lean compiler output
// Module: Lean.PostprocessTraces.Postprocessors
// Imports: public import Lean.PostprocessTraces.Basic import Lean.CoreM
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
lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PostprocessTraces_TraceTree_children(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object*, lean_object*);
lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object*);
uint8_t l_Lean_instBEqTraceResult_beq(uint8_t, uint8_t);
lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t lean_float_beq(double, double);
double l_Lean_PostprocessTraces_TraceTree_selfElapsed(lean_object*);
double lean_float_mul(double, double);
double round(double);
uint64_t lean_float_to_uint64(double);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_float_decLe(double, double);
double l_Lean_PostprocessTraces_TraceTree_elapsed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PostprocessTraces_succeeded___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_succeeded___redArg___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_succeeded___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PostprocessTraces_failed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_failed___redArg___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_failed___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PostprocessTraces_errored___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_errored___redArg___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_errored___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg(double, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs(double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg(double, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs(double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__0_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1;
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " node"};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__2 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__2_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3;
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__4 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__4_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5;
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__6 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__6_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__7 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0;
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__1 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__1_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ms"};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__2 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(double);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0;
static const lean_string_object l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " (self: "};
static const lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__1 = (const lean_object*)&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__1_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(lean_object* v_s_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
switch(lean_obj_tag(v_a_4_))
{
case 0:
{
lean_object* v_pos_7_; lean_object* v___x_8_; 
v_pos_7_ = lean_ctor_get(v_a_4_, 0);
lean_inc(v_pos_7_);
lean_dec_ref_known(v_a_4_, 1);
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v_pos_7_);
return v___x_8_;
}
case 1:
{
lean_object* v_pos_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_18_; 
v_pos_9_ = lean_ctor_get(v_a_4_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_18_ == 0)
{
v___x_11_ = v_a_4_;
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_pos_9_);
lean_dec(v_a_4_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_13_ = lean_string_utf8_next_fast(v_s_1_, v_pos_9_);
lean_dec(v_pos_9_);
if (v_isShared_12_ == 0)
{
lean_ctor_set_tag(v___x_11_, 0);
lean_ctor_set(v___x_11_, 0, v___x_13_);
v___x_15_ = v___x_11_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_13_);
v___x_15_ = v_reuseFailAlloc_17_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
v_a_4_ = v___x_15_;
v_b_5_ = v___x_6_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_19_; lean_object* v_table_20_; lean_object* v_stackPos_21_; lean_object* v_needlePos_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_73_; 
v_needle_19_ = lean_ctor_get(v_a_4_, 0);
v_table_20_ = lean_ctor_get(v_a_4_, 1);
v_stackPos_21_ = lean_ctor_get(v_a_4_, 2);
v_needlePos_22_ = lean_ctor_get(v_a_4_, 3);
v_isSharedCheck_73_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_73_ == 0)
{
v___x_24_ = v_a_4_;
v_isShared_25_ = v_isSharedCheck_73_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_needlePos_22_);
lean_inc(v_stackPos_21_);
lean_inc(v_table_20_);
lean_inc(v_needle_19_);
lean_dec(v_a_4_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_73_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v_str_26_; lean_object* v_startInclusive_27_; lean_object* v_endExclusive_28_; lean_object* v_basePos_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_str_26_ = lean_ctor_get(v_needle_19_, 0);
v_startInclusive_27_ = lean_ctor_get(v_needle_19_, 1);
v_endExclusive_28_ = lean_ctor_get(v_needle_19_, 2);
v_basePos_29_ = lean_nat_sub(v_stackPos_21_, v_needlePos_22_);
v___x_30_ = lean_nat_sub(v_endExclusive_28_, v_startInclusive_27_);
v___x_31_ = lean_nat_add(v_basePos_29_, v___x_30_);
v___x_32_ = lean_nat_dec_le(v___x_31_, v___x_3_);
lean_dec(v___x_31_);
if (v___x_32_ == 0)
{
uint8_t v___x_33_; 
lean_dec(v___x_30_);
lean_del_object(v___x_24_);
lean_dec(v_needlePos_22_);
lean_dec(v_stackPos_21_);
lean_dec_ref(v_table_20_);
lean_dec_ref(v_needle_19_);
v___x_33_ = lean_nat_dec_lt(v_basePos_29_, v___x_3_);
lean_dec(v_basePos_29_);
if (v___x_33_ == 0)
{
lean_inc(v_b_5_);
return v_b_5_;
}
else
{
lean_object* v___x_34_; 
v___x_34_ = lean_box(3);
v_a_4_ = v___x_34_;
v_b_5_ = v___x_6_;
goto _start;
}
}
else
{
uint8_t v_stackByte_36_; lean_object* v___x_37_; uint8_t v_patByte_38_; uint8_t v___x_39_; 
lean_dec(v_basePos_29_);
lean_inc(v_stackPos_21_);
v_stackByte_36_ = lean_string_get_byte_fast(v_s_1_, v_stackPos_21_);
v___x_37_ = lean_nat_add(v_startInclusive_27_, v_needlePos_22_);
v_patByte_38_ = lean_string_get_byte_fast(v_str_26_, v___x_37_);
v___x_39_ = lean_uint8_dec_eq(v_stackByte_36_, v_patByte_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; uint8_t v___x_41_; 
lean_dec(v___x_30_);
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = lean_nat_dec_eq(v_needlePos_22_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_newNeedlePos_44_; uint8_t v___x_45_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_sub(v_needlePos_22_, v___x_42_);
lean_dec(v_needlePos_22_);
v_newNeedlePos_44_ = lean_array_fget_borrowed(v_table_20_, v___x_43_);
lean_dec(v___x_43_);
v___x_45_ = lean_nat_dec_eq(v_newNeedlePos_44_, v___x_40_);
if (v___x_45_ == 0)
{
lean_object* v___x_47_; 
lean_inc(v_newNeedlePos_44_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v_newNeedlePos_44_);
v___x_47_ = v___x_24_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v_stackPos_21_);
lean_ctor_set(v_reuseFailAlloc_49_, 3, v_newNeedlePos_44_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
v_a_4_ = v___x_47_;
v_b_5_ = v___x_6_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_50_; lean_object* v___x_52_; 
v_nextStackPos_50_ = l_String_Slice_posGE___redArg(v___x_2_, v_stackPos_21_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v___x_40_);
lean_ctor_set(v___x_24_, 2, v_nextStackPos_50_);
v___x_52_ = v___x_24_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_54_, 2, v_nextStackPos_50_);
lean_ctor_set(v_reuseFailAlloc_54_, 3, v___x_40_);
v___x_52_ = v_reuseFailAlloc_54_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
v_a_4_ = v___x_52_;
v_b_5_ = v___x_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_nextStackPos_57_; lean_object* v___x_59_; 
lean_dec(v_needlePos_22_);
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v_stackPos_21_, v___x_55_);
lean_dec(v_stackPos_21_);
v_nextStackPos_57_ = l_String_Slice_posGE___redArg(v___x_2_, v___x_56_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v___x_40_);
lean_ctor_set(v___x_24_, 2, v_nextStackPos_57_);
v___x_59_ = v___x_24_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v_nextStackPos_57_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v___x_40_);
v___x_59_ = v_reuseFailAlloc_61_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
v_a_4_ = v___x_59_;
v_b_5_ = v___x_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_62_; lean_object* v_nextStackPos_63_; lean_object* v_nextNeedlePos_64_; uint8_t v___x_65_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v_nextStackPos_63_ = lean_nat_add(v_stackPos_21_, v___x_62_);
lean_dec(v_stackPos_21_);
v_nextNeedlePos_64_ = lean_nat_add(v_needlePos_22_, v___x_62_);
lean_dec(v_needlePos_22_);
v___x_65_ = lean_nat_dec_eq(v_nextNeedlePos_64_, v___x_30_);
lean_dec(v___x_30_);
if (v___x_65_ == 0)
{
lean_object* v___x_67_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v_nextNeedlePos_64_);
lean_ctor_set(v___x_24_, 2, v_nextStackPos_63_);
v___x_67_ = v___x_24_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v_nextStackPos_63_);
lean_ctor_set(v_reuseFailAlloc_69_, 3, v_nextNeedlePos_64_);
v___x_67_ = v_reuseFailAlloc_69_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
v_a_4_ = v___x_67_;
goto _start;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_del_object(v___x_24_);
lean_dec_ref(v_table_20_);
lean_dec_ref(v_needle_19_);
v___x_70_ = lean_nat_sub(v_nextStackPos_63_, v_nextNeedlePos_64_);
lean_dec(v_nextNeedlePos_64_);
lean_dec(v_nextStackPos_63_);
v___x_71_ = l_String_Slice_pos_x21(v___x_2_, v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
}
}
}
default: 
{
lean_inc(v_b_5_);
return v_b_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg___boxed(lean_object* v_s_74_, lean_object* v___x_75_, lean_object* v___x_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_74_, v___x_75_, v___x_76_, v_a_77_, v_b_78_);
lean_dec(v_b_78_);
lean_dec(v___x_76_);
lean_dec_ref(v___x_75_);
lean_dec_ref(v_s_74_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(lean_object* v_s_82_, lean_object* v_pat_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___y_88_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_string_utf8_byte_size(v_s_82_);
lean_inc_ref(v_s_82_);
v___x_86_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_86_, 0, v_s_82_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_85_);
v___x_93_ = lean_string_utf8_byte_size(v_pat_83_);
v___x_94_ = lean_nat_dec_eq(v___x_93_, v___x_84_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_95_, 0, v_pat_83_);
lean_ctor_set(v___x_95_, 1, v___x_84_);
lean_ctor_set(v___x_95_, 2, v___x_93_);
v___x_96_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_95_);
v___x_97_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
lean_ctor_set(v___x_97_, 2, v___x_84_);
lean_ctor_set(v___x_97_, 3, v___x_84_);
v___y_88_ = v___x_97_;
goto v___jp_87_;
}
else
{
lean_object* v___x_98_; 
lean_dec_ref(v_pat_83_);
v___x_98_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___closed__0));
v___y_88_ = v___x_98_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(0);
v___x_90_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_82_, v___x_86_, v___x_85_, v___y_88_, v___x_89_);
lean_dec_ref_known(v___x_86_, 3);
lean_dec_ref(v_s_82_);
if (lean_obj_tag(v___x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = 1;
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___boxed(lean_object* v_s_99_, lean_object* v_pat_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v_s_99_, v_pat_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0(lean_object* v_s_103_, lean_object* v___x_104_, lean_object* v___x_105_, lean_object* v_inst_106_, lean_object* v_R_107_, lean_object* v_a_108_, lean_object* v_b_109_, lean_object* v_c_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_103_, v___x_104_, v___x_105_, v_a_108_, v_b_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___boxed(lean_object* v_s_112_, lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v_inst_115_, lean_object* v_R_116_, lean_object* v_a_117_, lean_object* v_b_118_, lean_object* v_c_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0(v_s_112_, v___x_113_, v___x_114_, v_inst_115_, v_R_116_, v_a_117_, v_b_118_, v_c_119_);
lean_dec(v_b_118_);
lean_dec(v___x_114_);
lean_dec_ref(v___x_113_);
lean_dec_ref(v_s_112_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
if (lean_obj_tag(v_x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 1;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
else
{
if (lean_obj_tag(v_x_122_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
else
{
lean_object* v_val_126_; lean_object* v_val_127_; uint8_t v___x_128_; 
v_val_126_ = lean_ctor_get(v_x_121_, 0);
v_val_127_ = lean_ctor_get(v_x_122_, 0);
v___x_128_ = lean_name_eq(v_val_126_, v_val_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v_x_129_, v_x_130_);
lean_dec(v_x_130_);
lean_dec(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg(lean_object* v_cls_133_, lean_object* v_t_134_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_134_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_cls_133_);
v___x_138_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v___x_136_, v___x_137_);
lean_dec_ref_known(v___x_137_, 1);
lean_dec(v___x_136_);
v___x_139_ = lean_box(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg___boxed(lean_object* v_cls_141_, lean_object* v_t_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_141_, v_t_142_);
lean_dec_ref(v_t_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass(lean_object* v_cls_145_, lean_object* v_t_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_145_, v_t_146_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___boxed(lean_object* v_cls_151_, lean_object* v_t_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_PostprocessTraces_ofClass(v_cls_151_, v_t_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec_ref(v_t_152_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg(lean_object* v_pat_157_, lean_object* v_t_158_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_158_);
if (lean_obj_tag(v___x_165_) == 0)
{
goto v___jp_160_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_177_; 
v_val_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_177_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
uint8_t v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = 1;
v___x_171_ = l_Lean_Name_toString(v_val_166_, v___x_170_);
lean_inc_ref(v_pat_157_);
v___x_172_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v___x_171_, v_pat_157_);
if (v___x_172_ == 0)
{
lean_del_object(v___x_168_);
goto v___jp_160_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_175_; 
lean_dec_ref(v_t_158_);
lean_dec_ref(v_pat_157_);
v___x_173_ = lean_box(v___x_172_);
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 0);
lean_ctor_set(v___x_168_, 0, v___x_173_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
v___jp_160_:
{
lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = l_Lean_PostprocessTraces_TraceTree_headText(v_t_158_);
v___x_162_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v___x_161_, v_pat_157_);
v___x_163_ = lean_box(v___x_162_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg___boxed(lean_object* v_pat_178_, lean_object* v_t_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_178_, v_t_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString(lean_object* v_pat_182_, lean_object* v_t_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_182_, v_t_183_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___boxed(lean_object* v_pat_188_, lean_object* v_t_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_PostprocessTraces_containsString(v_pat_188_, v_t_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_193_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
if (lean_obj_tag(v_x_195_) == 0)
{
uint8_t v___x_196_; 
v___x_196_ = 1;
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
}
else
{
if (lean_obj_tag(v_x_195_) == 0)
{
uint8_t v___x_198_; 
v___x_198_ = 0;
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v_val_200_; uint8_t v___x_201_; uint8_t v___x_202_; uint8_t v___x_203_; 
v_val_199_ = lean_ctor_get(v_x_194_, 0);
v_val_200_ = lean_ctor_get(v_x_195_, 0);
v___x_201_ = lean_unbox(v_val_199_);
v___x_202_ = lean_unbox(v_val_200_);
v___x_203_ = l_Lean_instBEqTraceResult_beq(v___x_201_, v___x_202_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0___boxed(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v_x_204_, v_x_205_);
lean_dec(v_x_205_);
lean_dec(v_x_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg(lean_object* v_t_211_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_213_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_211_);
v___x_214_ = ((lean_object*)(l_Lean_PostprocessTraces_succeeded___redArg___closed__0));
v___x_215_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_213_, v___x_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg___boxed(lean_object* v_t_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_218_);
lean_dec_ref(v_t_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded(lean_object* v_t_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_221_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___boxed(lean_object* v_t_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_PostprocessTraces_succeeded(v_t_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec_ref(v_t_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg(lean_object* v_t_234_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_236_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_234_);
v___x_237_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_238_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg___boxed(lean_object* v_t_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_PostprocessTraces_failed___redArg(v_t_241_);
lean_dec_ref(v_t_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed(lean_object* v_t_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_PostprocessTraces_failed___redArg(v_t_244_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___boxed(lean_object* v_t_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_PostprocessTraces_failed(v_t_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_t_249_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg(lean_object* v_t_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_259_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_257_);
v___x_260_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_261_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_259_, v___x_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg___boxed(lean_object* v_t_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_PostprocessTraces_errored___redArg(v_t_264_);
lean_dec_ref(v_t_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored(lean_object* v_t_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_PostprocessTraces_errored___redArg(v_t_267_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___boxed(lean_object* v_t_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_PostprocessTraces_errored(v_t_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec_ref(v_t_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg(lean_object* v_t_277_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_277_);
v___x_280_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_281_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_283_ = l_Option_instBEq_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_279_, v___x_282_);
lean_dec(v___x_279_);
v___x_284_ = lean_box(v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v___x_279_);
v___x_286_ = lean_box(v___x_281_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg___boxed(lean_object* v_t_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_288_);
lean_dec_ref(v_t_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful(lean_object* v_t_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_291_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___boxed(lean_object* v_t_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_PostprocessTraces_unsuccessful(v_t_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec_ref(v_t_296_);
return v_res_300_;
}
}
static double _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0(void){
_start:
{
lean_object* v___x_301_; double v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1000u);
v___x_302_ = lean_float_of_nat(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg(double v_ms_303_, lean_object* v_t_304_){
_start:
{
double v___x_306_; double v___x_307_; double v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_304_);
v___x_307_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_308_ = lean_float_mul(v___x_306_, v___x_307_);
v___x_309_ = lean_float_decLe(v_ms_303_, v___x_308_);
v___x_310_ = lean_box(v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg___boxed(lean_object* v_ms_312_, lean_object* v_t_313_, lean_object* v_a_314_){
_start:
{
double v_ms_boxed_315_; lean_object* v_res_316_; 
v_ms_boxed_315_ = lean_unbox_float(v_ms_312_);
lean_dec_ref(v_ms_312_);
v_res_316_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_boxed_315_, v_t_313_);
lean_dec_ref(v_t_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs(double v_ms_317_, lean_object* v_t_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_317_, v_t_318_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___boxed(lean_object* v_ms_323_, lean_object* v_t_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
double v_ms_boxed_328_; lean_object* v_res_329_; 
v_ms_boxed_328_ = lean_unbox_float(v_ms_323_);
lean_dec_ref(v_ms_323_);
v_res_329_ = l_Lean_PostprocessTraces_minTimeMs(v_ms_boxed_328_, v_t_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec_ref(v_t_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg(double v_ms_330_, lean_object* v_t_331_){
_start:
{
double v___x_333_; double v___x_334_; double v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_333_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_331_);
v___x_334_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_335_ = lean_float_mul(v___x_333_, v___x_334_);
v___x_336_ = lean_float_decLe(v_ms_330_, v___x_335_);
v___x_337_ = lean_box(v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg___boxed(lean_object* v_ms_339_, lean_object* v_t_340_, lean_object* v_a_341_){
_start:
{
double v_ms_boxed_342_; lean_object* v_res_343_; 
v_ms_boxed_342_ = lean_unbox_float(v_ms_339_);
lean_dec_ref(v_ms_339_);
v_res_343_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_boxed_342_, v_t_340_);
lean_dec_ref(v_t_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs(double v_ms_344_, lean_object* v_t_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_344_, v_t_345_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___boxed(lean_object* v_ms_350_, lean_object* v_t_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
double v_ms_boxed_355_; lean_object* v_res_356_; 
v_ms_boxed_355_ = lean_unbox_float(v_ms_350_);
lean_dec_ref(v_ms_350_);
v_res_356_ = l_Lean_PostprocessTraces_minSelfTimeMs(v_ms_boxed_355_, v_t_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec_ref(v_t_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(lean_object* v_p_357_, lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
lean_inc(v___x_366_);
lean_inc_ref(v_p_357_);
v___x_367_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_357_, v___x_366_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v_a_370_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
if (lean_obj_tag(v_a_368_) == 0)
{
v_a_370_ = v_b_361_;
goto v___jp_369_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_375_; 
v_val_374_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v_a_368_, 1);
v___x_375_ = lean_array_push(v_b_361_, v_val_374_);
v_a_370_ = v___x_375_;
goto v___jp_369_;
}
v___jp_369_:
{
size_t v___x_371_; size_t v___x_372_; 
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_359_, v___x_371_);
v_i_359_ = v___x_372_;
v_b_361_ = v_a_370_;
goto _start;
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v_b_361_);
lean_dec_ref(v_p_357_);
v_a_376_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_367_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_367_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v___x_384_; 
lean_dec_ref(v_p_357_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_b_361_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_385_, lean_object* v_as_386_, lean_object* v_i_387_, lean_object* v_stop_388_, lean_object* v_b_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
size_t v_i_boxed_393_; size_t v_stop_boxed_394_; lean_object* v_res_395_; 
v_i_boxed_393_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_stop_boxed_394_ = lean_unbox_usize(v_stop_388_);
lean_dec(v_stop_388_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_385_, v_as_386_, v_i_boxed_393_, v_stop_boxed_394_, v_b_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec_ref(v_as_386_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(lean_object* v_p_398_, lean_object* v_as_399_, lean_object* v_start_400_, lean_object* v_stop_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0));
v___x_406_ = lean_nat_dec_lt(v_start_400_, v_stop_401_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
lean_dec_ref(v_p_398_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_array_get_size(v_as_399_);
v___x_409_ = lean_nat_dec_le(v_stop_401_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_lt(v_start_400_, v___x_408_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_p_398_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_405_);
return v___x_411_;
}
else
{
size_t v___x_412_; size_t v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_usize_of_nat(v_start_400_);
v___x_413_ = lean_usize_of_nat(v___x_408_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_398_, v_as_399_, v___x_412_, v___x_413_, v___x_405_, v___y_402_, v___y_403_);
return v___x_414_;
}
}
else
{
size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_usize_of_nat(v_start_400_);
v___x_416_ = lean_usize_of_nat(v_stop_401_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_398_, v_as_399_, v___x_415_, v___x_416_, v___x_405_, v___y_402_, v___y_403_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___boxed(lean_object* v_p_418_, lean_object* v_as_419_, lean_object* v_start_420_, lean_object* v_stop_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_418_, v_as_419_, v_start_420_, v_stop_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_stop_421_);
lean_dec(v_start_420_);
lean_dec_ref(v_as_419_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees(lean_object* v_p_426_, lean_object* v_roots_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_array_get_size(v_roots_427_);
v___x_433_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_426_, v_roots_427_, v___x_431_, v___x_432_, v_a_428_, v_a_429_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees___boxed(lean_object* v_p_434_, lean_object* v_roots_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_PostprocessTraces_filterSubtrees(v_p_434_, v_roots_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec_ref(v_roots_435_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(lean_object* v_p_440_, lean_object* v_as_441_, size_t v_i_442_, size_t v_stop_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = lean_usize_dec_eq(v_i_442_, v_stop_443_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_array_uget_borrowed(v_as_441_, v_i_442_);
lean_inc(v___x_449_);
lean_inc_ref(v_p_440_);
v___x_450_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_440_, v___x_449_, v_b_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; size_t v___x_452_; size_t v___x_453_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_442_, v___x_452_);
v_i_442_ = v___x_453_;
v_b_444_ = v_a_451_;
goto _start;
}
else
{
lean_dec_ref(v_p_440_);
return v___x_450_;
}
}
else
{
lean_object* v___x_455_; 
lean_dec_ref(v_p_440_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v_b_444_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0___boxed(lean_object* v_p_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_stop_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
size_t v_i_boxed_464_; size_t v_stop_boxed_465_; lean_object* v_res_466_; 
v_i_boxed_464_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_stop_boxed_465_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_456_, v_as_457_, v_i_boxed_464_, v_stop_boxed_465_, v_b_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec_ref(v_as_457_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist(lean_object* v_p_467_, lean_object* v_roots_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0));
v___x_474_ = lean_array_get_size(v_roots_468_);
v___x_475_ = lean_nat_dec_lt(v___x_472_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec_ref(v_p_467_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_473_);
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_le(v___x_474_, v___x_474_);
if (v___x_477_ == 0)
{
if (v___x_475_ == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v_p_467_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_473_);
return v___x_478_;
}
else
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___x_474_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_467_, v_roots_468_, v___x_479_, v___x_480_, v___x_473_, v_a_469_, v_a_470_);
return v___x_481_;
}
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_474_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_467_, v_roots_468_, v___x_482_, v___x_483_, v___x_473_, v_a_469_, v_a_470_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist___boxed(lean_object* v_p_485_, lean_object* v_roots_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_PostprocessTraces_hoist(v_p_485_, v_roots_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec_ref(v_roots_486_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(uint8_t v_a_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_cls_493_; lean_object* v_result_x3f_494_; double v_startTime_495_; double v_stopTime_496_; lean_object* v_tag_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_cls_493_ = lean_ctor_get(v_x_492_, 0);
v_result_x3f_494_ = lean_ctor_get(v_x_492_, 1);
v_startTime_495_ = lean_ctor_get_float(v_x_492_, sizeof(void*)*3);
v_stopTime_496_ = lean_ctor_get_float(v_x_492_, sizeof(void*)*3 + 8);
v_tag_497_ = lean_ctor_get(v_x_492_, 2);
v_isSharedCheck_504_ = !lean_is_exclusive(v_x_492_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v_x_492_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_tag_497_);
lean_inc(v_result_x3f_494_);
lean_inc(v_cls_493_);
lean_dec(v_x_492_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_cls_493_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_result_x3f_494_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_tag_497_);
lean_ctor_set_float(v_reuseFailAlloc_503_, sizeof(void*)*3, v_startTime_495_);
lean_ctor_set_float(v_reuseFailAlloc_503_, sizeof(void*)*3 + 8, v_stopTime_496_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3 + 16, v_a_491_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed(lean_object* v_a_505_, lean_object* v_x_506_){
_start:
{
uint8_t v_a_1094__boxed_507_; lean_object* v_res_508_; 
v_a_1094__boxed_507_ = lean_unbox(v_a_505_);
v_res_508_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(v_a_1094__boxed_507_, v_x_506_);
return v_res_508_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(lean_object* v_as_509_, size_t v_i_510_, size_t v_stop_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_eq(v_i_510_, v_stop_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v_snd_514_; uint8_t v___x_515_; 
v___x_513_ = lean_array_uget_borrowed(v_as_509_, v_i_510_);
v_snd_514_ = lean_ctor_get(v___x_513_, 1);
v___x_515_ = lean_unbox(v_snd_514_);
if (v___x_515_ == 0)
{
size_t v___x_516_; size_t v___x_517_; 
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_510_, v___x_516_);
v_i_510_ = v___x_517_;
goto _start;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = 1;
return v___x_519_;
}
}
else
{
uint8_t v___x_520_; 
v___x_520_ = 0;
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2___boxed(lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_){
_start:
{
size_t v_i_boxed_524_; size_t v_stop_boxed_525_; uint8_t v_res_526_; lean_object* v_r_527_; 
v_i_boxed_524_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_525_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_as_521_, v_i_boxed_524_, v_stop_boxed_525_);
lean_dec_ref(v_as_521_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(size_t v_sz_528_, size_t v_i_529_, lean_object* v_bs_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_lt(v_i_529_, v_sz_528_);
if (v___x_531_ == 0)
{
return v_bs_530_;
}
else
{
lean_object* v_v_532_; lean_object* v_fst_533_; lean_object* v___x_534_; lean_object* v_bs_x27_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; 
v_v_532_ = lean_array_uget_borrowed(v_bs_530_, v_i_529_);
v_fst_533_ = lean_ctor_get(v_v_532_, 0);
lean_inc(v_fst_533_);
v___x_534_ = lean_unsigned_to_nat(0u);
v_bs_x27_535_ = lean_array_uset(v_bs_530_, v_i_529_, v___x_534_);
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_add(v_i_529_, v___x_536_);
v___x_538_ = lean_array_uset(v_bs_x27_535_, v_i_529_, v_fst_533_);
v_i_529_ = v___x_537_;
v_bs_530_ = v___x_538_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1___boxed(lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_bs_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_544_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_boxed_543_, v_i_boxed_544_, v_bs_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(lean_object* v_p_546_, lean_object* v_t_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; 
lean_inc_ref(v_p_546_);
lean_inc(v_a_549_);
lean_inc_ref(v_a_548_);
lean_inc_ref(v_t_547_);
v___x_551_ = lean_apply_4(v_p_546_, v_t_547_, v_a_548_, v_a_549_, lean_box(0));
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_600_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_600_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_600_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_600_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint8_t v___x_556_; 
v___x_556_ = lean_unbox(v_a_552_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; size_t v_sz_558_; size_t v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_554_);
v___x_557_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_547_);
v_sz_558_ = lean_array_size(v___x_557_);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_546_, v_sz_558_, v___x_559_, v___x_557_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_587_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_587_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_587_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_587_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint8_t v___y_566_; lean_object* v___y_567_; lean_object* v___f_573_; uint8_t v___y_575_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
lean_inc(v_a_552_);
v___f_573_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed), 2, 1);
lean_closure_set(v___f_573_, 0, v_a_552_);
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_array_get_size(v_a_561_);
v___x_582_ = lean_nat_dec_lt(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; 
v___x_583_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
else
{
if (v___x_582_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
v___y_575_ = v___x_584_;
goto v___jp_574_;
}
else
{
size_t v___x_585_; uint8_t v___x_586_; 
lean_dec(v_a_552_);
v___x_585_ = lean_usize_of_nat(v___x_581_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_a_561_, v___x_559_, v___x_585_);
v___y_575_ = v___x_586_;
goto v___jp_574_;
}
}
v___jp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_568_ = lean_box(v___y_566_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___y_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_569_);
v___x_571_ = v___x_563_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
v___jp_574_:
{
size_t v_sz_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_sz_576_ = lean_array_size(v_a_561_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_576_, v___x_559_, v_a_561_);
v___x_578_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_547_, v___x_577_);
if (v___y_575_ == 0)
{
lean_dec_ref(v___f_573_);
v___y_566_ = v___y_575_;
v___y_567_ = v___x_578_;
goto v___jp_565_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_PostprocessTraces_TraceTree_modifyData(v___x_578_, v___f_573_);
v___y_566_ = v___y_575_;
v___y_567_ = v___x_579_;
goto v___jp_565_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_a_552_);
lean_dec_ref(v_t_547_);
v_a_588_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_560_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_560_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec_ref(v_p_546_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_t_547_);
lean_ctor_set(v___x_596_, 1, v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_596_);
v___x_598_ = v___x_554_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_t_547_);
lean_dec_ref(v_p_546_);
v_a_601_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_551_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_551_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(lean_object* v_p_609_, size_t v_sz_610_, size_t v_i_611_, lean_object* v_bs_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_611_, v_sz_610_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v_p_609_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_bs_612_);
return v___x_617_;
}
else
{
lean_object* v_v_618_; lean_object* v___x_619_; 
v_v_618_ = lean_array_uget_borrowed(v_bs_612_, v_i_611_);
lean_inc(v_v_618_);
lean_inc_ref(v_p_609_);
v___x_619_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_609_, v_v_618_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v_bs_x27_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = lean_unsigned_to_nat(0u);
v_bs_x27_622_ = lean_array_uset(v_bs_612_, v_i_611_, v___x_621_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_611_, v___x_623_);
v___x_625_ = lean_array_uset(v_bs_x27_622_, v_i_611_, v_a_620_);
v_i_611_ = v___x_624_;
v_bs_612_ = v___x_625_;
goto _start;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_bs_612_);
lean_dec_ref(v_p_609_);
v_a_627_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_619_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_619_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0___boxed(lean_object* v_p_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_bs_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_643_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_635_, v_sz_boxed_642_, v_i_boxed_643_, v_bs_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___boxed(lean_object* v_p_645_, lean_object* v_t_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_645_, v_t_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(lean_object* v_p_651_, size_t v_sz_652_, size_t v_i_653_, lean_object* v_bs_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = lean_usize_dec_lt(v_i_653_, v_sz_652_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec_ref(v_p_651_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_bs_654_);
return v___x_659_;
}
else
{
lean_object* v_v_660_; lean_object* v___x_661_; 
v_v_660_ = lean_array_uget_borrowed(v_bs_654_, v_i_653_);
lean_inc(v_v_660_);
lean_inc_ref(v_p_651_);
v___x_661_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_651_, v_v_660_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_fst_663_; lean_object* v___x_664_; lean_object* v_bs_x27_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v_fst_663_ = lean_ctor_get(v_a_662_, 0);
lean_inc(v_fst_663_);
lean_dec(v_a_662_);
v___x_664_ = lean_unsigned_to_nat(0u);
v_bs_x27_665_ = lean_array_uset(v_bs_654_, v_i_653_, v___x_664_);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_add(v_i_653_, v___x_666_);
v___x_668_ = lean_array_uset(v_bs_x27_665_, v_i_653_, v_fst_663_);
v_i_653_ = v___x_667_;
v_bs_654_ = v___x_668_;
goto _start;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_bs_654_);
lean_dec_ref(v_p_651_);
v_a_670_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_661_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_661_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0___boxed(lean_object* v_p_678_, lean_object* v_sz_679_, lean_object* v_i_680_, lean_object* v_bs_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_679_);
lean_dec(v_sz_679_);
v_i_boxed_686_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_678_, v_sz_boxed_685_, v_i_boxed_686_, v_bs_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees(lean_object* v_p_688_, lean_object* v_roots_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
size_t v_sz_693_; size_t v___x_694_; lean_object* v___x_695_; 
v_sz_693_ = lean_array_size(v_roots_689_);
v___x_694_ = ((size_t)0ULL);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_688_, v_sz_693_, v___x_694_, v_roots_689_, v_a_690_, v_a_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees___boxed(lean_object* v_p_696_, lean_object* v_roots_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_PostprocessTraces_exposeSubtrees(v_p_696_, v_roots_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(lean_object* v_as_702_, size_t v_i_703_, size_t v_stop_704_, lean_object* v_b_705_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_eq(v_i_703_, v_stop_704_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v_snd_708_; lean_object* v___x_709_; size_t v___x_710_; size_t v___x_711_; 
v___x_707_ = lean_array_uget_borrowed(v_as_702_, v_i_703_);
v_snd_708_ = lean_ctor_get(v___x_707_, 1);
v___x_709_ = lean_nat_add(v_b_705_, v_snd_708_);
lean_dec(v_b_705_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_add(v_i_703_, v___x_710_);
v_i_703_ = v___x_711_;
v_b_705_ = v___x_709_;
goto _start;
}
else
{
return v_b_705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2___boxed(lean_object* v_as_713_, lean_object* v_i_714_, lean_object* v_stop_715_, lean_object* v_b_716_){
_start:
{
size_t v_i_boxed_717_; size_t v_stop_boxed_718_; lean_object* v_res_719_; 
v_i_boxed_717_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_stop_boxed_718_ = lean_unbox_usize(v_stop_715_);
lean_dec(v_stop_715_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_as_713_, v_i_boxed_717_, v_stop_boxed_718_, v_b_716_);
lean_dec_ref(v_as_713_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(size_t v_sz_720_, size_t v_i_721_, lean_object* v_bs_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_usize_dec_lt(v_i_721_, v_sz_720_);
if (v___x_723_ == 0)
{
return v_bs_722_;
}
else
{
lean_object* v_v_724_; lean_object* v_fst_725_; lean_object* v___x_726_; lean_object* v_bs_x27_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v_v_724_ = lean_array_uget_borrowed(v_bs_722_, v_i_721_);
v_fst_725_ = lean_ctor_get(v_v_724_, 0);
lean_inc(v_fst_725_);
v___x_726_ = lean_unsigned_to_nat(0u);
v_bs_x27_727_ = lean_array_uset(v_bs_722_, v_i_721_, v___x_726_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_721_, v___x_728_);
v___x_730_ = lean_array_uset(v_bs_x27_727_, v_i_721_, v_fst_725_);
v_i_721_ = v___x_729_;
v_bs_722_ = v___x_730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1___boxed(lean_object* v_sz_732_, lean_object* v_i_733_, lean_object* v_bs_734_){
_start:
{
size_t v_sz_boxed_735_; size_t v_i_boxed_736_; lean_object* v_res_737_; 
v_sz_boxed_735_ = lean_unbox_usize(v_sz_732_);
lean_dec(v_sz_732_);
v_i_boxed_736_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_boxed_735_, v_i_boxed_736_, v_bs_734_);
return v_res_737_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__0));
v___x_740_ = l_Lean_stringToMessageData(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__2));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__4));
v___x_746_ = l_Lean_stringToMessageData(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(lean_object* v_a_749_){
_start:
{
if (lean_obj_tag(v_a_749_) == 0)
{
lean_object* v_data_750_; lean_object* v_msg_751_; lean_object* v_children_752_; lean_object* v_wrap_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_795_; 
v_data_750_ = lean_ctor_get(v_a_749_, 0);
v_msg_751_ = lean_ctor_get(v_a_749_, 1);
v_children_752_ = lean_ctor_get(v_a_749_, 2);
v_wrap_753_ = lean_ctor_get(v_a_749_, 3);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_749_);
if (v_isSharedCheck_795_ == 0)
{
v___x_755_ = v_a_749_;
v_isShared_756_ = v_isSharedCheck_795_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_wrap_753_);
lean_inc(v_children_752_);
lean_inc(v_msg_751_);
lean_inc(v_data_750_);
lean_dec(v_a_749_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_795_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
size_t v_sz_757_; size_t v___x_758_; lean_object* v_results_759_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___x_781_; lean_object* v___y_783_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_sz_757_ = lean_array_size(v_children_752_);
v___x_758_ = ((size_t)0ULL);
v_results_759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_757_, v___x_758_, v_children_752_);
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_array_get_size(v_results_759_);
v___x_789_ = lean_nat_dec_lt(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
v___y_783_ = v___x_781_;
goto v___jp_782_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_le(v___x_788_, v___x_788_);
if (v___x_790_ == 0)
{
if (v___x_789_ == 0)
{
v___y_783_ = v___x_781_;
goto v___jp_782_;
}
else
{
size_t v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_usize_of_nat(v___x_788_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_results_759_, v___x_758_, v___x_791_, v___x_781_);
v___y_783_ = v___x_792_;
goto v___jp_782_;
}
}
else
{
size_t v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_usize_of_nat(v___x_788_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_results_759_, v___x_758_, v___x_793_, v___x_781_);
v___y_783_ = v___x_794_;
goto v___jp_782_;
}
}
v___jp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; size_t v_sz_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_763_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v_msg_751_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
lean_inc(v___y_761_);
v___x_765_ = l_Nat_reprFast(v___y_761_);
v___x_766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___x_767_ = l_Lean_MessageData_ofFormat(v___x_766_);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_764_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_inc_ref(v___y_762_);
v___x_771_ = l_Lean_stringToMessageData(v___y_762_);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v_sz_775_ = lean_array_size(v_results_759_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_775_, v___x_758_, v_results_759_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 2, v___x_776_);
lean_ctor_set(v___x_755_, 1, v___x_774_);
v___x_778_ = v___x_755_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_data_750_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_wrap_753_);
v___x_778_ = v_reuseFailAlloc_780_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___y_761_);
return v___x_779_;
}
}
v___jp_782_:
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_eq(v___y_783_, v___x_781_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
v___x_785_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__6));
v___y_761_ = v___y_783_;
v___y_762_ = v___x_785_;
goto v___jp_760_;
}
else
{
lean_object* v___x_786_; 
v___x_786_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__7));
v___y_761_ = v___y_783_;
v___y_762_ = v___x_786_;
goto v___jp_760_;
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_a_749_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(size_t v_sz_798_, size_t v_i_799_, lean_object* v_bs_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_801_ == 0)
{
return v_bs_800_;
}
else
{
lean_object* v_v_802_; lean_object* v___x_803_; lean_object* v_bs_x27_804_; lean_object* v___x_805_; size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_v_802_ = lean_array_uget(v_bs_800_, v_i_799_);
v___x_803_ = lean_unsigned_to_nat(0u);
v_bs_x27_804_ = lean_array_uset(v_bs_800_, v_i_799_, v___x_803_);
v___x_805_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(v_v_802_);
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_799_, v___x_806_);
v___x_808_ = lean_array_uset(v_bs_x27_804_, v_i_799_, v___x_805_);
v_i_799_ = v___x_807_;
v_bs_800_ = v___x_808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0___boxed(lean_object* v_sz_810_, lean_object* v_i_811_, lean_object* v_bs_812_){
_start:
{
size_t v_sz_boxed_813_; size_t v_i_boxed_814_; lean_object* v_res_815_; 
v_sz_boxed_813_ = lean_unbox_usize(v_sz_810_);
lean_dec(v_sz_810_);
v_i_boxed_814_ = lean_unbox_usize(v_i_811_);
lean_dec(v_i_811_);
v_res_815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_boxed_813_, v_i_boxed_814_, v_bs_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(size_t v_sz_816_, size_t v_i_817_, lean_object* v_bs_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_lt(v_i_817_, v_sz_816_);
if (v___x_819_ == 0)
{
return v_bs_818_;
}
else
{
lean_object* v_v_820_; lean_object* v___x_821_; lean_object* v_fst_822_; lean_object* v___x_823_; lean_object* v_bs_x27_824_; size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
v_v_820_ = lean_array_uget_borrowed(v_bs_818_, v_i_817_);
lean_inc(v_v_820_);
v___x_821_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(v_v_820_);
v_fst_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_fst_822_);
lean_dec_ref(v___x_821_);
v___x_823_ = lean_unsigned_to_nat(0u);
v_bs_x27_824_ = lean_array_uset(v_bs_818_, v_i_817_, v___x_823_);
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_add(v_i_817_, v___x_825_);
v___x_827_ = lean_array_uset(v_bs_x27_824_, v_i_817_, v_fst_822_);
v_i_817_ = v___x_826_;
v_bs_818_ = v___x_827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0___boxed(lean_object* v_sz_829_, lean_object* v_i_830_, lean_object* v_bs_831_){
_start:
{
size_t v_sz_boxed_832_; size_t v_i_boxed_833_; lean_object* v_res_834_; 
v_sz_boxed_832_ = lean_unbox_usize(v_sz_829_);
lean_dec(v_sz_829_);
v_i_boxed_833_ = lean_unbox_usize(v_i_830_);
lean_dec(v_i_830_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_boxed_832_, v_i_boxed_833_, v_bs_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg(lean_object* v_roots_835_){
_start:
{
size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_sz_837_ = lean_array_size(v_roots_835_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_837_, v___x_838_, v_roots_835_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg___boxed(lean_object* v_roots_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes(lean_object* v_roots_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_844_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___boxed(lean_object* v_roots_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_PostprocessTraces_countNodes(v_roots_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_853_;
}
}
static double _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0(void){
_start:
{
lean_object* v___x_854_; double v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(10u);
v___x_855_ = lean_float_of_nat(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(double v_ms_858_){
_start:
{
lean_object* v___x_859_; double v___x_860_; double v___x_861_; double v___x_862_; uint64_t v___x_863_; lean_object* v_tenths_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_859_ = lean_unsigned_to_nat(10u);
v___x_860_ = lean_float_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0);
v___x_861_ = lean_float_mul(v_ms_858_, v___x_860_);
v___x_862_ = round(v___x_861_);
v___x_863_ = lean_float_to_uint64(v___x_862_);
v_tenths_864_ = lean_uint64_to_nat(v___x_863_);
v___x_865_ = lean_nat_div(v_tenths_864_, v___x_859_);
v___x_866_ = l_Nat_reprFast(v___x_865_);
v___x_867_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__1));
v___x_868_ = lean_string_append(v___x_866_, v___x_867_);
v___x_869_ = lean_nat_mod(v_tenths_864_, v___x_859_);
lean_dec(v_tenths_864_);
v___x_870_ = l_Nat_reprFast(v___x_869_);
v___x_871_ = lean_string_append(v___x_868_, v___x_870_);
lean_dec_ref(v___x_870_);
v___x_872_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__2));
v___x_873_ = lean_string_append(v___x_871_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___boxed(lean_object* v_ms_874_){
_start:
{
double v_ms_boxed_875_; lean_object* v_res_876_; 
v_ms_boxed_875_ = lean_unbox_float(v_ms_874_);
lean_dec_ref(v_ms_874_);
v_res_876_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(v_ms_boxed_875_);
return v_res_876_;
}
}
static double _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0(void){
_start:
{
lean_object* v___x_877_; double v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_float_of_nat(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__1));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go(lean_object* v_a_882_){
_start:
{
if (lean_obj_tag(v_a_882_) == 0)
{
lean_object* v_data_883_; lean_object* v_msg_884_; lean_object* v_children_885_; lean_object* v_wrap_886_; lean_object* v___y_888_; double v_startTime_893_; double v___x_894_; uint8_t v___x_895_; 
v_data_883_ = lean_ctor_get(v_a_882_, 0);
lean_inc_ref(v_data_883_);
v_msg_884_ = lean_ctor_get(v_a_882_, 1);
v_children_885_ = lean_ctor_get(v_a_882_, 2);
lean_inc_ref(v_children_885_);
v_wrap_886_ = lean_ctor_get(v_a_882_, 3);
lean_inc_ref(v_wrap_886_);
v_startTime_893_ = lean_ctor_get_float(v_data_883_, sizeof(void*)*3);
v___x_894_ = lean_float_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0);
v___x_895_ = lean_float_beq(v_startTime_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; double v___x_898_; double v___x_899_; double v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_896_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2);
lean_inc_ref(v_msg_884_);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v_msg_884_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_a_882_);
lean_dec_ref_known(v_a_882_, 4);
v___x_899_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_900_ = lean_float_mul(v___x_898_, v___x_899_);
v___x_901_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(v___x_900_);
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_897_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___y_888_ = v___x_905_;
goto v___jp_887_;
}
else
{
lean_inc_ref(v_msg_884_);
lean_dec_ref_known(v_a_882_, 4);
v___y_888_ = v_msg_884_;
goto v___jp_887_;
}
v___jp_887_:
{
size_t v_sz_889_; size_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_sz_889_ = lean_array_size(v_children_885_);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_889_, v___x_890_, v_children_885_);
v___x_892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_892_, 0, v_data_883_);
lean_ctor_set(v___x_892_, 1, v___y_888_);
lean_ctor_set(v___x_892_, 2, v___x_891_);
lean_ctor_set(v___x_892_, 3, v_wrap_886_);
return v___x_892_;
}
}
else
{
return v_a_882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(size_t v_sz_906_, size_t v_i_907_, lean_object* v_bs_908_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = lean_usize_dec_lt(v_i_907_, v_sz_906_);
if (v___x_909_ == 0)
{
return v_bs_908_;
}
else
{
lean_object* v_v_910_; lean_object* v___x_911_; lean_object* v_bs_x27_912_; lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v_v_910_ = lean_array_uget(v_bs_908_, v_i_907_);
v___x_911_ = lean_unsigned_to_nat(0u);
v_bs_x27_912_ = lean_array_uset(v_bs_908_, v_i_907_, v___x_911_);
v___x_913_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go(v_v_910_);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_add(v_i_907_, v___x_914_);
v___x_916_ = lean_array_uset(v_bs_x27_912_, v_i_907_, v___x_913_);
v_i_907_ = v___x_915_;
v_bs_908_ = v___x_916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0___boxed(lean_object* v_sz_918_, lean_object* v_i_919_, lean_object* v_bs_920_){
_start:
{
size_t v_sz_boxed_921_; size_t v_i_boxed_922_; lean_object* v_res_923_; 
v_sz_boxed_921_ = lean_unbox_usize(v_sz_918_);
lean_dec(v_sz_918_);
v_i_boxed_922_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_res_923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_boxed_921_, v_i_boxed_922_, v_bs_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg(lean_object* v_roots_924_){
_start:
{
size_t v_sz_926_; size_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_sz_926_ = lean_array_size(v_roots_924_);
v___x_927_ = ((size_t)0ULL);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_926_, v___x_927_, v_roots_924_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg___boxed(lean_object* v_roots_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime(lean_object* v_roots_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_933_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___boxed(lean_object* v_roots_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_PostprocessTraces_selfTime(v_roots_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
return v_res_942_;
}
}
lean_object* runtime_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_Postprocessors(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PostprocessTraces_Postprocessors(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PostprocessTraces_Basic(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PostprocessTraces_Postprocessors(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PostprocessTraces_Postprocessors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PostprocessTraces_Postprocessors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PostprocessTraces_Postprocessors(builtin);
}
#ifdef __cplusplus
}
#endif
